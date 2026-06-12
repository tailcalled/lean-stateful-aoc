/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import Mathlib.Order.Basic
import Mathlib.Data.Finmap

/-!
# The monotone-update monad

This is the computational spine of the model (module 1 of the README layout, the
`Computation` module). Realizers are values in the *monotone-update monad* `T`
over a preorder `P` of forcing conditions:

```
T X := (c : P) → Σ c' ≥ c, X
```

From a condition `c` a computation may *extend* the condition to some `c' ≥ c`
(it never backtracks: the order is baked into the return type) and yields an `X`.
Monotonicity — "the generic filter only grows" — therefore holds *by
construction*, not as a side condition to be discharged later.

Here we only build the generic spine: `T` over an arbitrary preorder, its `Monad`
instance, and a `LawfulMonad` proof. The concrete poset of forcing conditions
(the heap of caches), allocation, and the firewall/parametricity lemma are layered
on top in subsequent work; the README's `Forcing`/`Realizes` modules then sheafify
relative to this monad.
-/

namespace LeanStatefulAoc

universe u v

variable {P : Type u} [Preorder P]

/-- One step of a monotone-update computation that starts at condition `c`:
it commits to an extended condition `next ≥ c` and returns a value of type `X`.

The `le` field lives in `Prop`, so two steps are equal as soon as their `next`
and `val` agree — Lean's definitional proof irrelevance discharges the order
witness. This is what makes the monad laws hold *definitionally* below. -/
structure Step (X : Type v) (c : P) where
  /-- the (possibly) extended condition the step commits to -/
  next : P
  /-- monotonicity: the condition only grows -/
  le : c ≤ next
  /-- the returned value -/
  val : X

/-- The monotone-update monad over the preorder `P`. -/
def T (P : Type u) [Preorder P] (X : Type v) : Type (max u v) := (c : P) → Step X c

namespace T

/-- Return: commit to nothing, hand back the value. -/
protected def pure {X : Type v} (x : X) : T P X := fun c => ⟨c, le_refl c, x⟩

/-- Bind: run `m` from `c`, then run `f` from the condition `m` left us in,
composing the two extension witnesses by transitivity. -/
protected def bind {X Y : Type v} (m : T P X) (f : X → T P Y) : T P Y :=
  fun c =>
    let s := m c
    let s' := f s.val s.next
    ⟨s'.next, le_trans s.le s'.le, s'.val⟩

instance : Monad (T P) where
  pure := T.pure
  bind := T.bind

@[simp] theorem pure_eq {X : Type v} (x : X) : (pure x : T P X) = fun c => ⟨c, le_refl c, x⟩ := rfl

@[simp] theorem bind_eq {X Y : Type v} (m : T P X) (f : X → T P Y) :
    m >>= f = T.bind m f := rfl

/-- Left identity. Holds definitionally thanks to proof irrelevance of `le`. -/
@[simp] theorem pure_bind {X Y : Type v} (x : X) (f : X → T P Y) :
    (pure x : T P X) >>= f = f x := rfl

/-- Right identity. -/
@[simp] theorem bind_pure {X : Type v} (m : T P X) : m >>= pure = m := rfl

/-- Associativity. -/
theorem bind_assoc {X Y Z : Type v} (m : T P X) (f : X → T P Y) (g : Y → T P Z) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := rfl

instance : LawfulMonad (T P) := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)

end T

/-!
## The heap of caches and its extension order

A forcing condition is a *finite partial section*: a heap of caches. We flatten the
heap to a single finite map from `(cell, key)` pairs to value-codes. The `cell`
component (a `Loc = ℕ`) is the identity of the cache a single `AC_dec` application
allocated; both the key and the stored value are codes in the untyped realizer
domain `V`. Storing codes (rather than typed elements of `B a`) is what makes
"compatibility = syntactic agreement of stored realizers" literally equality in `V`,
needing no equality on semantic values — exactly the README's firewall stance.

The order is plain extension of partial functions: `h ≤ h'` iff `h'` agrees with `h`
wherever `h` is defined. This is the cleanest possible poset to feed to `T`, and
"the generic only grows" is just monotone insertion. -/

/-- Cell label / cache identity. A fresh `Loc` is handed out per `AC_dec` application. -/
abbrev Loc : Type := ℕ

variable (V : Type u) [DecidableEq V]

/-- A forcing condition: a finite partial section, as a finite map from
`(cell, key)` pairs to value-codes. -/
abbrev Heap : Type u := Finmap (fun _ : Loc × V => V)

namespace Heap

variable {V}

/-- Look up the code stored at `(cell, key)`, if any. -/
def lookup (h : Heap V) (cell : Loc) (key : V) : Option V := Finmap.lookup (cell, key) h

/-- The extension order: `h ≤ h'` when `h'` retains every commitment of `h`. -/
instance : LE (Heap V) where
  le h h' := ∀ p v, Finmap.lookup p h = some v → Finmap.lookup p h' = some v

theorem le_def {h h' : Heap V} :
    h ≤ h' ↔ ∀ p v, Finmap.lookup p h = some v → Finmap.lookup p h' = some v := Iff.rfl

instance : PartialOrder (Heap V) where
  le_refl _ := fun _ _ hv => hv
  le_trans _ _ _ hab hbc := fun p v hv => hbc p v (hab p v hv)
  le_antisymm a b hab hba := by
    apply Finmap.ext_lookup
    intro p
    rcases hl : Finmap.lookup p a with _ | v
    · rcases hr : Finmap.lookup p b with _ | w
      · rfl
      · exact hl.symm.trans (hba p w hr)
    · rw [hab p v hl]

/-- Commit a value at `(cell, key)` (overwriting; callers commit only on a miss). -/
def commit (h : Heap V) (cell : Loc) (key : V) (v : V) : Heap V :=
  Finmap.insert (cell, key) v h

/-- Committing at a previously-undefined slot extends the condition. -/
theorem le_commit_of_lookup_none {h : Heap V} {cell : Loc} {key : V}
    (hmiss : h.lookup cell key = none) (v : V) : h ≤ h.commit cell key v := by
  intro p w hw
  by_cases hp : p = (cell, key)
  · subst hp
    simp only [Heap.lookup] at hmiss
    rw [hmiss] at hw
    exact absurd hw (by simp)
  · simp only [Heap.commit]
    rw [Finmap.lookup_insert_of_ne _ hp]
    exact hw

end Heap

/-!
## Realizers: the free monad over the single cache operation

Realizers are *terms* of a free monad `F` whose only effect is the eq-guarded
lookup-or-commit. This is the rigorous content of the README's "no quote, no
reflection": a realizer literally cannot inspect a condition, because the syntax
offers no constructor that does — so the firewall/value-blindness is a structural
property of `F`, not an unprovable claim about arbitrary Lean functions. The poset
`Heap` is the *interpreter's* state, never exposed to the realizer.

The handler `run` interprets `F` into the monotone-update monad `T (Heap V)`. It is
strict, left-to-right state threading: every operation performs its lookup-or-commit
*now*. The only non-determinism is the value committed on a miss, which is supplied
by an `oracle` (a point of the forcing cover); value-blindness will be the statement
that `run`'s observable result is invariant under the oracle. -/

/-- Free monad over one operation. `op cell key eq cont`: consult cache `cell` for a
key eq-matching `key`; on a hit resume `cont` with the stored code, on a miss commit
and resume `cont` with the committed code. The equality test is a *realizer*
(`V → V → Bool`), never a global `DecidableEq` — so the sheaf layer can later refine
it to condition-local equality classes without retrofitting `F`. -/
inductive F (V : Type u) (X : Type u) where
  /-- a pure result -/
  | ret : X → F V X
  /-- the eq-guarded lookup-or-commit, with a continuation over the resulting code -/
  | op : Loc → V → (V → V → Bool) → (V → F V X) → F V X

namespace F

/-- Monadic bind: graft `f` onto every `ret` leaf. -/
protected def bind {V X Y : Type u} : F V X → (X → F V Y) → F V Y
  | ret x, f => f x
  | op cell key eq k, f => op cell key eq (fun v => (k v).bind f)

instance {V : Type u} : Monad (F V) where
  pure := F.ret
  bind := F.bind

end F

/-!
### The handler `run : F X → T (Heap) X`

At this layer the lookup-or-commit matches keys by *exact code identity*. The eq
realizer carried in `op` is deliberately **not** consumed here: condition-local
equality classes (where eq-equal-but-syntactically-distinct keys must collapse to one
cache entry) are a `Realizes`-layer construction, built in there from the start. So
`run` is the bare computable substrate the sheaf quotient sits on top of. -/

/-- One operation as a monotone-update action: lookup-or-commit at the exact slot,
returning the resulting code. On a miss it commits the oracle's generic value at a
provably-fresh slot, so the condition strictly extends. -/
def stepOp {V : Type u} [DecidableEq V] (oracle : Loc → V → V) (cell : Loc) (key : V) :
    T (Heap V) V := fun h =>
  match hlk : h.lookup cell key with
  | some v => ⟨h, le_refl h, v⟩
  | none => ⟨h.commit cell key (oracle cell key),
             Heap.le_commit_of_lookup_none hlk (oracle cell key),
             oracle cell key⟩

/-- The handler: interpret a realizer into the monotone-update monad over the heap,
relative to an `oracle` supplying the generic value committed at each fresh key. -/
def run {V X : Type u} [DecidableEq V] (oracle : Loc → V → V) : F V X → T (Heap V) X
  | F.ret x => pure x
  | F.op cell key _eq k => stepOp oracle cell key >>= fun r => run oracle (k r)

end LeanStatefulAoc
