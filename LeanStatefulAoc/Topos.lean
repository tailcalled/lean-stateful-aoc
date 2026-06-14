import LeanStatefulAoc.Combinators
import LeanStatefulAoc.CodeEval
import LeanStatefulAoc.Tripos

/-!
# Internal type structure (Layer 3) — evaluation modality, Π, and truncation

Layer 2 built the Heyting algebra of *pure* truth values: realizers transported by
the pure reduction `Reds`, propositions saturated under `Code.Red`. The headline
`AC_dec` realizer is **effectful**: it `alloc`s a memo cell and returns a
memoizing choice function. Its target `‖Π x:A. B x‖` therefore *cannot* be a pure
`RProp`, for a sharp reason:

> `Code.Red` contains `S ⬝ x ⬝ y ⬝ z → x ⬝ z ⬝ (y ⬝ z)`, which **duplicates** `z`.
> If `z` performs an effect (`alloc`/`memo`), a single pure reduction changes how
> many times that effect runs. So a proposition whose realizers *run* (heaps
> matter) is **not** closed under full `Code.Red` expansion — it does not fit the
> `RProp` structure, which demands exactly that closure.

Hence the two layers are bridged, not merged: `RProp` is the pure, `Red`-saturated
tripos; the eval-based notions here (`Evaluates`, `Produces`, and the eval-modal
truncation `Trunc`) are **native `eval` relations**, saturated under weak-head
(`eval`) steps only. Pure `RProp`s still embed (a pure realizer is an `eval`
value), but `Π`/`‖·‖` are built directly on `eval`, where effects live.

This file lays the eval-based foundations:

* `Evaluates h e h' v` — `e`, run from `h`, reaches value `v` leaving `h'`.
* `Produces h e Q` — the **state modality**: `e` runs to a value realizing `Q`.
* `Trunc P` — propositional truncation, *eval-modal* (bare relation): a realizer
  may first perform effects (`h → h'`), and a realizer of `P` need only exist at
  `h'`. This is what lets the effectful `alloc`-then-memoize realizer inhabit
  `‖Π x. B x‖`.
-/

namespace LeanStatefulAoc

open Code

/-- `e`, evaluated from heap `h`, reaches value `v` leaving heap `h'` (for some
fuel). Weak-head: `v` is in head-normal form, its sub-codes possibly unreduced. -/
def Evaluates (h : CHeap) (e : Code) (h' : CHeap) (v : Code) : Prop :=
  ∃ fuel, eval fuel h e = some (h', v)

/-- The **state modality**: `e` run from `h` produces a value realizing `Q`
(at the resulting heap). Effects performed along the way are kept in `h'`. -/
def Produces (h : CHeap) (e : Code) (Q : RProp) : Prop :=
  ∃ h' v, Evaluates h e h' v ∧ Q.rel h' v

/-! ### Basic evaluation lemmas -/

/-- A leaf constant (non-application) is already a value: it evaluates to itself
in one step, leaving the heap unchanged. -/
theorem Evaluates.const {h : CHeap} {c : Code} (hc : ∀ f x, c ≠ f ⬝ x) :
    Evaluates h c h c := by
  refine ⟨1, ?_⟩
  cases c with
  | app f x => exact absurd rfl (hc f x)
  | _ => simp only [eval]

/-- `Produces` is monotone in the target proposition. -/
theorem Produces.mono {h : CHeap} {e : Code} {Q R : RProp}
    (hQR : ∀ h' v, Q.rel h' v → R.rel h' v) (hQ : Produces h e Q) :
    Produces h e R := by
  obtain ⟨h', v, hev, hq⟩ := hQ
  exact ⟨h', v, hev, hQR h' v hq⟩

/-- A value realizing `Q` `Produces` `Q` immediately (no effects). -/
theorem Produces.of_value {h : CHeap} {v : Code} {Q : RProp}
    (hval : ∀ f x, v ≠ f ⬝ x) (hv : Q.rel h v) : Produces h v Q :=
  ⟨h, v, Evaluates.const hval, hv⟩

/-! ### Propositional truncation (eval-modal, bare relation)

`Trunc P h e` holds when `e`, *run from `h`*, terminates — performing effects
`h → h'` — after which a realizer of `P` exists at `h'`. The realizer's return
value is discarded (truncation is proof-irrelevant), but its **effects are kept**:
this is precisely what lets `AC_dec`'s realizer `alloc` a memo cell and then point
at the memoizing choice function living in the new heap `h'`.

It takes a **bare relation** `P : CHeap → Code → Prop` (not an `RProp`): as
explained in the module header, eval-modal propositions are not closed under full
`Code.Red` expansion (effect duplication via `S`), so they do not inhabit the pure
`RProp` structure — and the body `Π x. B x` we will truncate is itself a bare
eval-relation (`RPi` below). Pure `RProp`s are fed in via `P.rel`. -/
def Trunc (P : CHeap → Code → Prop) (h : CHeap) (e : Code) : Prop :=
  ∃ h' v, Evaluates h e h' v ∧ ∃ a, P h' a

/-- Truncation unit: a value realizing `P` realizes `‖P‖` (effect-free). -/
theorem Trunc.intro_value {P : CHeap → Code → Prop} {h : CHeap} {a : Code}
    (hval : ∀ f x, a ≠ f ⬝ x) (ha : P h a) : Trunc P h a :=
  ⟨h, a, Evaluates.const hval, a, ha⟩

/-- Truncation is monotone in the proposition (at a fixed heap, pointwise). -/
theorem Trunc.mono {P Q : CHeap → Code → Prop} {h : CHeap} {e : Code}
    (hPQ : ∀ h' a, P h' a → Q h' a) (hP : Trunc P h e) : Trunc Q h e := by
  obtain ⟨h', v, hev, a, ha⟩ := hP
  exact ⟨h', v, hev, a, hPQ h' a ha⟩

/-! ### Projective base type and the dependent function space `Π`

For the first (projective) target, a base type `A` is a `Type` together with a
realizability relation `KeyRel kx x` ("code `kx` realizes the element `x`"), with
**enough realizers** (every element has at least one). The dependent function
space is eval-native: `e` realizes `Π x:A. B x` when applying `e` to *any*
realizer of *any* element `x` **produces** a realizer of `B x`. -/

/-- A projective base type: elements realized by codes, every element realized. -/
structure Base where
  /-- the underlying set of elements -/
  carrier : Type
  /-- `KeyRel kx x`: code `kx` realizes element `x` -/
  KeyRel : Code → carrier → Prop
  /-- projectivity / enough points: every element has a realizer -/
  realized : ∀ x, ∃ kx, KeyRel kx x

/-- Dependent function space (eval-native, bare relation): `e` realizes
`Π x:A. B x` when applied to any realizer of any `x` it produces a realizer of
`B x`. -/
def RPi (A : Base) (B : A.carrier → RProp) (h : CHeap) (e : Code) : Prop :=
  ∀ x kx, A.KeyRel kx x → Produces h (e ⬝ kx) (B x)

end LeanStatefulAoc
