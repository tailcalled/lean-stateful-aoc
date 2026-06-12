import Mathlib.Order.Basic
import Mathlib.Data.List.Basic

/-!
# The computation layer: monotone state, realizer syntax, the interpreter

Module 1 of the kernel design (see `THEORY.md` §5). Three layers:

* `T P` / `PT P` — the (partial) **monotone-update monad** over a preorder of
  conditions: from a condition, a computation may only *extend* it, so "the
  generic filter only grows / no backtracking" holds by construction.
* `F V` — **realizer syntax**: a mono-sorted free monad over exactly two
  effects — `memo` (eq-guarded memoizing lookup at a cell) and `alloc` (create
  a cell that *owns* its eq and family realizers). The Diaconescu firewall is
  what is *absent* here: no constructor reads or writes the heap directly,
  enumerates keys, observes cache sizes, or compares cells. In particular a
  client cannot commit a chosen value — on a miss the cell's own family
  realizer computes the value.
* `run` — the **fuel-indexed interpreter** of `F V` into `PT (Heap V)`. Fuel
  is unavoidable: a `memo` miss runs the cell's family realizer, an arbitrary
  program, which Lean cannot see terminating. Realizability statements assert
  termination per-realizer (`∃` fuel), BBC-style.

The code domain `V` stays abstract; the interpreter needs only a truth-decoder
`isTrue : V → Bool` for the answers of eq realizers. No `DecidableEq V` is
required anywhere: cells live in a grow-only list (`Loc` is a stable index, so
allocation is append and freshness is free), and key routing inside a cell is
done by the cell's own eq realizer, never by code equality.
-/

namespace LeanStatefulAoc

universe u v w

variable {P : Type u} [Preorder P]

/-! ## The monotone-update monad -/

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

/-- Steps are determined by their condition and value; the order witness is
proof-irrelevant. -/
theorem Step.ext {X : Type v} {c : P} {s t : Step X c}
    (hn : s.next = t.next) (hv : s.val = t.val) : s = t := by
  cases s; cases t
  subst hn; subst hv
  rfl

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

/-! ## The partial monotone-update monad -/

/-- The partial monotone-update monad: like `T`, but a computation may fail
(fuel exhaustion, stuck operation). Failure produces no condition extension. -/
def PT (P : Type u) [Preorder P] (X : Type v) : Type (max u v) :=
  (c : P) → Option (Step X c)

namespace PT

/-- Succeed without extending the condition. -/
protected def pure {X : Type v} (x : X) : PT P X := fun c => some ⟨c, le_refl c, x⟩

/-- Sequencing; extension witnesses compose by transitivity. (Deliberately
universe-heterogeneous, hence no `Monad` instance.) -/
protected def bind {X : Type v} {Y : Type w} (m : PT P X) (f : X → PT P Y) : PT P Y :=
  fun c =>
    (m c).bind fun s =>
      (f s.val s.next).map fun s' => ⟨s'.next, le_trans s.le s'.le, s'.val⟩

@[simp] theorem pure_apply {X : Type v} (x : X) (c : P) :
    (PT.pure x : PT P X) c = some ⟨c, le_refl c, x⟩ := rfl

/-- Inversion for `pure`. -/
theorem pure_eq_some {X : Type v} {x : X} {c : P} {s : Step X c}
    (h : (PT.pure x : PT P X) c = some s) : s.next = c ∧ s.val = x := by
  have he := Option.some.inj h
  exact ⟨(congrArg Step.next he).symm, (congrArg Step.val he).symm⟩

/-- Introduction for `bind`. -/
theorem bind_some {X : Type v} {Y : Type w} {m : PT P X} {f : X → PT P Y} {c : P}
    {s₁ : Step X c} {s₂ : Step Y s₁.next}
    (hm : m c = some s₁) (hf : f s₁.val s₁.next = some s₂) :
    PT.bind m f c = some ⟨s₂.next, le_trans s₁.le s₂.le, s₂.val⟩ := by
  simp [PT.bind, hm, hf]

/-- Left identity: holds definitionally up to structure eta and proof
irrelevance of the order witness. -/
@[simp] theorem pure_bind {X : Type v} {Y : Type w} (x : X) (f : X → PT P Y) :
    PT.bind (PT.pure x) f = f x := by
  funext c
  change (f x c).map
      (fun s' => (⟨s'.next, le_trans (le_refl c) s'.le, s'.val⟩ : Step Y c)) = f x c
  rcases h : f x c with _ | s' <;> rfl

/-- Inversion for `bind`. -/
theorem bind_eq_some {X : Type v} {Y : Type w} {m : PT P X} {f : X → PT P Y} {c : P}
    {s : Step Y c} (h : PT.bind m f c = some s) :
    ∃ s₁ : Step X c, m c = some s₁ ∧ ∃ s₂ : Step Y s₁.next,
      f s₁.val s₁.next = some s₂ ∧ s.next = s₂.next ∧ s.val = s₂.val := by
  unfold PT.bind at h
  rcases hm : m c with _ | s₁ <;> rw [hm] at h
  · simp at h
  · -- expose the `map` under the (now reduced) `bind`
    have h' : (f s₁.val s₁.next).map
        (fun s₂ => (⟨s₂.next, le_trans s₁.le s₂.le, s₂.val⟩ : Step Y c)) = some s := h
    rcases hf : f s₁.val s₁.next with _ | s₂ <;> rw [hf] at h'
    · simp at h'
    · have he := Option.some.inj h'
      exact ⟨s₁, rfl, s₂, hf,
        (congrArg Step.next he).symm, (congrArg Step.val he).symm⟩

/-- Lift a success of `bind` along componentwise lifts (e.g. to more fuel). -/
theorem bind_mono {X : Type v} {Y : Type w} {m m' : PT P X} {f f' : X → PT P Y}
    (hm : ∀ (c : P) (s : Step X c), m c = some s → m' c = some s)
    (hf : ∀ (x : X) (c : P) (s : Step Y c), f x c = some s → f' x c = some s) :
    ∀ (c : P) (s : Step Y c), PT.bind m f c = some s → PT.bind m' f' c = some s := by
  intro c s h
  obtain ⟨s₁, h₁, s₂, h₂, hn, hv⟩ := PT.bind_eq_some h
  rw [PT.bind_some (hm _ _ h₁) (hf _ _ _ h₂)]
  exact congrArg some (Step.ext hn.symm hv.symm)

end PT

/-! ## Realizer syntax -/

/-- Cell identity. Cells live in a grow-only list, so a `Loc` is a stable
index; allocation hands out the current length. -/
abbrev Loc : Type := ℕ

/-- Realizer syntax: the free monad over the two heap effects, mono-sorted
(every computation returns a code in `V`) so that the eq/family fields of
`alloc` are strictly positive with a uniform parameter.

* `ret v` — return the code `v`.
* `memo ℓ a k` — consult cell `ℓ` at key `a`: eq-guarded lookup; on a miss the
  cell's own family realizer computes and commits the value; either way `k`
  continues with the resulting code.
* `alloc eqr fam k` — create a fresh cell owning the eq realizer `eqr` and the
  family realizer `fam`; `k` continues with its location.

The Diaconescu firewall is what is *absent*: no constructor inspects the heap,
compares cells, or writes a chosen value. -/
inductive F (V : Type u) : Type u where
  /-- return a code -/
  | ret : V → F V
  /-- eq-guarded memoizing lookup at a cell -/
  | memo : Loc → V → (V → F V) → F V
  /-- allocate a cell owning its eq and family realizers -/
  | alloc : (V → V → F V) → (V → F V) → (Loc → F V) → F V

namespace F

variable {V : Type u}

/-- Graft a continuation onto every `ret` leaf. The label fields of `alloc`
are *not* rewritten: a cell's eq and family realizers are closed subprograms,
fixed at allocation. -/
protected def bind : F V → (V → F V) → F V
  | ret v, g => g v
  | memo ℓ a k, g => memo ℓ a fun v => (k v).bind g
  | alloc eqr fam k, g => alloc eqr fam fun ℓ => (k ℓ).bind g

@[simp] theorem ret_bind (v : V) (g : V → F V) : (ret v).bind g = g v := rfl

@[simp] theorem bind_ret (m : F V) : m.bind ret = m := by
  induction m with
  | ret v => rfl
  | memo ℓ a k ih => exact congrArg (memo ℓ a) (funext ih)
  | alloc eqr fam k ih_eqr ih_fam ih_k => exact congrArg (alloc eqr fam) (funext ih_k)

theorem bind_assoc (m : F V) (f g : V → F V) :
    (m.bind f).bind g = m.bind fun v => (f v).bind g := by
  induction m with
  | ret v => rfl
  | memo ℓ a k ih => exact congrArg (memo ℓ a) (funext ih)
  | alloc eqr fam k ih_eqr ih_fam ih_k => exact congrArg (alloc eqr fam) (funext ih_k)

end F

/-- The choice realizer is one line: eq-guarded memoizing lookup at the cell
allocated for this `AC_dec` application. Totality, single-valuedness, and
extensionality are semantic theorems about `run`, not visible in the syntax. -/
def memoizer {V : Type u} (ℓ : Loc) : V → F V := fun a => F.memo ℓ a F.ret

/-! ## The heap of cells -/

/-- A cell: the label it owns (its eq and family realizers, fixed at
allocation) and its cache of committed `(key, value)` code pairs, newest
first. -/
structure Cell (V : Type u) : Type u where
  /-- the eq realizer the cell routes keys with -/
  eqr : V → V → F V
  /-- the family realizer that computes values on a miss -/
  fam : V → F V
  /-- committed entries, newest first -/
  cache : List (V × V)

namespace Cell

variable {V : Type u}

/-- Cell extension: same label, cache extended by newer entries. -/
def Le (c c' : Cell V) : Prop :=
  c.eqr = c'.eqr ∧ c.fam = c'.fam ∧ ∃ p, c'.cache = p ++ c.cache

theorem Le.refl (c : Cell V) : c.Le c := ⟨rfl, rfl, [], rfl⟩

theorem Le.trans {a b c : Cell V} (h₁ : a.Le b) (h₂ : b.Le c) : a.Le c := by
  obtain ⟨he₁, hf₁, p, hp⟩ := h₁
  obtain ⟨he₂, hf₂, q, hq⟩ := h₂
  exact ⟨he₁.trans he₂, hf₁.trans hf₂, q ++ p, by rw [hq, hp, List.append_assoc]⟩

theorem Le.antisymm {a b : Cell V} (h₁ : a.Le b) (h₂ : b.Le a) : a = b := by
  obtain ⟨he, hf, p, hp⟩ := h₁
  obtain ⟨-, -, q, hq⟩ := h₂
  have hcache : a.cache = b.cache := by
    have hlen : b.cache.length = p.length + a.cache.length := by
      rw [hp, List.length_append]
    have hlen' : a.cache.length = q.length + b.cache.length := by
      rw [hq, List.length_append]
    have hp0 : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hp, hp0, List.nil_append]
  cases a; cases b
  simp only [Cell.mk.injEq]
  exact ⟨he, hf, hcache⟩

end Cell

/-- The heap: a grow-only list of cells. `Loc`s are stable indices; allocation
is append, so freshness needs no bookkeeping. -/
abbrev Heap (V : Type u) : Type u := List (Cell V)

namespace Heap

variable {V : Type u}

/-- Heap extension: every existing cell persists with the same label and an
extended cache; new cells may appear. Nothing is ever removed. -/
instance : LE (Heap V) where
  le h h' := ∀ (ℓ : Loc) (c : Cell V), h[ℓ]? = some c → ∃ c', h'[ℓ]? = some c' ∧ c.Le c'

theorem le_def {h h' : Heap V} :
    h ≤ h' ↔
      ∀ (ℓ : Loc) (c : Cell V), h[ℓ]? = some c → ∃ c', h'[ℓ]? = some c' ∧ c.Le c' :=
  Iff.rfl

instance : PartialOrder (Heap V) where
  le_refl h := fun _ c hc => ⟨c, hc, Cell.Le.refl c⟩
  le_trans h₁ h₂ h₃ h₁₂ h₂₃ := fun ℓ c hc => by
    obtain ⟨c', hc', l₁⟩ := h₁₂ ℓ c hc
    obtain ⟨c'', hc'', l₂⟩ := h₂₃ ℓ c' hc'
    exact ⟨c'', hc'', l₁.trans l₂⟩
  le_antisymm h h' hab hba := by
    apply List.ext_getElem?
    intro ℓ
    rcases e : h[ℓ]? with _ | c
    · rcases e' : h'[ℓ]? with _ | c'
      · rfl
      · obtain ⟨c'', hc'', -⟩ := hba ℓ c' e'
        rw [e] at hc''
        cases hc''
    · obtain ⟨c', hc', l₁⟩ := hab ℓ c e
      obtain ⟨c'', hc'', l₂⟩ := hba ℓ c' hc'
      rw [e] at hc''
      obtain rfl : c = c'' := Option.some.inj hc''
      rw [hc']
      exact congrArg some (Cell.Le.antisymm l₁ l₂)

/-- Update the cell at `ℓ` in place (no-op if `ℓ` is unallocated). -/
def updateCell : Heap V → Loc → (Cell V → Cell V) → Heap V
  | [], _, _ => []
  | c :: t, 0, f => f c :: t
  | c :: t, ℓ + 1, f => c :: updateCell t ℓ f

theorem getElem?_updateCell_self :
    ∀ (h : Heap V) (ℓ : Loc) (f : Cell V → Cell V),
      (updateCell h ℓ f)[ℓ]? = h[ℓ]?.map f
  | [], _, _ => by simp [updateCell]
  | c :: t, 0, f => by simp [updateCell]
  | c :: t, ℓ + 1, f => by
      simpa [updateCell] using getElem?_updateCell_self t ℓ f

theorem getElem?_updateCell_ne :
    ∀ (h : Heap V) {ℓ ℓ' : Loc} (f : Cell V → Cell V),
      ℓ' ≠ ℓ → (updateCell h ℓ f)[ℓ']? = h[ℓ']?
  | [], _, _, _, _ => by simp [updateCell]
  | c :: t, 0, 0, f, hne => absurd rfl hne
  | c :: t, 0, ℓ' + 1, f, _ => by simp [updateCell]
  | c :: t, ℓ + 1, 0, f, _ => by simp [updateCell]
  | c :: t, ℓ + 1, ℓ' + 1, f, hne => by
      have hne' : ℓ' ≠ ℓ := fun hh => hne (congrArg (· + 1) hh)
      simpa [updateCell] using getElem?_updateCell_ne t f hne'

/-- Commit `(a, b)` at cell `ℓ`. (Total: a no-op at an unallocated `ℓ`; the
interpreter only commits at allocated cells.) -/
def commit (h : Heap V) (ℓ : Loc) (a b : V) : Heap V :=
  updateCell h ℓ fun c => { c with cache := (a, b) :: c.cache }

theorem le_commit (h : Heap V) (ℓ : Loc) (a b : V) : h ≤ h.commit ℓ a b := by
  intro ℓ' c hc
  by_cases hℓ : ℓ' = ℓ
  · subst hℓ
    refine ⟨{ c with cache := (a, b) :: c.cache }, ?_, rfl, rfl, [(a, b)], rfl⟩
    rw [commit, getElem?_updateCell_self, hc]
    rfl
  · exact ⟨c, by rw [commit, getElem?_updateCell_ne _ _ hℓ]; exact hc, Cell.Le.refl c⟩

/-- Allocate a fresh cell with the given label; its location is the current
length. -/
def alloc (h : Heap V) (eqr : V → V → F V) (fam : V → F V) : Heap V :=
  h ++ [⟨eqr, fam, []⟩]

theorem le_alloc (h : Heap V) (eqr : V → V → F V) (fam : V → F V) :
    h ≤ h.alloc eqr fam := by
  intro ℓ c hc
  refine ⟨c, ?_, Cell.Le.refl c⟩
  have hlt : ℓ < h.length := by
    rcases Nat.lt_or_ge ℓ h.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hc
      cases hc
  rw [alloc, List.getElem?_append_left hlt]
  exact hc

end Heap

/-! ## The fuel-indexed interpreter -/

variable {V : Type u}

/-- Committing as a step of the partial monotone-update monad, passing the
committed value through. -/
def commitPT (ℓ : Loc) (a b : V) : PT (Heap V) V :=
  fun h => some ⟨h.commit ℓ a b, Heap.le_commit h ℓ a b, b⟩

/-- Allocation as a step of the partial monotone-update monad, returning the
fresh location. -/
def allocPT (eqr : V → V → F V) (fam : V → F V) : PT (Heap V) Loc :=
  fun h => some ⟨h.alloc eqr fam, Heap.le_alloc h eqr fam, h.length⟩

/-- Inversion for `commitPT`. -/
theorem commitPT_eq_some {ℓ : Loc} {a b : V} {h : Heap V} {s : Step V h}
    (hc : commitPT ℓ a b h = some s) : s.next = h.commit ℓ a b ∧ s.val = b := by
  have he := Option.some.inj hc
  exact ⟨(congrArg Step.next he).symm, (congrArg Step.val he).symm⟩

/-- Inversion for `allocPT`. -/
theorem allocPT_eq_some {eqr : V → V → F V} {fam : V → F V} {h : Heap V}
    {s : Step Loc h} (hc : allocPT eqr fam h = some s) :
    s.next = h.alloc eqr fam ∧ s.val = h.length := by
  have he := Option.some.inj hc
  exact ⟨(congrArg Step.next he).symm, (congrArg Step.val he).symm⟩

mutual

/-- Interpret a realizer into the partial monotone-update monad over the heap.
`isTrue` decodes the answers of eq realizers. The only failure modes are fuel
exhaustion and `memo` at an unallocated cell.

The `memo` case is the model's heart: eq-guarded scan of the cell's cache
(running the cell's own eq realizer, whose effects persist — no rollback); on
a hit, continue with the stored code; on a miss, run the cell's own family
realizer, commit its value, continue. The client never supplies the committed
value. -/
def run (isTrue : V → Bool) (fuel : ℕ) (e : F V) : PT (Heap V) V :=
  match fuel, e with
  | 0, _ => fun _ => none
  | _ + 1, .ret v => PT.pure v
  | n + 1, .memo ℓ a k => fun h =>
    match h[ℓ]? with
    | none => none
    | some cell =>
      (PT.bind (scan isTrue n cell.eqr a cell.cache) fun hit? =>
        match hit? with
        | some b => run isTrue n (k b)
        | none =>
          PT.bind (PT.bind (run isTrue n (cell.fam a)) (commitPT ℓ a)) fun b =>
            run isTrue n (k b)) h
  | n + 1, .alloc eqr fam k =>
    PT.bind (allocPT eqr fam) fun ℓ => run isTrue n (k ℓ)
termination_by (fuel, 0)

/-- Scan a cache for a key matching `a` under the cell's eq realizer, threading
the eq realizer's heap effects. Returns the first matching entry's value. -/
def scan (isTrue : V → Bool) (fuel : ℕ) (eqr : V → V → F V) (a : V) :
    List (V × V) → PT (Heap V) (Option V)
  | [] => PT.pure none
  | (key, val) :: rest =>
    PT.bind (run isTrue fuel (eqr a key)) fun r =>
      if isTrue r then PT.pure (some val) else scan isTrue fuel eqr a rest
termination_by entries => (fuel, entries.length + 1)

end

/-! ### Equation lemmas

`run` and `scan` are defined by well-founded recursion, so they do not unfold
definitionally; these are the equations proofs work with. -/

variable {isTrue : V → Bool}

@[simp] theorem run_zero (e : F V) : run isTrue 0 e = fun _ => none := by
  rw [run]

@[simp] theorem run_ret (n : ℕ) (v : V) : run isTrue (n + 1) (F.ret v) = PT.pure v := by
  rw [run]

@[simp] theorem run_memo (n : ℕ) (ℓ : Loc) (a : V) (k : V → F V) :
    run isTrue (n + 1) (F.memo ℓ a k) = fun h =>
      match h[ℓ]? with
      | none => none
      | some cell =>
        (PT.bind (scan isTrue n cell.eqr a cell.cache) fun hit? =>
          match hit? with
          | some b => run isTrue n (k b)
          | none =>
            PT.bind (PT.bind (run isTrue n (cell.fam a)) (commitPT ℓ a)) fun b =>
              run isTrue n (k b)) h := by
  rw [run]

@[simp] theorem run_alloc (n : ℕ) (eqr : V → V → F V) (fam : V → F V) (k : Loc → F V) :
    run isTrue (n + 1) (F.alloc eqr fam k) =
      PT.bind (allocPT eqr fam) fun ℓ => run isTrue n (k ℓ) := by
  rw [run]

@[simp] theorem scan_nil (fuel : ℕ) (eqr : V → V → F V) (a : V) :
    scan isTrue fuel eqr a [] = PT.pure none := by
  rw [scan]

@[simp] theorem scan_cons (fuel : ℕ) (eqr : V → V → F V) (a key val : V)
    (rest : List (V × V)) :
    scan isTrue fuel eqr a ((key, val) :: rest) =
      PT.bind (run isTrue fuel (eqr a key)) fun r =>
        if isTrue r then PT.pure (some val) else scan isTrue fuel eqr a rest := by
  rw [scan]

/-- Inversion: running `ret` returns the value and leaves the heap alone. -/
theorem run_ret_inv {fuel : ℕ} {v : V} {h : Heap V} {s : Step V h}
    (hr : run isTrue fuel (F.ret v) h = some s) : s.next = h ∧ s.val = v := by
  cases fuel with
  | zero => rw [run_zero] at hr; cases hr
  | succ n => rw [run_ret] at hr; exact PT.pure_eq_some hr

/-! ### Fuel monotonicity

Success is stable under extra fuel — needed to compose independently-obtained
runs at a common fuel. -/

/-- Scan inherits fuel monotonicity from a run-level lift at the same fuels. -/
theorem scan_fuel_mono_aux {n n' : ℕ}
    (ihrun : ∀ (e : F V) (h : Heap V) (s : Step V h),
      run isTrue n e h = some s → run isTrue n' e h = some s) :
    ∀ {entries : List (V × V)} {eqr : V → V → F V} {a : V} {h : Heap V}
      {s : Step (Option V) h},
      scan isTrue n eqr a entries h = some s →
        scan isTrue n' eqr a entries h = some s := by
  intro entries
  induction entries with
  | nil =>
    intro eqr a h s hs
    rw [scan_nil] at hs
    rw [scan_nil]
    exact hs
  | cons e rest ih =>
    obtain ⟨key, val⟩ := e
    intro eqr a h s hs
    rw [scan_cons] at hs
    rw [scan_cons]
    refine PT.bind_mono (fun c s' h' => ihrun _ _ _ h') ?_ h s hs
    intro r c s' h'
    by_cases ht : isTrue r
    · rw [if_pos ht] at h' ⊢
      exact h'
    · rw [if_neg ht] at h' ⊢
      exact ih h'

/-- **Fuel monotonicity**: a successful run stays successful, with the same
result, at any larger fuel. -/
theorem run_fuel_mono :
    ∀ {fuel fuel' : ℕ}, fuel ≤ fuel' →
      ∀ {e : F V} {h : Heap V} {s : Step V h},
        run isTrue fuel e h = some s → run isTrue fuel' e h = some s := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' _ e h s hs
    rw [run_zero] at hs
    cases hs
  | succ m ihm =>
    intro fuel' hle e h s hs
    obtain ⟨m', rfl⟩ : ∃ m', fuel' = m' + 1 := ⟨fuel' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases e with
    | ret v =>
      rw [run_ret] at hs
      rw [run_ret]
      exact hs
    | memo ℓ a k =>
      simp only [run_memo] at hs ⊢
      rcases hcell : h[ℓ]? with _ | cell
      · rw [hcell] at hs
        simp at hs
      · rw [hcell] at hs
        refine PT.bind_mono
          (fun c s' h' => scan_fuel_mono_aux (fun _ _ _ hr => ihm hm hr) h') ?_ h s hs
        intro hit? c s' h'
        rcases hit? with _ | b
        · exact PT.bind_mono
            (PT.bind_mono (fun _ _ hr => ihm hm hr) (fun _ _ _ hc => hc))
            (fun _ _ _ hr => ihm hm hr) c s' h'
        · exact ihm hm h'
    | alloc eqr fam k =>
      rw [run_alloc] at hs
      rw [run_alloc]
      exact PT.bind_mono (fun _ _ ha => ha) (fun _ _ _ hr => ihm hm hr) h s hs

/-- A successful scan hit returns a value stored in the cache. (The key it was
stored under is existential: which entry matched depends on the eq realizer.) -/
theorem scan_val_mem {fuel : ℕ} {eqr : V → V → F V} {a : V} {entries : List (V × V)} :
    ∀ {h : Heap V} {s : Step (Option V) h} {b : V},
      scan isTrue fuel eqr a entries h = some s → s.val = some b →
      ∃ k, (k, b) ∈ entries := by
  induction entries with
  | nil =>
    intro h s b hs hv
    rw [scan_nil] at hs
    obtain ⟨-, hval⟩ := PT.pure_eq_some hs
    rw [hval] at hv
    cases hv
  | cons e rest ih =>
    obtain ⟨key, val⟩ := e
    intro h s b hs hv
    rw [scan_cons] at hs
    obtain ⟨s₁, -, s₂, hf, -, hval⟩ := PT.bind_eq_some hs
    by_cases ht : isTrue s₁.val
    · rw [if_pos ht] at hf
      obtain ⟨-, hval₂⟩ := PT.pure_eq_some hf
      rw [hval, hval₂] at hv
      obtain rfl := Option.some.inj hv
      exact ⟨key, List.mem_cons_self ..⟩
    · rw [if_neg ht] at hf
      have : s₂.val = some b := by rw [← hval, hv]
      obtain ⟨k, hk⟩ := ih hf this
      exact ⟨k, List.mem_cons_of_mem _ hk⟩

end LeanStatefulAoc
