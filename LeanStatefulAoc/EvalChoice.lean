import LeanStatefulAoc.EvalMemo

set_option linter.style.longLine false

/-!
# `AC_dec` in the eval model: the memoized choice section

The data of one `AC_dec` application is bundled as `AcCell` (eval-model port of `Choice.lean`'s
F-monad `AcCell`): an abstract index type `A`, a relation `KeyRel` saying which key codes realize
which index, an **equality-guard realizer** `eqr` that is *sound* (answers `tt`/`ff` exactly on
same/different indices), a family realizer `fam`, and a value-realizing relation `rel`.

Over its *valid* heaps (`ValidAt`: the cell exists, owns `eqr`/`fam`, its cache entries are typed,
and its keys realize pairwise-distinct indices) the memoizer is **single-valued**: querying with
*any* realizer of an already-committed index returns that index's committed witness (`AcCell.hit`),
because the eq-guard routes the scan past other indices' entries to the matching one. This is the
property that the now-deceq-respecting evaluator (eq-guarded `memoScan`) makes provable.
-/

namespace LeanStatefulAoc

open Code

universe u v

/-- Uniformize fuel over a finite list: if each `g c` (for `c ∈ l`) evaluates to `val` at `h`
(no heap change), there is one fuel `N` at which all of them do. -/
theorem uniformFuel {α : Type*} {h : CHeap} {g : α → Code} {val : Code} :
    ∀ (l : List α), (∀ c ∈ l, Evaluates h (g c) h val) →
      ∃ N, ∀ c ∈ l, eval N h (g c) = some (h, val) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons c rest ih =>
    intro hl
    obtain ⟨nc, hnc⟩ := hl c (by simp)
    obtain ⟨N, hN⟩ := ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
    refine ⟨max nc N, fun c' hc' => ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc''
    · exact eval_mono_le (Nat.le_max_left nc N) hnc
    · exact eval_mono_le (Nat.le_max_right nc N) (hN c' hc'')

namespace Eval

/-- The data of one `AC_dec` application in the eval model. -/
structure AcCell (A : Type u) (B : A → Type v) where
  /-- which key codes realize which index -/
  KeyRel : Code → A → Prop
  /-- the equality-guard realizer (`eqr · k · k' ↠ tt`/`ff` decides whether the indices match) -/
  eqr : Code
  /-- the family realizer (of `Π x. ‖B x‖`) -/
  fam : Code
  /-- which value codes realize which family member -/
  rel : (x : A) → Code → B x → Prop
  /-- the guard answers `tt` on codes realizing the **same** index, at any heap, purely -/
  sound_tt : ∀ {k k' : Code} {x : A}, KeyRel k x → KeyRel k' x →
    ∀ h, Evaluates h (eqr ⬝ k ⬝ k') h Code.tt
  /-- the guard answers `ff` on codes realizing **different** indices, at any heap, purely -/
  sound_ff : ∀ {k k' : Code} {x x' : A}, KeyRel k x → KeyRel k' x' → x ≠ x' →
    ∀ h, Evaluates h (eqr ⬝ k ⬝ k') h Code.ff
  /-- a key code realizes at most one index (`KeyRel` is a partial function code → index). In a
  realizability model with a decidable-equality realizer this follows from `sound`; we take it as
  data to stay constructive (no `Classical` over the abstract index `A`). -/
  keyRel_fn : ∀ {k : Code} {x x' : A}, KeyRel k x → KeyRel k x' → x = x'

namespace AcCell

variable {A : Type u} {B : A → Type v} (C : AcCell A B)

/-- Valid heaps for the cell at `ℓ`: it exists owning `eqr`/`fam`; every cache entry is typed
(its key realizes an index, its value realizes a member there); and the keys realize **pairwise
distinct** indices (a finite partial function on indices). -/
def ValidAt (ℓ : Nat) (h : CHeap) : Prop :=
  ∃ cell, h[ℓ]? = some cell ∧ cell.eqr = C.eqr ∧ cell.fam = C.fam ∧
    (∀ p ∈ cell.cache, ∃ x y, C.KeyRel p.1 x ∧ C.rel x p.2 y) ∧
    cell.cache.Pairwise (fun p q => ∀ x, C.KeyRel p.1 x → ¬ C.KeyRel q.1 x)

/-- **Allocation yields a valid cell.** The `AC_dec` program allocates `alloc · eqr · fam`,
producing a fresh cell `⟨eqr, fam, []⟩` at `|h|`; with an empty cache it is vacuously valid. -/
theorem validAt_alloc (h : CHeap) : C.ValidAt h.length (h ++ [⟨C.eqr, C.fam, []⟩]) :=
  ⟨⟨C.eqr, C.fam, []⟩, List.getElem?_concat_length, rfl, rfl, by simp, by simp⟩

variable {C}

/-- **Single-valued hit over a valid cache.** If `ℓ` is valid and some cache entry `(k, v)` has a
key realizing the queried index `x` (with `a` *any* value realizing `x`), then `memo (loc ℓ) a`
produces `v` — the committed witness for `x`, regardless of which realizer `a` is used to query.
The eq-guard routes the scan past every other index's entry (`sound_ff`) to the matching one
(`sound_tt`). -/
theorem hit {ℓ : Nat} {h : CHeap} {a k v : Code} {x : A} {cell : CCell}
    (ha : ∀ n, eval (n + 1) h a = some (h, a))
    (hKa : C.KeyRel a x) (hKk : C.KeyRel k x)
    (hv : C.ValidAt ℓ h) (hcell : h[ℓ]? = some cell) (hmem : (k, v) ∈ cell.cache)
    {Q : EProp} (hQ : Q.rel h v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ a) := by
  obtain ⟨cell', hcell', heqr, _, htyped, hpw⟩ := hv
  obtain rfl := Option.some.inj (hcell'.symm.trans hcell)
  -- split the cache around the matching entry
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  -- the guard rejects every earlier entry (different index) and accepts the matching one
  have hskip : ∀ p ∈ pre, Evaluates h (C.eqr ⬝ p.1 ⬝ a) h Code.ff := by
    intro p hp
    obtain ⟨xp, _, hKp, _⟩ := htyped p (by rw [hsplit]; exact List.mem_append_left _ hp)
    have hpk : ∀ x', C.KeyRel p.1 x' → ¬ C.KeyRel k x' := by
      rw [hsplit] at hpw
      exact (List.pairwise_append.mp hpw).2.2 p hp (k, v) List.mem_cons_self
    have hxp_ne : xp ≠ x := by rintro rfl; exact hpk _ hKp hKk
    exact C.sound_ff hKp hKa hxp_ne h
  have hhit : Evaluates h (C.eqr ⬝ k ⬝ a) h Code.tt := C.sound_tt hKk hKa h
  -- uniformize the guard fuels, then read off a successful scan
  obtain ⟨M, hM⟩ := uniformFuel (g := fun p : Code × Code => C.eqr ⬝ p.1 ⬝ a) pre hskip
  obtain ⟨nk, hnk⟩ := hhit
  refine EProp.memoizer_hit ha hcell (max M nk) ?_ hQ
  rw [heqr, hsplit]
  refine memoScan_skip_hit (max M nk + 2) h C.eqr a v k post pre (fun p hp => ?_) ?_
  · exact eval_mono_le (by omega) (hM p hp)
  · exact eval_mono_le (by omega) hnk

/-- **Totality + validity-preservation on a miss.** If the queried index `x` is *not yet*
committed (no cache key realizes it), the guard rejects every entry, so the scan misses; the
memoizer then runs the cell's family — which (by the `Π x. ‖B x‖` premise) produces a witness `v`
realizing `B x` — and commits `(a, v)`. The result `v` realizes the fiber, and the committed heap
is again valid (the new key `a` realizes `x`, distinct from every existing key's index). -/
theorem total_miss {ℓ : Nat} {h h2 : CHeap} {a v : Code} {x : A} {y : B x} {cell : CCell}
    (ha : ∀ n, eval (n + 1) h a = some (h, a))
    (hKa : C.KeyRel a x)
    (hcell : h[ℓ]? = some cell) (heqr : cell.eqr = C.eqr) (hfamc : cell.fam = C.fam)
    (htyped : ∀ p ∈ cell.cache, ∃ x' y', C.KeyRel p.1 x' ∧ C.rel x' p.2 y')
    (hpw : cell.cache.Pairwise (fun p q => ∀ x', C.KeyRel p.1 x' → ¬ C.KeyRel q.1 x'))
    (hmiss : ∀ p ∈ cell.cache, ¬ C.KeyRel p.1 x)
    (n : Nat) (hfam : eval (n + 2) h (C.fam ⬝ a) = some (h2, v)) (hframe : h2[ℓ]? = some cell)
    (hrel : C.rel x v y)
    {Q : EProp} (hQ : Q.rel (h2.set ℓ ⟨cell.eqr, cell.fam, (a, v) :: cell.cache⟩) v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ a) ∧
      C.ValidAt ℓ (h2.set ℓ ⟨cell.eqr, cell.fam, (a, v) :: cell.cache⟩) := by
  -- the guard rejects every existing entry (each realizes an index ≠ x)
  have hskip : ∀ p ∈ cell.cache, Evaluates h (cell.eqr ⬝ p.1 ⬝ a) h Code.ff := by
    intro p hp
    obtain ⟨x', _, hKp, _⟩ := htyped p hp
    have hx'_ne : x' ≠ x := fun heq => hmiss p hp (heq ▸ hKp)
    rw [heqr]; exact C.sound_ff hKp hKa hx'_ne h
  obtain ⟨M, hM⟩ := uniformFuel (g := fun p : Code × Code => cell.eqr ⬝ p.1 ⬝ a) cell.cache hskip
  refine ⟨?_, ?_⟩
  · -- Produces: miss → run family, commit
    refine EProp.memoizer_miss (h' := h) ha hcell (max M n) ?_ ?_ hframe hQ
    · exact memoScan_all_skip (max M n + 2) h cell.eqr a cell.cache
        (fun p hp => eval_mono_le (by omega) (hM p hp))
    · rw [hfamc]; exact eval_mono_le (by omega) hfam
  · -- validity preserved
    have hlt : ℓ < h2.length := by rw [List.getElem?_eq_some_iff] at hframe; exact hframe.1
    refine ⟨⟨cell.eqr, cell.fam, (a, v) :: cell.cache⟩, by rw [List.getElem?_set_self hlt],
      heqr, hfamc, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨x, y, hKa, hrel⟩
      · exact htyped p hp
    · refine List.pairwise_cons.mpr ⟨fun q hq x' hKax' => ?_, hpw⟩
      have hx' : x' = x := C.keyRel_fn hKax' hKa
      subst hx'; exact hmiss q hq

end AcCell

end Eval

end LeanStatefulAoc
