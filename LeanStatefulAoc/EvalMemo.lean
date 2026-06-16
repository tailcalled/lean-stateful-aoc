import LeanStatefulAoc.EvalTopos
import LeanStatefulAoc.Memo

set_option linter.style.longLine false

/-!
# The memoizer at the eval-model `EProp.Produces` level

`Memo.lean` proves the operational behaviour of `alloc`/`memo` directly on `eval`/`applyV`
(`memo_hit`, `memo_miss`, `eval_memoizer`, `HLe.commit`, `find_commit`, `find_cons_ne`) — those
facts are model-agnostic. This file lifts them to the **effectful tripos** `EProp.Produces`
(the relation the eval-model topos `EvalTopos` is built over), giving the operational heart of
the eventual `AC_dec` realizer: allocate a memo cell, then look-up-or-commit the family's witness,
single-valued across distinct keys.
-/

namespace LeanStatefulAoc

open Code

/-- **Allocation.** `alloc · eqc · fam` appends a fresh cell `⟨fam, []⟩` (empty cache, family
`fam`) and returns its location `loc |h|`. The equality-guard `eqc` is recorded for the future
deceq-respecting key but ignored by the current code-identity cache. -/
theorem Evaluates.alloc {h : CHeap} {eqc fam : Code} :
    Evaluates h (Code.alloc ⬝ eqc ⬝ fam) (h ++ [⟨fam, []⟩]) (Code.loc h.length) := by
  have hhead : Evaluates h (Code.alloc ⬝ eqc) h (Code.alloc ⬝ eqc) := ⟨2, by simp only [eval, applyV]⟩
  exact Evaluates.mk_app hhead ⟨1, by simp only [applyV]⟩

/-- The allocation step is an `HLe` (monotone-state) extension. -/
theorem Evaluates.alloc_hle {h : CHeap} {fam : Code} :
    HLe h (h ++ [⟨fam, []⟩]) := HLe.alloc h _

/-- **Memoizer hit, at the `EProp.Produces` level.** If `key` is a value and cell `ℓ`'s cache
already maps it to `v`, the memoizer produces `v` with no further effects — so it produces
whatever `v` realizes. -/
theorem EProp.memoizer_hit {h : CHeap} {ℓ : Nat} {key v : Code} {cell : CCell} {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (hfind : cell.cache.find? (fun p => decide (p.1 = key)) = some (key, v))
    (hQ : Q.rel h v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ key) :=
  ⟨h, v, ⟨3, by
    rw [show (3 : Nat) = 0 + 3 from rfl, eval_memoizer]
    exact memo_hit 2 h h ℓ key key v cell (hkeyval 1) hcell hfind⟩, hQ⟩

/-- **Memoizer miss, at the `EProp.Produces` level.** On a key not yet cached, the memoizer runs
the cell's family (which produces `v` at fuel `n+2`) and commits it; the result `v` then realizes
`Q` at the committed heap. -/
theorem EProp.memoizer_miss {h h2 : CHeap} {ℓ : Nat} {key v : Code} {cell cell' : CCell} {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (hfind : cell.cache.find? (fun p => decide (p.1 = key)) = none)
    (n : Nat) (hfam : eval (n + 2) h (cell.fam ⬝ key) = some (h2, v))
    (hcell2 : h2[ℓ]? = some cell')
    (hQ : Q.rel (h2.set ℓ ⟨cell'.fam, (key, v) :: cell'.cache⟩) v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ key) :=
  ⟨h2.set ℓ ⟨cell'.fam, (key, v) :: cell'.cache⟩, v, ⟨n + 3, by
    rw [eval_memoizer]
    exact memo_miss (n + 2) h h h2 ℓ key key v cell cell'
      (hkeyval (n + 1)) hcell hfind hfam hcell2⟩, hQ⟩

/-- **Allocate-then-query** (the first move of the `AC_dec` choice section). On a *freshly*
allocated cell `loc |h|` (empty cache, family `fam`), querying `key` always misses, so the
memoizer runs `fam · key` and commits its value — producing whatever the family's witness
realizes. Combine with `Evaluates.alloc` to thread the allocation effect. -/
theorem EProp.alloc_query {h h2 : CHeap} {fam key v : Code} {cell' : CCell} {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) (h ++ [⟨fam, []⟩]) key = some (h ++ [⟨fam, []⟩], key))
    (n : Nat) (hfam : eval (n + 2) (h ++ [⟨fam, []⟩]) (fam ⬝ key) = some (h2, v))
    (hcell2 : h2[h.length]? = some cell')
    (hQ : Q.rel (h2.set h.length ⟨cell'.fam, (key, v) :: cell'.cache⟩) v) :
    Q.Produces (h ++ [⟨fam, []⟩]) (memo ⬝ loc h.length ⬝ key) := by
  refine EProp.memoizer_miss (cell := ⟨fam, []⟩) hkeyval ?_ rfl n hfam hcell2 hQ
  exact List.getElem?_concat_length

end LeanStatefulAoc
