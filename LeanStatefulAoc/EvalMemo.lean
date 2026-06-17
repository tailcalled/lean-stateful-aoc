import LeanStatefulAoc.EvalTopos
import LeanStatefulAoc.Memo

set_option linter.style.longLine false

/-!
# The memoizer at the eval-model `EProp.Produces` level

`Memo.lean` proves the operational behaviour of `alloc`/`memo` directly on `eval`/`applyV`
(`memo_hit`, `memo_miss`, `eval_memoizer`, `HLe.commit`, `memoScan_commit`, `memoScan_cons_ne`)
— those facts are model-agnostic. This file lifts them to the **effectful tripos**
`EProp.Produces` (the relation the eval-model topos `EvalTopos` is built over), giving the
operational heart of the eventual `AC_dec` realizer: allocate a cell carrying an
**equality-guard** `eqr`, then look-up-or-commit the family's witness, with the cache scanned by
`eqr` so the choice respects the object's equality `ρ_A` (not syntactic code identity).
-/

namespace LeanStatefulAoc

open Code

/-- **Allocation.** `alloc · eqc · fam` appends a fresh cell `⟨eqc, fam, []⟩` (equality-guard
`eqc`, family `fam`, empty cache) and returns its location `loc |h|`. -/
theorem Evaluates.alloc {h : CHeap} {eqc fam : Code} :
    Evaluates h (Code.alloc ⬝ eqc ⬝ fam) (h ++ [⟨eqc, fam, []⟩]) (Code.loc h.length) := by
  have hhead : Evaluates h (Code.alloc ⬝ eqc) h (Code.alloc ⬝ eqc) := ⟨2, by simp only [eval, applyV]⟩
  exact Evaluates.mk_app hhead ⟨1, by simp only [applyV]⟩

/-- The allocation step is an `HLe` (monotone-state) extension. -/
theorem Evaluates.alloc_hle {h : CHeap} {eqc fam : Code} :
    HLe h (h ++ [⟨eqc, fam, []⟩]) := HLe.alloc h _

/-- **Memoizer hit, at the `EProp.Produces` level.** If `key` is a value and the eq-guarded scan
of cell `ℓ`'s cache finds a match returning `(h', some v)`, the memoizer produces `v` — so it
produces whatever `v` realizes (at the post-scan heap `h'`). -/
theorem EProp.memoizer_hit {h h' : CHeap} {ℓ : Nat} {key v : Code} {cell : CCell} {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (n : Nat) (hscan : memoScan (n + 2) h cell.eqr key cell.cache = some (h', some v))
    (hQ : Q.rel h' v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ key) :=
  ⟨h', v, ⟨n + 3, by
    rw [eval_memoizer]
    exact memo_hit (n + 2) h h h' ℓ key key v cell (hkeyval (n + 1)) hcell hscan⟩, hQ⟩

/-- **Memoizer miss, at the `EProp.Produces` level.** When the eq-guarded scan finds no match
(returning `(h', none)`), the memoizer runs the cell's family at `h'` and commits its value; the
result `v` then realizes `Q` at the committed heap. -/
theorem EProp.memoizer_miss {h h' h2 : CHeap} {ℓ : Nat} {key v : Code} {cell cell' : CCell}
    {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (n : Nat) (hscan : memoScan (n + 2) h cell.eqr key cell.cache = some (h', none))
    (hfam : eval (n + 2) h' (cell.fam ⬝ key) = some (h2, v))
    (hcell2 : h2[ℓ]? = some cell')
    (hQ : Q.rel (h2.set ℓ ⟨cell'.eqr, cell'.fam, (key, v) :: cell'.cache⟩) v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ key) :=
  ⟨h2.set ℓ ⟨cell'.eqr, cell'.fam, (key, v) :: cell'.cache⟩, v, ⟨n + 3, by
    rw [eval_memoizer]
    exact memo_miss (n + 2) h h h' h2 ℓ key key v cell cell'
      (hkeyval (n + 1)) hcell hscan hfam hcell2⟩, hQ⟩

/-- **Allocate-then-query** (the first move of the `AC_dec` choice section). On a *freshly*
allocated cell `loc |h|` (empty cache, equality-guard `eqc`, family `fam`), querying `key` always
misses (the empty cache needs no guard), so the memoizer runs `fam · key` and commits its value —
producing whatever the family's witness realizes. Combine with `Evaluates.alloc` to thread the
allocation effect. -/
theorem EProp.alloc_query {h h2 : CHeap} {eqc fam key v : Code} {cell' : CCell} {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) (h ++ [⟨eqc, fam, []⟩]) key = some (h ++ [⟨eqc, fam, []⟩], key))
    (n : Nat) (hfam : eval (n + 2) (h ++ [⟨eqc, fam, []⟩]) (fam ⬝ key) = some (h2, v))
    (hcell2 : h2[h.length]? = some cell')
    (hQ : Q.rel (h2.set h.length ⟨cell'.eqr, cell'.fam, (key, v) :: cell'.cache⟩) v) :
    Q.Produces (h ++ [⟨eqc, fam, []⟩]) (memo ⬝ loc h.length ⬝ key) := by
  refine EProp.memoizer_miss (cell := ⟨eqc, fam, []⟩) hkeyval List.getElem?_concat_length n
    ?_ hfam hcell2 hQ
  simp only [memoScan]

/-- **Equality-respecting single-valuedness (operational).** Querying a cell whose cache already
holds `(a, v)` at the front with a key `key` that the cell's guard *accepts* (`eqr · a · key ↠ tt`,
even when `a ≠ key` syntactically) produces the cached `v` — a hit, no recomputation. This is
exactly why the eq-guard fixes code-identity keying: two distinct realizers of the **same element**
(judged equal by the supplied decidable-equality realizer) map to the **same** memoized witness. -/
theorem EProp.memo_requery {h h' : CHeap} {ℓ : Nat} {key a v : Code} {rest : List (Code × Code)}
    {cell : CCell} {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (hcache : cell.cache = (a, v) :: rest)
    (n : Nat) (hg : eval (n + 2) h (cell.eqr ⬝ a ⬝ key) = some (h', Code.tt))
    (hQ : Q.rel h' v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ key) := by
  refine EProp.memoizer_hit hkeyval hcell n ?_ hQ
  rw [hcache]
  exact memoScan_found (n + 2) h h' cell.eqr a key v rest hg

/-- **Equality-respecting single-valuedness with eq-routing.** Querying a cell whose cache holds
`(k, v)` somewhere, where the guard *rejects* every earlier entry (`eqr · p.1 · key ↠ ff`) and
*accepts* `k` (`eqr · k · key ↠ tt`), produces `v`. This is the form the `AC_dec` `sv` proof needs:
under the cache invariant (keys pairwise-distinct under the guard, each realizing one element), the
element's committed witness is returned for *any* realizer used to query it. -/
theorem EProp.memo_hit_routed {h : CHeap} {ℓ : Nat} {key v k : Code}
    {pre post : List (Code × Code)} {cell : CCell} {Q : EProp}
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (hcache : cell.cache = pre ++ (k, v) :: post)
    (n : Nat)
    (hskip : ∀ p ∈ pre, eval (n + 2) h (cell.eqr ⬝ p.1 ⬝ key) = some (h, ff))
    (hhit : eval (n + 2) h (cell.eqr ⬝ k ⬝ key) = some (h, tt))
    (hQ : Q.rel h v) :
    Q.Produces h (memo ⬝ loc ℓ ⬝ key) := by
  refine EProp.memoizer_hit hkeyval hcell n ?_ hQ
  rw [hcache]
  exact memoScan_skip_hit (n + 2) h cell.eqr key v k post pre hskip hhit

/-! ### Adapting a decidable-equality realizer to the memo guard -/

/-- Turn a coproduct verdict `inl`/`inr` into the memo guard's `tt`/`ff`. -/
def caseTF : Code := case ⬝ (K ⬝ tt) ⬝ (K ⬝ ff)

/-- The **eq-guard built from a decidable-equality realizer** `r`: `eqrOfDec r · k₁ · k₂` runs
`r · k₁ · k₂` (which decides the equality, producing `inl`/`inr`) and maps the verdict to `tt`/`ff`
— exactly the `tt`/`ff` guard the memo cache scans by. This is the adapter that lets a topos
`HasDecEq` realizer key the memo cache. -/
def eqrOfDec (r : Code) : Code := Code.B ⬝ (Code.B ⬝ caseTF) ⬝ r

theorem caseTF_val {h : CHeap} : Evaluates h caseTF h caseTF :=
  ⟨3, by simp only [caseTF, eval, applyV]⟩

/-- `eqrOfDec r · k₁ · k₂` runs like `caseTF · (r · k₁ · k₂)`. -/
theorem eqrOfDec_app {r k1 k2 : Code} {h hh : CHeap} {v : Code}
    (hc : Evaluates h (caseTF ⬝ (r ⬝ k1 ⬝ k2)) hh v) :
    Evaluates h (eqrOfDec r ⬝ k1 ⬝ k2) hh v := by
  simp only [eqrOfDec]
  have hg : Evaluates h (Code.B ⬝ (Code.B ⬝ caseTF) ⬝ r ⬝ k1) h
      (S ⬝ (K ⬝ caseTF) ⬝ (r ⬝ k1)) :=
    Evaluates.Bsim (Evaluates.mk_app Evaluates.B1 ⟨1, by simp only [applyV]⟩)
  refine Evaluates.appHeadSwap hg Evaluates.S2 ?_
  apply Evaluates.headS
  exact Evaluates.appHeadSwap (Evaluates.headK caseTF_val) caseTF_val hc

/-- If the decidable-equality realizer judges `k₁`, `k₂` **equal** (`r · k₁ · k₂ ↠ inl · w`), the
guard reduces to `tt`. -/
theorem eqrOfDec_tt {r k1 k2 w : Code} {h h' : CHeap}
    (hr : Evaluates h (r ⬝ k1 ⬝ k2) h' (inl ⬝ w)) :
    Evaluates h (eqrOfDec r ⬝ k1 ⬝ k2) h' tt :=
  eqrOfDec_app (Evaluates.caseLβ' hr (Evaluates.headK ⟨1, by simp only [eval]⟩))

/-- If the decidable-equality realizer judges `k₁`, `k₂` **unequal** (`r · k₁ · k₂ ↠ inr · w`), the
guard reduces to `ff`. -/
theorem eqrOfDec_ff {r k1 k2 w : Code} {h h' : CHeap}
    (hr : Evaluates h (r ⬝ k1 ⬝ k2) h' (inr ⬝ w)) :
    Evaluates h (eqrOfDec r ⬝ k1 ⬝ k2) h' ff :=
  eqrOfDec_app (Evaluates.caseRβ' hr (Evaluates.headK ⟨1, by simp only [eval]⟩))

end LeanStatefulAoc
