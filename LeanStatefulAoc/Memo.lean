import LeanStatefulAoc.Topos
import LeanStatefulAoc.EvalMono
import LeanStatefulAoc.FwdClosed

/-!
# Memo behaviour and single-valuedness (effectful core)

The AC_dec choice map is tracked by the memoizer `memo · (loc ℓ)`. Its correctness —
that it is a *single-valued* (equality-respecting) section — rests on the cache
behaviour of `eval`/`applyV`:

* **hit** — once `(key, v)` is the first cache match, the memoizer returns `v` with
  the heap unchanged;
* **miss** — otherwise it runs the cell's family on the key and **commits** the
  result;
* a commit is an `HLe` step (monotone state), and the committed entry sits at the
  front of the cache, so an immediate re-query **hits** the same `v` — single
  value.

These are proved by unfolding the well-founded `eval`/`applyV` with `simp only`.
-/

namespace LeanStatefulAoc

open Code

/-- **Memo hit.** If `x` evaluates to a value `key`, cell `ℓ` exists, and the first
cache match for `key` is `v`, then `memo (loc ℓ)` applied to `x` returns `(h1, v)` —
no new effects. -/
theorem memo_hit (fuel : Nat) (h h1 : CHeap) (ℓ : Nat) (x key v : Code) (cell : CCell)
    (hx : eval fuel h x = some (h1, key))
    (hcell : h1[ℓ]? = some cell)
    (hfind : cell.cache.find? (fun p => decide (p.1 = key)) = some (key, v)) :
    applyV fuel h (memo ⬝ (loc ℓ)) x = some (h1, v) := by
  simp only [applyV, hx, hcell, hfind]

/-- **Memo miss.** If there is no cache match for `key`, the memoizer runs the
cell's family on `key`, commits the result, and returns it. -/
theorem memo_miss (fuel : Nat) (h h1 h2 : CHeap) (ℓ : Nat) (x key v : Code)
    (cell cell' : CCell)
    (hx : eval fuel h x = some (h1, key))
    (hcell : h1[ℓ]? = some cell)
    (hfind : cell.cache.find? (fun p => decide (p.1 = key)) = none)
    (hfam : eval fuel h1 (cell.fam ⬝ key) = some (h2, v))
    (hcell2 : h2[ℓ]? = some cell') :
    applyV fuel h (memo ⬝ (loc ℓ)) x =
      some (h2.set ℓ ⟨cell'.fam, (key, v) :: cell'.cache⟩, v) := by
  simp only [applyV, hx, hcell, hfind, hfam, hcell2]

/-- A commit (replacing cell `ℓ` with the same family and a prepended cache entry)
is an `HLe` step: monotone state. -/
theorem HLe.commit (h : CHeap) (ℓ : Nat) (cell : CCell) (entry : Code × Code)
    (hcell : h[ℓ]? = some cell) :
    HLe h (h.set ℓ ⟨cell.fam, entry :: cell.cache⟩) := by
  have hlt : ℓ < h.length := by rw [List.getElem?_eq_some_iff] at hcell; exact hcell.1
  refine ⟨by simp, fun ℓ' c hc => ?_⟩
  by_cases hℓ : ℓ' = ℓ
  · subst hℓ
    rw [hcell] at hc; obtain rfl := Option.some.inj hc
    refine ⟨⟨cell.fam, entry :: cell.cache⟩, ?_, rfl, List.suffix_cons _ _⟩
    rw [List.getElem?_set_self hlt]
  · refine ⟨c, ?_, rfl, List.suffix_refl _⟩
    rw [List.getElem?_set_ne (Ne.symm hℓ)]; exact hc

/-- Running the memoizer reduces to its `applyV` behaviour: forcing `memo (loc ℓ)`
to itself costs no effects. -/
theorem eval_memoizer (fuel : Nat) (h : CHeap) (ℓ : Nat) (key : Code) :
    eval (fuel + 3) h (memo ⬝ loc ℓ ⬝ key) = applyV (fuel + 2) h (memo ⬝ loc ℓ) key := by
  simp only [eval, applyV]

/-- **Memoizer hit, at the `Produces` level.** If `key` is a value and cell `ℓ`'s
cache already maps it to `v`, the memoizer produces `v` with no further effects — so
it produces whatever `v` realizes. -/
theorem memoizer_hit (h : CHeap) (ℓ : Nat) (key v : Code) (cell : CCell) (Q : RProp)
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (hfind : cell.cache.find? (fun p => decide (p.1 = key)) = some (key, v))
    (hQ : Q.rel h v) :
    Produces h (memo ⬝ loc ℓ ⬝ key) Q := by
  refine ⟨h, v, ⟨3, ?_⟩, hQ⟩
  rw [show (3 : Nat) = 0 + 3 from rfl, eval_memoizer]
  exact memo_hit 2 h h ℓ key key v cell (hkeyval 1) hcell hfind

/-- **Memoizer miss, at the `Produces` level.** On a key not yet cached, the
memoizer runs the cell's family (which produces `v` at fuel `n+2`) and commits it;
the result `v` then realizes `Q` at the committed heap. -/
theorem memoizer_miss (h h2 : CHeap) (ℓ : Nat) (key v : Code) (cell cell' : CCell) (Q : RProp)
    (hkeyval : ∀ n, eval (n + 1) h key = some (h, key))
    (hcell : h[ℓ]? = some cell)
    (hfind : cell.cache.find? (fun p => decide (p.1 = key)) = none)
    (n : Nat) (hfam : eval (n + 2) h (cell.fam ⬝ key) = some (h2, v))
    (hcell2 : h2[ℓ]? = some cell')
    (hQ : Q.rel (h2.set ℓ ⟨cell'.fam, (key, v) :: cell'.cache⟩) v) :
    Produces h (memo ⬝ loc ℓ ⬝ key) Q := by
  refine ⟨h2.set ℓ ⟨cell'.fam, (key, v) :: cell'.cache⟩, v, ⟨n + 3, ?_⟩, hQ⟩
  rw [eval_memoizer]
  exact memo_miss (n + 2) h h h2 ℓ key key v cell cell' (hkeyval (n + 1)) hcell hfind hfam hcell2

/-- **Sequencing reduction.** `seq ⬝ e ⬝ k` forces `e` to a value once (threading
its effects), then runs the continuation `k` on that value — the clean
effect-sequencing that lets effectful realizers compose without call-by-name
duplication. -/
theorem eval_seq_some (N : Nat) (h h' : CHeap) (e k v : Code)
    (he : eval (N + 2) h e = some (h', v)) :
    eval (N + 3) h (seq ⬝ e ⬝ k) = eval (N + 2) h' (k ⬝ v) := by
  simp only [eval, applyV, he]

/-- **Monadic bind for the state modality.** `seq ⬝ e ⬝ k` produces an `R`-realizer
when `e` produces a `Q`-realizer and `k` produces an `R`-realizer from any
`Q`-realizer. This is the clean effectful composition (using fuel-monotonicity to
align the two sub-runs' fuels) that lets effectful realizers — and so the effectful
dependent product — compose without call-by-name duplication. -/
theorem Produces.bind {h : CHeap} {e k : Code} {Q R : RProp}
    (hQ : Produces h e Q) (hk : ∀ h' v, Q.rel h' v → Produces h' (k ⬝ v) R) :
    Produces h (seq ⬝ e ⬝ k) R := by
  obtain ⟨h', v, ⟨n0, hev0⟩, hqv⟩ := hQ
  obtain ⟨h'', w, ⟨m0, hevm⟩, hrw⟩ := hk h' v hqv
  refine ⟨h'', w, ⟨max n0 m0 + 3, ?_⟩, hrw⟩
  rw [eval_seq_some (max n0 m0) h h' e k v
        (eval_mono_le (Nat.le_trans (Nat.le_max_left n0 m0) (by omega)) hev0)]
  exact eval_mono_le (Nat.le_trans (Nat.le_max_right n0 m0) (by omega)) hevm

/-- **A realizer Produces its (forward-closed) proposition.** If a code `c` realizes
a forward-closed `P` and evaluates (purely) to a value `w` via `c ↠ w`, then `c`
produces a `P`-realizer — the value `w` still realizes `P` by forward-closure. This
is the bridge that lets a pure transport realizer, applied to a produced value,
re-enter the `Produces` modality (used by the effectful dependent product's
`symm`/`trans`). -/
theorem Produces.of_fwd {P : RProp} (hP : P.FwdClosed) {h h' : CHeap} {c w : Code}
    (hred : Code.Reds c w) (hev : Evaluates h c h' w) (hc : P.rel h' c) :
    Produces h c P :=
  ⟨h', w, hev, hP.reds hred hc⟩

/-! ### Single-valuedness of the cache -/

/-- A freshly-committed entry is at the cache front, so it is the first match: the
memoizer immediately returns the value just committed. -/
theorem find_commit (key v : Code) (rest : List (Code × Code)) :
    ((key, v) :: rest).find? (fun p => decide (p.1 = key)) = some (key, v) := by
  simp

/-- Committing a *different* key does not change the first match for `key'`: the
memoizer is single-valued — each key keeps its committed answer. -/
theorem find_cons_ne (key key' v : Code) (rest : List (Code × Code)) (hne : key ≠ key') :
    ((key, v) :: rest).find? (fun p => decide (p.1 = key')) =
      rest.find? (fun p => decide (p.1 = key')) := by
  simp [hne]

end LeanStatefulAoc

