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

/-- **Memo hit.** If `x` evaluates to a value `key`, cell `ℓ` exists, and the eq-guarded
cache scan finds a match returning `(h', some v)`, then `memo (loc ℓ)` applied to `x` returns
`(h', v)`. -/
theorem memo_hit (fuel : Nat) (h h1 h' : CHeap) (ℓ : Nat) (x key v : Code) (cell : CCell)
    (hx : eval fuel h x = some (h1, key))
    (hcell : h1[ℓ]? = some cell)
    (hscan : memoScan fuel h1 cell.eqr key cell.cache = some (h', some v)) :
    applyV fuel h (memo ⬝ (loc ℓ)) x = some (h', v) := by
  simp only [applyV, hx, hcell, hscan]

/-- **Memo miss.** If the eq-guarded scan finds no match (returning `(h', none)`), the memoizer
runs the cell's family on `key` (at the post-scan heap `h'`), commits the result, and returns it. -/
theorem memo_miss (fuel : Nat) (h h1 h' h2 : CHeap) (ℓ : Nat) (x key v : Code)
    (cell cell' : CCell)
    (hx : eval fuel h x = some (h1, key))
    (hcell : h1[ℓ]? = some cell)
    (hscan : memoScan fuel h1 cell.eqr key cell.cache = some (h', none))
    (hfam : eval fuel h' (cell.fam ⬝ key) = some (h2, v))
    (hcell2 : h2[ℓ]? = some cell') :
    applyV fuel h (memo ⬝ (loc ℓ)) x =
      some (h2.set ℓ ⟨cell'.eqr, cell'.fam, (key, v) :: cell'.cache⟩, v) := by
  simp only [applyV, hx, hcell, hscan, hfam, hcell2]

/-- A commit (replacing cell `ℓ` with the same eq-guard, same family, and a prepended cache
entry) is an `HLe` step: monotone state. -/
theorem HLe.commit (h : CHeap) (ℓ : Nat) (cell : CCell) (entry : Code × Code)
    (hcell : h[ℓ]? = some cell) :
    HLe h (h.set ℓ ⟨cell.eqr, cell.fam, entry :: cell.cache⟩) := by
  have hlt : ℓ < h.length := by rw [List.getElem?_eq_some_iff] at hcell; exact hcell.1
  refine ⟨by simp, fun ℓ' c hc => ?_⟩
  by_cases hℓ : ℓ' = ℓ
  · subst hℓ
    rw [hcell] at hc; obtain rfl := Option.some.inj hc
    refine ⟨⟨cell.eqr, cell.fam, entry :: cell.cache⟩, ?_, rfl, List.suffix_cons _ _⟩
    rw [List.getElem?_set_self hlt]
  · refine ⟨c, ?_, rfl, List.suffix_refl _⟩
    rw [List.getElem?_set_ne (Ne.symm hℓ)]; exact hc

/-- Running the memoizer reduces to its `applyV` behaviour: forcing `memo (loc ℓ)`
to itself costs no effects. -/
theorem eval_memoizer (fuel : Nat) (h : CHeap) (ℓ : Nat) (key : Code) :
    eval (fuel + 3) h (memo ⬝ loc ℓ ⬝ key) = applyV (fuel + 2) h (memo ⬝ loc ℓ) key := by
  simp only [eval, applyV]

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

/-! ### Single-valuedness of the eq-guarded cache -/

/-- The eq-guard accepts a cached key: if `eqr · k · key ↠ tt` for a cached key `k`, the scan of
`(k, v) :: rest` returns `v`. With `k = key` and a reflexive guard this is "a freshly-committed
entry is re-found immediately"; with `k ≠ key` (different code) but guard-equal it is the
**equality-respecting hit** — two realizers of the *same* element get the *same* committed value. -/
theorem memoScan_found (fuel : Nat) (h h' : CHeap) (eqr k key v : Code) (rest : List (Code × Code))
    (hg : eval fuel h (Code.app (Code.app eqr k) key) = some (h', Code.tt)) :
    memoScan fuel h eqr key ((k, v) :: rest) = some (h', some v) := by
  simp only [memoScan, hg]

/-- Committing a key the guard *rejects* does not change the scan result: if
`eqr · k · key ↠ verdict ≠ tt`, the entry `(k, _)` is skipped (threading the guard's heap). So
distinct (under the guard) keys keep their committed answers — single-valuedness. -/
theorem memoScan_cons_ne (fuel : Nat) (h h' : CHeap) (eqr k key v verdict : Code)
    (rest : List (Code × Code)) (hv : verdict ≠ Code.tt)
    (hg : eval fuel h (Code.app (Code.app eqr k) key) = some (h', verdict)) :
    memoScan fuel h eqr key ((k, v) :: rest) = memoScan fuel h' eqr key rest := by
  cases verdict <;> first | exact absurd rfl hv | simp only [memoScan, hg]

/-- **Eq-routing of the scan.** When the guard (purely) *rejects* every cache entry before some
`(k, v)` (`eqr · p.1 · key ↠ ff`) and *accepts* `k` (`eqr · k · key ↠ tt`), the scan skips the
rejected prefix and returns `v`. With the cache invariant "keys are pairwise distinct under the
guard, and each key realizes one element", this delivers the choice section's single value at an
element regardless of which realizer `key` is used to query. -/
theorem memoScan_skip_hit (fuel : Nat) (h : CHeap) (eqr key v k : Code)
    (post : List (Code × Code)) :
    ∀ (pre : List (Code × Code)),
      (∀ p ∈ pre, eval fuel h (Code.app (Code.app eqr p.1) key) = some (h, Code.ff)) →
      eval fuel h (Code.app (Code.app eqr k) key) = some (h, Code.tt) →
      memoScan fuel h eqr key (pre ++ (k, v) :: post) = some (h, some v) := by
  intro pre
  induction pre with
  | nil => intro _ hhit; exact memoScan_found fuel h h eqr k key v post hhit
  | cons p rest ih =>
    intro hskip hhit
    obtain ⟨pk, pv⟩ := p
    rw [List.cons_append,
        memoScan_cons_ne fuel h h eqr pk key pv Code.ff (rest ++ (k, v) :: post)
          (by decide) (hskip (pk, pv) (by simp))]
    exact ih (fun q hq => hskip q (List.mem_cons_of_mem _ hq)) hhit

/-- **The scan misses.** If the (pure) guard *rejects* every cache entry (`eqr · p.1 · key ↠ ff`),
the scan returns `none` (no match) — the miss path then runs the cell's family. -/
theorem memoScan_all_skip (fuel : Nat) (h : CHeap) (eqr key : Code) :
    ∀ (cache : List (Code × Code)),
      (∀ p ∈ cache, eval fuel h (Code.app (Code.app eqr p.1) key) = some (h, Code.ff)) →
      memoScan fuel h eqr key cache = some (h, none) := by
  intro cache
  induction cache with
  | nil => intro _; simp only [memoScan]
  | cons p rest ih =>
    intro hskip
    obtain ⟨pk, pv⟩ := p
    rw [memoScan_cons_ne fuel h h eqr pk key pv Code.ff rest (by decide)
          (hskip (pk, pv) (by simp))]
    exact ih (fun q hq => hskip q (List.mem_cons_of_mem _ hq))

end LeanStatefulAoc

