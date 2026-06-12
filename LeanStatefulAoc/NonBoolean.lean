/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanStatefulAoc.Computation

/-!
# Non-Booleanness: EM is not realized (K1)

The headline theorem, in the bar-free form of `THEORY.md` §3. Setup: a single
cell (`Loc 0`) for the generic `s : ℕ → Bool`, labeled with code-equality on
keys and the **constant-false family**, allocated and empty (`h₀`). For
`φ := ∃ n, s n = true`:

* `φ ∨ ¬φ` is not realized at `h₀` — horn `inl` dies because memo-only
  operations never let a program write `true` into the cell (the firewall,
  here the `Protected` invariant); horn `inr` dies because the *typed
  possibilium* `h' + (0 : m ↦ true)` is a legitimate heap extension that
  realizes `φ` (the genericity).
* `¬¬φ` *is* forced everywhere above `h₀`.
* hence `¬¬φ → φ` is not realized: the model is non-Boolean, not merely
  EM-free.

Propositions here are realizer-irrelevant, so realizability of the
propositional fragment is plain forcing; the disjunction realizer contributes
only its tag.
-/

namespace LeanStatefulAoc

/-- The code domain for K1: numerals (keys) and booleans (values, eq answers). -/
inductive V₀ : Type where
  /-- a numeral key -/
  | nat : ℕ → V₀
  /-- a boolean value -/
  | bool : Bool → V₀
  deriving DecidableEq

/-- Truth-decoder for eq-realizer answers. -/
def isTrue₀ : V₀ → Bool
  | .bool true => true
  | _ => false

/-- The generic cell's eq realizer: code equality (on numerals this is exactly
equality of `ℕ`). -/
abbrev eqCode : V₀ → V₀ → F V₀ := fun a k => F.ret (.bool (decide (a = k)))

/-- The constant-false family: a legitimate realizer of `Π n. ‖Bool‖`. -/
abbrev famFalse : V₀ → F V₀ := fun _ => F.ret (.bool false)

/-- The generic cell, freshly allocated. -/
abbrev cell₀ : Cell V₀ := ⟨eqCode, famFalse, []⟩

/-- The base condition: the generic cell allocated, nothing committed. -/
def h₀ : Heap V₀ := [cell₀]

/-! ## The firewall invariant

`Protected h`: the generic cell exists, still owns the constant-false family,
and every value ever committed in it is `false`. Since clients can only reach
the cell through `memo`, and a miss commits the *cell's own* family's output,
this is preserved by every program run — the memo-discipline lemma. -/

/-- The cell at `0` has the constant-false family and only `false` values. -/
def Protected (h : Heap V₀) : Prop :=
  ∃ cell, h[0]? = some cell ∧ cell.fam = famFalse ∧
    ∀ p ∈ cell.cache, p.2 = V₀.bool false

theorem protected_h₀ : Protected h₀ :=
  ⟨cell₀, rfl, rfl, fun _ hp => absurd hp (List.not_mem_nil)⟩

theorem Protected.commit_ne {h : Heap V₀} (hP : Protected h) {ℓ : Loc} {a b : V₀}
    (hℓ : ℓ ≠ 0) : Protected (h.commit ℓ a b) := by
  obtain ⟨c₀, hc₀, hfam, hvals⟩ := hP
  refine ⟨c₀, ?_, hfam, hvals⟩
  rw [Heap.commit, Heap.getElem?_updateCell_ne _ _ (Ne.symm hℓ)]
  exact hc₀

theorem Protected.commit_zero {h : Heap V₀} (hP : Protected h) {a : V₀} :
    Protected (h.commit 0 a (V₀.bool false)) := by
  obtain ⟨c₀, hc₀, hfam, hvals⟩ := hP
  refine ⟨{ c₀ with cache := (a, V₀.bool false) :: c₀.cache }, ?_, hfam, ?_⟩
  · rw [Heap.commit, Heap.getElem?_updateCell_self, hc₀]
    rfl
  · intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · rw [hp]
    · exact hvals p hp

theorem Protected.alloc {h : Heap V₀} (hP : Protected h) {eqr : V₀ → V₀ → F V₀}
    {fam : V₀ → F V₀} : Protected (h.alloc eqr fam) := by
  obtain ⟨c₀, hc₀, hfam, hvals⟩ := hP
  have hlt : 0 < h.length := by
    rcases Nat.lt_or_ge 0 h.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at hc₀
      cases hc₀
  refine ⟨c₀, ?_, hfam, hvals⟩
  rw [Heap.alloc, List.getElem?_append_left hlt]
  exact hc₀

/-! ## The memo-discipline lemma

By induction on fuel: every program run preserves `Protected`. The only heap
writes `run` performs are `alloc` (a fresh cell beyond `0`) and the memo-miss
commit, whose value at cell `0` is an output of the cell's *own* family —
`famFalse` — hence `false`. -/

/-- Scan preserves `Protected`, given that runs at the scan's fuel do. -/
theorem protected_scan {n : ℕ}
    (ihrun : ∀ (e : F V₀) (h : Heap V₀) (s : Step V₀ h),
      Protected h → run isTrue₀ n e h = some s → Protected s.next) :
    ∀ (entries : List (V₀ × V₀)) (eqr : V₀ → V₀ → F V₀) (a : V₀) (h : Heap V₀)
      (s : Step (Option V₀) h),
      Protected h → scan isTrue₀ n eqr a entries h = some s → Protected s.next := by
  intro entries
  induction entries with
  | nil =>
    intro eqr a h s hP hs
    rw [scan_nil] at hs
    obtain ⟨hnext, -⟩ := PT.pure_eq_some hs
    rw [hnext]
    exact hP
  | cons e rest ih =>
    obtain ⟨key, val⟩ := e
    intro eqr a h s hP hs
    rw [scan_cons] at hs
    obtain ⟨s₁, hm, s₂, hf, hnext, -⟩ := PT.bind_eq_some hs
    have hP₁ : Protected s₁.next := ihrun _ _ _ hP hm
    by_cases ht : isTrue₀ s₁.val
    · rw [if_pos ht] at hf
      obtain ⟨hn₂, -⟩ := PT.pure_eq_some hf
      rw [hnext, hn₂]
      exact hP₁
    · rw [if_neg ht] at hf
      have := ih eqr a s₁.next s₂ hP₁ hf
      rw [hnext]
      exact this

/-- **Memo-discipline**: every run preserves `Protected`. -/
theorem protected_run :
    ∀ (fuel : ℕ) (e : F V₀) (h : Heap V₀) (s : Step V₀ h),
      Protected h → run isTrue₀ fuel e h = some s → Protected s.next := by
  intro fuel
  induction fuel with
  | zero =>
    intro e h s hP hs
    rw [run_zero] at hs
    cases hs
  | succ n ihn =>
    intro e h s hP hs
    cases e with
    | ret v =>
      obtain ⟨hnext, -⟩ := run_ret_inv hs
      rw [hnext]
      exact hP
    | memo ℓ a k =>
      simp only [run_memo] at hs
      rcases hcell : h[ℓ]? with _ | cell
      · rw [hcell] at hs
        simp at hs
      · rw [hcell] at hs
        obtain ⟨s₁, hm, s₂, hf, hnext, -⟩ := PT.bind_eq_some hs
        have hP₁ : Protected s₁.next := protected_scan ihn _ _ _ _ _ hP hm
        rcases hhit : s₁.val with _ | b
        · -- miss: run the cell's family, commit, continue
          rw [hhit] at hf
          obtain ⟨t₁, hm₁, t₂, hf₂, hnext₂, -⟩ := PT.bind_eq_some hf
          obtain ⟨u₁, hu₁, u₂, hu₂, hun, -⟩ := PT.bind_eq_some hm₁
          have hPu : Protected u₁.next := ihn _ _ _ hP₁ hu₁
          obtain ⟨hu₂n, -⟩ := commitPT_eq_some hu₂
          have hPt : Protected t₁.next := by
            rw [hun, hu₂n]
            by_cases hℓ : ℓ = 0
            · -- the committed value is the constant-false family's output
              subst hℓ
              obtain ⟨c₀, hc₀, hfam, -⟩ := hP
              obtain rfl : cell = c₀ := by
                rw [hcell] at hc₀
                exact Option.some.inj hc₀
              rw [hfam] at hu₁
              obtain ⟨-, huval⟩ := run_ret_inv hu₁
              rw [huval]
              exact hPu.commit_zero
            · exact hPu.commit_ne hℓ
          have := ihn _ _ _ hPt hf₂
          rw [hnext, hnext₂]
          exact this
        · -- hit: continue with the stored value
          rw [hhit] at hf
          have := ihn _ _ _ hP₁ hf
          rw [hnext]
          exact this
    | alloc eqr fam k =>
      rw [run_alloc] at hs
      obtain ⟨s₁, hm, s₂, hf, hnext, -⟩ := PT.bind_eq_some hs
      obtain ⟨hn₁, -⟩ := allocPT_eq_some hm
      have hP₁ : Protected s₁.next := by
        rw [hn₁]
        exact hP.alloc
      have := ihn _ _ _ hP₁ hf
      rw [hnext]
      exact this

/-- Under `Protected`, the memoizer can only ever answer `false`: a hit
returns a cached value (all `false`), a miss commits the constant-false
family's output. This is horn `inl`'s engine. -/
theorem memoizer_val_false {fuel n : ℕ} {h : Heap V₀} {s : Step V₀ h}
    (hP : Protected h)
    (hr : run isTrue₀ fuel (memoizer 0 (.nat n)) h = some s) :
    s.val = V₀.bool false := by
  cases fuel with
  | zero =>
    rw [memoizer, run_zero] at hr
    cases hr
  | succ m =>
    obtain ⟨c₀, hc₀, hfam, hvals⟩ := hP
    simp only [memoizer, run_memo] at hr
    rw [hc₀] at hr
    obtain ⟨s₁, hm, s₂, hf, -, hval⟩ := PT.bind_eq_some hr
    rcases hhit : s₁.val with _ | b
    · -- miss
      rw [hhit] at hf
      obtain ⟨t₁, hm₁, t₂, hf₂, -, hval₂⟩ := PT.bind_eq_some hf
      obtain ⟨u₁, hu₁, u₂, hu₂, -, huv⟩ := PT.bind_eq_some hm₁
      rw [hfam] at hu₁
      obtain ⟨-, huval⟩ := run_ret_inv hu₁
      obtain ⟨-, hu₂v⟩ := commitPT_eq_some hu₂
      obtain ⟨-, ht₂v⟩ := run_ret_inv hf₂
      rw [hval, hval₂, ht₂v, huv, hu₂v, huval]
    · -- hit: the stored value is `false` by `Protected`
      rw [hhit] at hf
      obtain ⟨-, hsv⟩ := run_ret_inv hf
      obtain ⟨kk, hmem⟩ := scan_val_mem hm hhit
      rw [hval, hsv]
      exact hvals _ hmem

/-! ## The forcing clauses

Propositions in this fragment are realizer-irrelevant, so realizability is
plain forcing. `φ := ∃ n, s n = true` is forced when some `s n` *evaluates* to
`true`; negation is the Kripke clause over all heap extensions. -/

/-- `s n = true` is forced at `h`: evaluating the memoizer at key `n` from `h`
yields `true`. -/
def EvalsTrue (h : Heap V₀) (n : ℕ) : Prop :=
  ∃ (fuel : ℕ) (s : Step V₀ h),
    run isTrue₀ fuel (memoizer 0 (.nat n)) h = some s ∧ s.val = .bool true

/-- `φ := ∃ n, s n = true` is forced at `h`. -/
def ForcesPhi (h : Heap V₀) : Prop := ∃ n, EvalsTrue h n

/-- `¬φ` is forced at `h`: no extension forces `φ`. -/
def ForcesNegPhi (h : Heap V₀) : Prop := ∀ h', h ≤ h' → ¬ ForcesPhi h'

/-- The firewall, logically: a protected heap never forces `φ`. -/
theorem Protected.not_forcesPhi {h : Heap V₀} (hP : Protected h) : ¬ ForcesPhi h := by
  rintro ⟨n, fuel, s, hr, hv⟩
  have := memoizer_val_false hP hr
  rw [this] at hv
  simp at hv

/-! ## The genericity horn

At any extension `h'` of `h₀`, committing `(0 ↦ true)` at the head of the
cell's cache is a legitimate heap (a *typed possibilium* — unreachable by
running the constant-false family, but conditions are possibilia, not
execution states), and at it `s 0` cache-hits `true`. So no extension of `h₀`
forces `¬φ`. -/

/-- After committing `(nat 0 ↦ true)`, the memoizer at key `0` evaluates to
`true`: the fresh entry sits at the head of the cache, and the scan checks the
newest entry first. -/
theorem evalsTrue_commit {h' : Heap V₀} {c' : Cell V₀} (hc' : h'[0]? = some c')
    (heq : eqCode = c'.eqr) :
    EvalsTrue (h'.commit 0 (.nat 0) (.bool true)) 0 := by
  have hc'' : (h'.commit 0 (.nat 0) (.bool true))[0]? =
      some ⟨c'.eqr, c'.fam, (V₀.nat 0, V₀.bool true) :: c'.cache⟩ := by
    rw [Heap.commit, Heap.getElem?_updateCell_self, hc']
    rfl
  refine ⟨2, ⟨_, le_refl _, .bool true⟩, ?_, rfl⟩
  simp [memoizer, run_memo, hc'', scan_cons, ← heq, eqCode, isTrue₀,
    run_ret, PT.bind, PT.pure]

/-- No extension of the base condition forces `¬φ`. -/
theorem not_forcesNegPhi {h' : Heap V₀} (hle : h₀ ≤ h') : ¬ ForcesNegPhi h' := by
  intro hneg
  obtain ⟨c', hc', hcle⟩ := hle 0 cell₀ rfl
  have heq : eqCode = c'.eqr := hcle.1
  exact hneg _ (Heap.le_commit h' 0 (.nat 0) (.bool true)) ⟨0, evalsTrue_commit hc' heq⟩

/-! ## The theorems -/

/-- `¬¬φ` is forced at the base condition. -/
theorem notNot_phi_forced : ∀ h', h₀ ≤ h' → ¬ ForcesNegPhi h' :=
  fun _ => not_forcesNegPhi

/-- **EM is not realized**: no program decides `φ ∨ ¬φ` at the base condition.
The two horns are exactly the firewall (`inl`: programs cannot put `true` in)
and the genericity (`inr`: the semantics can imagine `true` in). -/
theorem em_not_realized :
    ¬ ∃ (e : F V₀) (fuel : ℕ) (s : Step V₀ h₀),
        run isTrue₀ fuel e h₀ = some s ∧
        (if isTrue₀ s.val then ForcesPhi s.next else ForcesNegPhi s.next) := by
  rintro ⟨e, fuel, s, hr, hd⟩
  have hP : Protected s.next := protected_run fuel e h₀ s protected_h₀ hr
  by_cases ht : isTrue₀ s.val
  · rw [if_pos ht] at hd
    exact hP.not_forcesPhi hd
  · rw [if_neg ht] at hd
    exact not_forcesNegPhi s.le hd

/-- **Non-Booleanness**: `¬¬φ → φ` is not realized either. Since `¬¬φ` is
forced everywhere above `h₀`, a realizer would have to force `φ` from `h₀`
itself — which the firewall forbids. This is strictly stronger than
`em_not_realized`. -/
theorem dne_not_realized :
    ¬ ∃ e : F V₀, ∀ h', h₀ ≤ h' →
        (∀ h'', h' ≤ h'' → ¬ ForcesNegPhi h'') →
        ∃ (fuel : ℕ) (s : Step V₀ h'),
          run isTrue₀ fuel e h' = some s ∧ ForcesPhi s.next := by
  rintro ⟨e, he⟩
  obtain ⟨fuel, s, hr, hphi⟩ := he h₀ (le_refl h₀) (fun _ hle => not_forcesNegPhi hle)
  have hP : Protected s.next := protected_run fuel e h₀ s protected_h₀ hr
  exact hP.not_forcesPhi hphi

/-! ## Single-valued conditions and the Kripke algebra

The theorems above are realizer-level statements over raw heaps. The raw heap
order is *not* a forcing order: an extension may prepend an entry whose key
already occurs, and the newest-first scan then shadows the old value, so
`ForcesPhi` is not monotone. To say anything topos-shaped, conditions must be
**single-valued** — finite partial *functions*, pairwise-distinct keys — which
is exactly the semantic-conditions discipline of `THEORY.md` §2, specialized to
code-equality routing.

Over the poset `Cond` of single-valued conditions above `h₀`, monotone
propositions form the standard Kripke algebra — the algebra of truth values of
the *presheaf* topos over `Cond`. Below: `φ` is persistent there, `¬φ = ⊥`
(density: every condition has a valid extension forcing `φ`, now at a *fresh*
key), hence `¬¬φ = ⊤`, while `φ ≠ ⊤`. So that algebra is **non-Boolean**,
witnessed by the operationally-defined `φ`. The identification with `Psh(Cond)`
and the sheaf topos for the decision coverage remain on paper (K3). -/

/-- The generic cell's cache has pairwise-distinct keys: the condition is a
finite partial function, not a multimap. -/
def KeysDistinct (h : Heap V₀) : Prop :=
  ∀ cell, h[0]? = some cell → cell.cache.Pairwise fun p q => p.1 ≠ q.1

/-- The condition poset: single-valued heaps above the base condition. -/
def Cond : Type := {h : Heap V₀ // h₀ ≤ h ∧ KeysDistinct h}

instance : PartialOrder Cond := Subtype.partialOrder _

/-- The base condition as an element of `Cond`. -/
def base : Cond :=
  ⟨h₀, le_refl h₀, fun cell hc => by
    obtain rfl := Option.some.inj hc
    exact List.Pairwise.nil⟩

@[simp] theorem isTrue₀_bool (b : Bool) : isTrue₀ (.bool b) = b := by
  cases b <;> rfl

/-- Under code-equality routing, a scan hit is on the queried key itself. -/
theorem scan_eqCode_val {fuel : ℕ} {a : V₀} {entries : List (V₀ × V₀)} :
    ∀ {h : Heap V₀} {s : Step (Option V₀) h} {b : V₀},
      scan isTrue₀ fuel eqCode a entries h = some s → s.val = some b →
      (a, b) ∈ entries := by
  induction entries with
  | nil =>
    intro h s b hs hv
    rw [scan_nil] at hs
    obtain ⟨-, hval⟩ := PT.pure_eq_some hs
    rw [hval] at hv
    cases hv
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    intro h s b hs hv
    rw [scan_cons] at hs
    obtain ⟨s₁, hm, s₂, hf, -, hval⟩ := PT.bind_eq_some hs
    obtain ⟨-, hv₁⟩ := run_ret_inv hm
    rcases hd : decide (a = k) with - | -
    · rw [if_neg (by rw [hv₁, isTrue₀_bool, hd]; exact Bool.false_ne_true)] at hf
      have : s₂.val = some b := by rw [← hval, hv]
      exact List.mem_cons_of_mem _ (ih hf this)
    · rw [if_pos (by rw [hv₁, isTrue₀_bool, hd])] at hf
      obtain ⟨-, hv₂⟩ := PT.pure_eq_some hf
      obtain rfl : a = k := of_decide_eq_true hd
      have : some v = some b := by rw [← hv₂, ← hval, hv]
      obtain rfl := Option.some.inj this
      exact List.mem_cons_self ..

/-- Scanning skips a prefix none of whose keys is the queried one. -/
theorem scan_skip {fuel : ℕ} {a : V₀} {rest : List (V₀ × V₀)} :
    ∀ {l₁ : List (V₀ × V₀)}, (∀ p ∈ l₁, p.1 ≠ a) →
      scan isTrue₀ (fuel + 1) eqCode a (l₁ ++ rest) =
        scan isTrue₀ (fuel + 1) eqCode a rest := by
  intro l₁
  induction l₁ with
  | nil => intro _; rfl
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    intro hno
    rw [List.cons_append, scan_cons,
      show eqCode a k = F.ret (.bool (decide (a = k))) from rfl, run_ret, PT.pure_bind]
    have hk : decide (a = k) = false :=
      decide_eq_false fun hh => hno (k, v) (List.mem_cons_self ..) hh.symm
    rw [if_neg (by rw [isTrue₀_bool, hk]; exact Bool.false_ne_true)]
    exact ih fun p hp => hno p (List.mem_cons_of_mem _ hp)

/-- Scanning hits a head entry stored at the queried key. -/
theorem scan_hit_head {fuel : ℕ} {a b : V₀} {rest : List (V₀ × V₀)} :
    scan isTrue₀ (fuel + 1) eqCode a ((a, b) :: rest) = PT.pure (some b) := by
  rw [scan_cons, show eqCode a a = F.ret (.bool (decide (a = a))) from rfl, run_ret,
    PT.pure_bind, if_pos (by rw [isTrue₀_bool]; simp)]

/-- A `true` answer of the memoizer comes from a cache entry at the queried
key: misses commit the constant-false family's output. -/
theorem evalsTrue_entry {h : Heap V₀} {n : ℕ} (hle : h₀ ≤ h) (he : EvalsTrue h n) :
    ∃ cell, h[0]? = some cell ∧ (V₀.nat n, V₀.bool true) ∈ cell.cache := by
  obtain ⟨cell, hcell, hLe⟩ := hle 0 cell₀ rfl
  have heqr : eqCode = cell.eqr := hLe.1
  have hfam : famFalse = cell.fam := hLe.2.1
  obtain ⟨fuel, s, hr, hv⟩ := he
  cases fuel with
  | zero => rw [memoizer, run_zero] at hr; cases hr
  | succ m =>
    simp only [memoizer, run_memo] at hr
    rw [hcell] at hr
    obtain ⟨s₁, hm, s₂, hf, -, hval⟩ := PT.bind_eq_some hr
    rcases hhit : s₁.val with - | b
    · -- a miss returns the constant-false family's output, not `true`
      rw [hhit] at hf
      obtain ⟨t₁, hm₁, t₂, hf₂, -, hval₂⟩ := PT.bind_eq_some hf
      obtain ⟨u₁, hu₁, u₂, hu₂, -, huv⟩ := PT.bind_eq_some hm₁
      rw [← hfam] at hu₁
      obtain ⟨-, huval⟩ := run_ret_inv hu₁
      obtain ⟨-, hu₂v⟩ := commitPT_eq_some hu₂
      obtain ⟨-, ht₂v⟩ := run_ret_inv hf₂
      rw [hval, hval₂, ht₂v, huv, hu₂v, huval] at hv
      cases hv
    · -- a hit at key `nat n` with value `true`
      rw [hhit] at hf
      obtain ⟨-, hsv⟩ := run_ret_inv hf
      rw [← heqr] at hm
      have hb : b = V₀.bool true := by
        rw [← hsv, ← hval]; exact hv
      rw [hb] at hhit
      exact ⟨cell, hcell, scan_eqCode_val hm hhit⟩

/-- Conversely, on a single-valued condition a cached `(nat n ↦ true)` entry
makes the memoizer answer `true`: distinctness lets the scan skip everything
before the entry. -/
theorem evalsTrue_of_entry {h : Heap V₀} {n : ℕ} {cell : Cell V₀}
    (hcell : h[0]? = some cell) (heqr : eqCode = cell.eqr) (hkd : KeysDistinct h)
    (hmem : (V₀.nat n, V₀.bool true) ∈ cell.cache) : EvalsTrue h n := by
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hmem
  have hno : ∀ p ∈ l₁, p.1 ≠ V₀.nat n := by
    intro p hp
    have hpw := hkd _ hcell
    rw [hsplit] at hpw
    exact (List.pairwise_append.mp hpw).2.2 p hp _ (List.mem_cons_self ..)
  refine ⟨2, ⟨h, le_refl h, .bool true⟩, ?_, rfl⟩
  simp only [memoizer, run_memo, hcell]
  rw [← heqr, hsplit, scan_skip hno, scan_hit_head, PT.pure_bind]
  simp [run_ret]

/-! ### Persistence: `φ` is monotone over single-valued conditions -/

theorem forcesPhi_persists {c c' : Cond} (hle : c ≤ c') (hphi : ForcesPhi c.1) :
    ForcesPhi c'.1 := by
  obtain ⟨n, hn⟩ := hphi
  obtain ⟨cell, hcell, hmem⟩ := evalsTrue_entry c.2.1 hn
  obtain ⟨cell', hcell', hLe⟩ := hle 0 cell hcell
  have heqr' : eqCode = cell'.eqr := by
    obtain ⟨c₀cell, hc₀, hLe₀⟩ := c'.2.1 0 cell₀ rfl
    obtain rfl := Option.some.inj (hc₀.symm.trans hcell')
    exact hLe₀.1
  obtain ⟨p, hp⟩ := hLe.2.2
  refine ⟨n, evalsTrue_of_entry hcell' heqr' c'.2.2 ?_⟩
  rw [hp]
  exact List.mem_append_right p hmem

/-! ### Density: every condition has a valid extension forcing `φ` -/

/-- Decode a key to a numeral (defaulting non-numerals to `0`). -/
def keyNat : V₀ × V₀ → ℕ
  | (.nat j, _) => j
  | _ => 0

/-- A numeral key occurring nowhere in the cache. -/
def freshKey (l : List (V₀ × V₀)) : ℕ := (l.map keyNat).foldr max 0 + 1

theorem le_foldr_max {x : ℕ} : ∀ {l : List ℕ}, x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro hx; cases hx
  | cons a t ih =>
    intro hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx
      omega

theorem freshKey_not_mem {l : List (V₀ × V₀)} : ∀ p ∈ l, p.1 ≠ V₀.nat (freshKey l) := by
  rintro ⟨k, v⟩ hp hkey
  have hkey' : k = V₀.nat (freshKey l) := hkey
  subst hkey'
  have h2 : keyNat (V₀.nat (freshKey l), v) ≤ (l.map keyNat).foldr max 0 :=
    le_foldr_max (List.mem_map_of_mem hp)
  simp only [keyNat, freshKey] at h2
  omega

/-- **Density**: above any single-valued condition there is a single-valued
condition forcing `φ` — commit `true` at a fresh key. -/
theorem kPhi_dense (c : Cond) : ∃ c', c ≤ c' ∧ ForcesPhi c'.1 := by
  obtain ⟨cell, hcell, hLe⟩ := c.2.1 0 cell₀ rfl
  have heqr : eqCode = cell.eqr := hLe.1
  set m := freshKey cell.cache with hm
  set h'' := c.1.commit 0 (.nat m) (.bool true) with hh
  have hcell'' : h''[0]? = some ⟨cell.eqr, cell.fam, (V₀.nat m, V₀.bool true) :: cell.cache⟩ := by
    rw [hh, Heap.commit, Heap.getElem?_updateCell_self, hcell]
    rfl
  have hkd'' : KeysDistinct h'' := by
    intro cl hcl
    obtain rfl := Option.some.inj (hcell''.symm.trans hcl)
    refine List.pairwise_cons.mpr ⟨?_, c.2.2 _ hcell⟩
    intro q hq hqkey
    exact freshKey_not_mem q hq (by rw [← hqkey])
  refine ⟨⟨h'', le_trans c.2.1 (Heap.le_commit c.1 0 (.nat m) (.bool true)), hkd''⟩,
    Heap.le_commit c.1 0 (.nat m) (.bool true),
    ⟨m, evalsTrue_of_entry hcell'' heqr hkd'' (List.mem_cons_self ..)⟩⟩

/-! ### The Kripke algebra and the non-Booleanness witness -/

/-- A Kripke proposition: a monotone predicate on single-valued conditions.
These form the algebra of truth values of the presheaf topos over `Cond`. -/
@[ext] structure KProp where
  /-- where the proposition is forced -/
  holds : Cond → Prop
  /-- persistence -/
  mono : ∀ {c c'}, c ≤ c' → holds c → holds c'

/-- The true proposition. -/
def kTop : KProp := ⟨fun _ => True, fun _ _ => trivial⟩

/-- The false proposition. -/
def kBot : KProp := ⟨fun _ => False, fun _ h => h⟩

/-- Kripke negation — the Heyting negation of this algebra. -/
def kNot (p : KProp) : KProp :=
  ⟨fun c => ∀ c', c ≤ c' → ¬ p.holds c',
   fun hcc' hn _ hc'' => hn _ (le_trans hcc' hc'')⟩

/-- `φ := ∃ n, s n = true` as a Kripke proposition: persistent by
single-valuedness. -/
def kPhi : KProp := ⟨fun c => ForcesPhi c.1, forcesPhi_persists⟩

/-- `¬φ = ⊥`: `φ` is dense. -/
theorem kNot_kPhi_eq_bot : kNot kPhi = kBot := by
  ext c
  simp only [kNot, kBot, kPhi, iff_false]
  intro hn
  obtain ⟨c', hle, hphi⟩ := kPhi_dense c
  exact hn c' hle hphi

/-- `¬¬φ = ⊤`. -/
theorem kNotNot_kPhi_eq_top : kNot (kNot kPhi) = kTop := by
  ext c
  simp only [kNot, kPhi, kTop, iff_true]
  intro c' _ hnot
  obtain ⟨c'', hle'', hphi⟩ := kPhi_dense c'
  exact hnot c'' hle'' hphi

/-- `φ ≠ ⊤`: nothing forces `φ` at the base condition (the firewall). -/
theorem kPhi_ne_top : kPhi ≠ kTop := by
  intro h
  have hb : kPhi.holds base := by rw [h]; trivial
  exact protected_h₀.not_forcesPhi hb

/-- **The Kripke algebra over single-valued conditions is non-Boolean**:
the operational `φ` is double-negation dense but not true. -/
theorem kripke_not_boolean : ∃ p : KProp, kNot (kNot p) = kTop ∧ p ≠ kTop :=
  ⟨kPhi, kNotNot_kPhi_eq_top, kPhi_ne_top⟩

end LeanStatefulAoc
