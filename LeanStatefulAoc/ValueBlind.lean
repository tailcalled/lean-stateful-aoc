import LeanStatefulAoc.Computation
import LeanStatefulAoc.NonBoolean

/-!
# Value-blindness as a logical relation (the ∀A closure, framework)

The remaining firewall gap is *all-programs* value-blindness: every code-opaque
program reveals no more about the stored representatives than the eq-realizer and
the family already expose. `Firewall.dia_eval`/`dia_value_blind` settle this for
the canonical Diaconescu attack; here we set up the general statement as a binary
**logical relation** `RelF R` between programs (and `RelHeap R` between heaps),
parametrized by a relation `R` on codes.

`RelF R e e'` holds when `e`, `e'` are "the same up to `R`-relabeling of the codes
they pass around" — the `memo`/`alloc` continuations must send `R`-related inputs
to `RelF`-related outputs, which is exactly *not branching on a code's identity*.
The **fundamental lemma** (`rel_run`) — that `RelF`-related programs on
`RelHeap`-related heaps produce `R`-related results — is value-blindness: with
`R` a code-bijection that fixes booleans, a program's boolean output is then
forced to be `R`-invariant, i.e. independent of the representative codes.

The eq-verdicts agree across the two runs *for free*: the cells' eq-realizers are
themselves `RelF`-related, so running them on `R`-related keys yields `R`-related
verdict codes (the fundamental lemma, recursively), and `RTrue R` makes their
`isTrue₀` decode agree. No separate equality-compatibility hypothesis is needed.
-/

namespace LeanStatefulAoc

namespace VB

/-- Two programs are `R`-related: same control structure, codes `R`-related, and
every continuation sends `R`-related inputs to `R`-related outputs (so it never
inspects a code's identity). -/
inductive RelF (R : V₀ → V₀ → Prop) : F V₀ → F V₀ → Prop
  | ret {v v'} : R v v' → RelF R (.ret v) (.ret v')
  | memo {ℓ a a' k k'} : R a a' → (∀ r r', R r r' → RelF R (k r) (k' r')) →
      RelF R (.memo ℓ a k) (.memo ℓ a' k')
  | alloc {eqr eqr' fam fam' kont kont'} :
      (∀ a a' b b', R a a' → R b b' → RelF R (eqr a b) (eqr' a' b')) →
      (∀ a a', R a a' → RelF R (fam a) (fam' a')) →
      (∀ ℓ, RelF R (kont ℓ) (kont' ℓ)) →
      RelF R (.alloc eqr fam kont) (.alloc eqr' fam' kont')

/-- Two cells are `R`-related: `R`-related eq-realizers, `R`-related families, and
`R`-related caches (entrywise on keys and values). -/
def RelCell (R : V₀ → V₀ → Prop) (c c' : Cell V₀) : Prop :=
  (∀ a a' b b', R a a' → R b b' → RelF R (c.eqr a b) (c'.eqr a' b')) ∧
  (∀ a a', R a a' → RelF R (c.fam a) (c'.fam a')) ∧
  c.cache.Forall₂ (fun p p' => R p.1 p'.1 ∧ R p.2 p'.2) c'.cache

/-- Two heaps are `R`-related: same length, corresponding cells `R`-related. -/
def RelHeap (R : V₀ → V₀ → Prop) (h h' : Heap V₀) : Prop :=
  h.length = h'.length ∧
    ∀ (ℓ : Loc) (c c' : Cell V₀), h[ℓ]? = some c → h'[ℓ]? = some c' → RelCell R c c'

/-- `R` respects the truth-decoder: `R`-related verdict codes decode equally. -/
def RTrue (R : V₀ → V₀ → Prop) : Prop := ∀ v v', R v v' → isTrue₀ v = isTrue₀ v'

/-- Two optional steps are related: both fail, or both succeed with values
related by `S` and `RelHeap`-related resulting heaps. -/
def RelOptR (R : V₀ → V₀ → Prop) {X : Type} (S : X → X → Prop) {h h' : Heap V₀}
    (o : Option (Step X h)) (o' : Option (Step X h')) : Prop :=
  (o = none ∧ o' = none) ∨
    ∃ s s', o = some s ∧ o' = some s' ∧ S s.val s'.val ∧ RelHeap R s.next s'.next

/-- The value relation for `scan`'s `Option V₀` result. -/
def OptRel (R : V₀ → V₀ → Prop) (o o' : Option V₀) : Prop :=
  (o = none ∧ o' = none) ∨ ∃ b b', o = some b ∧ o' = some b' ∧ R b b'

/-- Heaps of equal length are simultaneously defined or undefined at each `ℓ`. -/
theorem getElem?_len {h h' : Heap V₀} (hlen : h.length = h'.length) (ℓ : Loc) :
    (h[ℓ]?.isSome) = (h'[ℓ]?.isSome) := by
  by_cases hℓ : ℓ < h.length
  · rw [List.getElem?_eq_getElem hℓ, List.getElem?_eq_getElem (hlen ▸ hℓ)]; rfl
  · have hge : h.length ≤ ℓ := Nat.le_of_not_lt hℓ
    rw [List.getElem?_eq_none hge, List.getElem?_eq_none (hlen ▸ hge)]

/-- Sequencing preserves relatedness. -/
theorem relOptR_bind {R : V₀ → V₀ → Prop} {X Y : Type} {S : X → X → Prop}
    {T : Y → Y → Prop} {m m' : PT (Heap V₀) X} {f f' : X → PT (Heap V₀) Y}
    {h h' : Heap V₀} (hm : RelOptR R S (m h) (m' h'))
    (hf : ∀ x x' (g g' : Heap V₀), S x x' → RelHeap R g g' →
      RelOptR R T (f x g) (f' x' g')) :
    RelOptR R T (PT.bind m f h) (PT.bind m' f' h') := by
  rcases hm with ⟨h1, h2⟩ | ⟨s, s', h1, h2, hval, hheap⟩
  · exact Or.inl ⟨by simp [PT.bind, h1], by simp [PT.bind, h2]⟩
  · rcases hf s.val s'.val s.next s'.next hval hheap with ⟨g1, g2⟩ | ⟨t, t', g1, g2, tval, theap⟩
    · exact Or.inl ⟨by simp [PT.bind, h1, g1], by simp [PT.bind, h2, g2]⟩
    · exact Or.inr ⟨⟨t.next, le_trans s.le t.le, t.val⟩, ⟨t'.next, le_trans s'.le t'.le, t'.val⟩,
        by simp [PT.bind, h1, g1], by simp [PT.bind, h2, g2], tval, theap⟩

/-- `pure` preserves relatedness. -/
theorem relOptR_pure {R : V₀ → V₀ → Prop} {X : Type} {S : X → X → Prop} {x x' : X}
    {h h' : Heap V₀} (hx : S x x') (hh : RelHeap R h h') :
    RelOptR R S (PT.pure x h) (PT.pure x' h') :=
  Or.inr ⟨_, _, rfl, rfl, hx, hh⟩

theorem length_updateCell : ∀ (h : Heap V₀) (ℓ : Loc) (f : Cell V₀ → Cell V₀),
    (Heap.updateCell h ℓ f).length = h.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | c :: t, ℓ + 1, f => by simp [Heap.updateCell, length_updateCell t ℓ f]

/-- Committing `R`-related entries preserves `RelHeap`. -/
theorem relHeap_commit {R : V₀ → V₀ → Prop} {h h' : Heap V₀} (hh : RelHeap R h h')
    {ℓ : Loc} {a a' b b' : V₀} (ha : R a a') (hb : R b b') :
    RelHeap R (h.commit ℓ a b) (h'.commit ℓ a' b') := by
  refine ⟨by simp only [Heap.commit, length_updateCell, hh.1], ?_⟩
  intro ℓ' c c' hc hc'
  by_cases hℓ : ℓ' = ℓ
  · subst hℓ
    rw [Heap.commit, Heap.getElem?_updateCell_self] at hc hc'
    rcases hc0 : h[ℓ']? with _ | c₀ <;> rw [hc0] at hc <;>
      simp only [Option.map_none, Option.map_some] at hc
    · exact absurd hc (by simp)
    rcases hc0' : h'[ℓ']? with _ | c₀' <;> rw [hc0'] at hc' <;>
      simp only [Option.map_none, Option.map_some] at hc'
    · exact absurd hc' (by simp)
    obtain rfl := (Option.some.inj hc).symm
    obtain rfl := (Option.some.inj hc').symm
    obtain ⟨heqr, hfam, hcache⟩ := hh.2 ℓ' c₀ c₀' hc0 hc0'
    exact ⟨heqr, hfam, List.Forall₂.cons ⟨ha, hb⟩ hcache⟩
  · rw [Heap.commit, Heap.getElem?_updateCell_ne _ _ hℓ] at hc
    rw [Heap.commit, Heap.getElem?_updateCell_ne _ _ hℓ] at hc'
    exact hh.2 ℓ' c c' hc hc'

/-- Allocating `R`-related cells preserves `RelHeap`. -/
theorem relHeap_alloc {R : V₀ → V₀ → Prop} {h h' : Heap V₀} (hh : RelHeap R h h')
    {eqr eqr' : V₀ → V₀ → F V₀} {fam fam' : V₀ → F V₀}
    (heq : ∀ a a' b b', R a a' → R b b' → RelF R (eqr a b) (eqr' a' b'))
    (hfam : ∀ a a', R a a' → RelF R (fam a) (fam' a')) :
    RelHeap R (h.alloc eqr fam) (h'.alloc eqr' fam') := by
  refine ⟨by simp [Heap.alloc, hh.1], ?_⟩
  intro ℓ c c' hc hc'
  by_cases hℓ : ℓ < h.length
  · rw [Heap.alloc, List.getElem?_append_left hℓ] at hc
    rw [Heap.alloc, List.getElem?_append_left (hh.1 ▸ hℓ)] at hc'
    exact hh.2 ℓ c c' hc hc'
  · have hlen : (h.alloc eqr fam).length = h.length + 1 := by
      simp [Heap.alloc]
    have hlt : ℓ < h.length + 1 := by
      rcases Nat.lt_or_ge ℓ (h.length + 1) with h1 | h1
      · exact h1
      · exfalso
        have hnone : (h.alloc eqr fam)[ℓ]? = none :=
          List.getElem?_eq_none (by rw [hlen]; exact h1)
        rw [hnone] at hc; exact absurd hc (by simp)
    have hℓe : ℓ = h.length :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) (Nat.le_of_not_lt hℓ)
    subst hℓe
    have e1 : (h.alloc eqr fam)[h.length]? = some ⟨eqr, fam, []⟩ := by
      rw [Heap.alloc]; exact List.getElem?_concat_length ..
    have e2 : (h'.alloc eqr' fam')[h.length]? = some ⟨eqr', fam', []⟩ := by
      rw [Heap.alloc, hh.1]; exact List.getElem?_concat_length ..
    rw [e1] at hc; rw [e2] at hc'
    obtain rfl := (Option.some.inj hc).symm
    obtain rfl := (Option.some.inj hc').symm
    exact ⟨heq, hfam, List.Forall₂.nil⟩

/-- `commitPT` of `R`-related entries is `R`-related. -/
theorem relOptR_commitPT {R : V₀ → V₀ → Prop} {h h' : Heap V₀} (hh : RelHeap R h h')
    {ℓ : Loc} {a a' b b' : V₀} (ha : R a a') (hb : R b b') :
    RelOptR R R (commitPT ℓ a b h) (commitPT ℓ a' b' h') :=
  Or.inr ⟨_, _, rfl, rfl, hb, relHeap_commit hh ha hb⟩

/-- `allocPT` of `R`-related cells is related, with equal fresh locations. -/
theorem relOptR_allocPT {R : V₀ → V₀ → Prop} {h h' : Heap V₀} (hh : RelHeap R h h')
    {eqr eqr' : V₀ → V₀ → F V₀} {fam fam' : V₀ → F V₀}
    (heq : ∀ a a' b b', R a a' → R b b' → RelF R (eqr a b) (eqr' a' b'))
    (hfam : ∀ a a', R a a' → RelF R (fam a) (fam' a')) :
    RelOptR R (· = ·) (allocPT eqr fam h) (allocPT eqr' fam' h') :=
  Or.inr ⟨_, _, rfl, rfl, hh.1, relHeap_alloc hh heq hfam⟩

/-- The eq-guarded scan preserves relatedness, given relatedness of runs at the
same fuel (the run-IH). The two scans take the same hit/miss branch at each entry
because the eq-realizers are `RelF`-related and `RTrue R` makes the verdicts
decode equally. -/
theorem rel_scan {R : V₀ → V₀ → Prop} (hRT : RTrue R) {fuel : ℕ}
    {eqr eqr' : V₀ → V₀ → F V₀} {a a' : V₀}
    (ihrun : ∀ (e e' : F V₀) (g g' : Heap V₀), RelF R e e' → RelHeap R g g' →
      RelOptR R R (run isTrue₀ fuel e g) (run isTrue₀ fuel e' g'))
    (heq : ∀ x x' y y', R x x' → R y y' → RelF R (eqr x y) (eqr' x' y'))
    (ha : R a a') {cache cache' : List (V₀ × V₀)}
    (hcache : cache.Forall₂ (fun p p' => R p.1 p'.1 ∧ R p.2 p'.2) cache') :
    ∀ {h h' : Heap V₀}, RelHeap R h h' →
      RelOptR R (OptRel R) (scan isTrue₀ fuel eqr a cache h)
        (scan isTrue₀ fuel eqr' a' cache' h') := by
  induction hcache with
  | nil =>
    intro h h' hh
    simp only [scan_nil]
    exact relOptR_pure (Or.inl ⟨rfl, rfl⟩) hh
  | cons hpair _ ih =>
    intro h h' hh
    obtain ⟨hkey, hval⟩ := hpair
    rw [scan_cons, scan_cons]
    refine relOptR_bind (ihrun _ _ _ _ (heq _ _ _ _ ha hkey) hh) ?_
    intro r r' g g' hrr hgg
    have hverdict : isTrue₀ r = isTrue₀ r' := hRT r r' hrr
    by_cases hb : isTrue₀ r = true
    · rw [if_pos hb, if_pos (hverdict ▸ hb)]
      exact relOptR_pure (Or.inr ⟨_, _, rfl, rfl, hval⟩) hgg
    · rw [if_neg hb, if_neg (hverdict ▸ hb)]
      exact ih hgg

/-- **The fundamental lemma / value-blindness.** `RelF`-related programs run on
`RelHeap`-related heaps produce `R`-related results. A code-opaque program (one
`RelF R`-related to itself for every `R` fixing the eq/family data) therefore
cannot tell apart heaps that differ only by an `R`-relabeling of stored values:
its observable output is `R`-invariant. -/
theorem rel_run {R : V₀ → V₀ → Prop} (hRT : RTrue R) :
    ∀ (fuel : ℕ) {e e' : F V₀} {h h' : Heap V₀}, RelF R e e' → RelHeap R h h' →
      RelOptR R R (run isTrue₀ fuel e h) (run isTrue₀ fuel e' h') := by
  intro fuel
  induction fuel with
  | zero => intro e e' h h' _ _; simp only [run_zero]; exact Or.inl ⟨rfl, rfl⟩
  | succ n ih =>
    intro e e' h h' he hh
    cases he with
    | ret hv => simp only [run_ret]; exact relOptR_pure hv hh
    | @memo ℓ a a' k k' ha hk =>
      simp only [run_memo]
      rcases hcl : h[ℓ]? with _ | cell <;> rcases hcl' : h'[ℓ]? with _ | cell'
      · exact Or.inl ⟨rfl, rfl⟩
      · exfalso; have hs := getElem?_len hh.1 ℓ; rw [hcl, hcl'] at hs; simp at hs
      · exfalso; have hs := getElem?_len hh.1 ℓ; rw [hcl, hcl'] at hs; simp at hs
      · obtain ⟨heqr, hfam, hcache⟩ := hh.2 ℓ cell cell' hcl hcl'
        refine relOptR_bind
          (rel_scan hRT (fun _ _ _ _ hr hg => ih hr hg) heqr ha hcache hh) ?_
        intro hit? hit'? g g' hhit hgg
        rcases hhit with ⟨hn, hn'⟩ | ⟨b, b', hbs, hbs', hbb⟩
        · subst hn; subst hn'
          have hinner : RelOptR R R
              (PT.bind (run isTrue₀ n (cell.fam a)) (commitPT ℓ a) g)
              (PT.bind (run isTrue₀ n (cell'.fam a')) (commitPT ℓ a') g') :=
            relOptR_bind (ih (hfam _ _ ha) hgg)
              (fun _ _ _ _ hx hgg2 => relOptR_commitPT hgg2 ha hx)
          exact relOptR_bind hinner (fun _ _ _ _ hx hgg2 => ih (hk _ _ hx) hgg2)
        · subst hbs; subst hbs'; exact ih (hk _ _ hbb) hgg
    | @alloc eqr eqr' fam fam' kont kont' heqr hfam hkont =>
      simp only [run_alloc]
      refine relOptR_bind (relOptR_allocPT hh heqr hfam) ?_
      intro ℓ ℓ' g g' hℓ hgg
      subst hℓ
      exact ih (hkont ℓ) hgg

/-- **Value-blindness, observable form.** Two `RelF`-related programs run on
`RelHeap`-related heaps decode to the *same* boolean. Taking `e' = e` and `h'` an
`R`-relabeling of `h` (with `R` fixing booleans, so `RTrue R`), a code-opaque
program's boolean output is invariant under relabeling the stored representative
codes — it cannot extract anything about them beyond what the eq-realizer and
family expose. This is the general value-blindness the canonical-attack results
(`Firewall.dia_eval`) exhibit case-by-case. -/
theorem value_blind_isTrue {R : V₀ → V₀ → Prop} (hRT : RTrue R) {e e' : F V₀}
    {h h' : Heap V₀} (he : RelF R e e') (hh : RelHeap R h h') {fuel : ℕ}
    {s : Step V₀ h} {s' : Step V₀ h'}
    (hrun : run isTrue₀ fuel e h = some s) (hrun' : run isTrue₀ fuel e' h' = some s') :
    isTrue₀ s.val = isTrue₀ s'.val := by
  rcases rel_run hRT fuel he hh with ⟨h1, _⟩ | ⟨t, t', ht, ht', hval, _⟩
  · rw [hrun] at h1; exact absurd h1 (by simp)
  · rw [hrun] at ht; rw [hrun'] at ht'
    obtain rfl := Option.some.inj ht
    obtain rfl := Option.some.inj ht'
    exact hRT _ _ hval

end VB

end LeanStatefulAoc
