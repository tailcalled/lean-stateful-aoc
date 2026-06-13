import LeanStatefulAoc.NonBoolean

/-!
# The Kripke–Heyting algebra of truth values (⊩-layer, propositional fragment)

K1 produced `KProp` — monotone propositions over the poset `Cond` of
single-valued conditions — and showed the operational `φ` sits in it with
`¬¬φ = ⊤`, `φ ≠ ⊤`. This file equips `KProp` with the Heyting connectives
(`kAnd`, `kOr`, `kImp`, with `kNot`/`kTop`/`kBot` from K1) and proves they
satisfy the **Heyting-algebra laws** — in particular the defining adjunction
`p ⊓ q ≤ r ↔ p ≤ (q ⇨ r)`. This is the truth-value algebra of the presheaf
topos over `Cond`. The payoff: the excluded middle **fails as an algebra law**
(`kEM_fails : kOr kPhi (kNot kPhi) ≠ kTop`), so the algebra is a Heyting algebra
that is *not* Boolean — K1's non-Booleanness made literal, no longer modulo an
informal identification.

(We prove the laws directly rather than via Mathlib's `HeytingAlgebra` typeclass,
to keep the development self-contained and free of order-instance plumbing; the
laws below are exactly the typeclass's fields.)

Scope: this is the *presheaf*, *propositional* ⊩-layer. The realizer-level
*sheaf* relation — where the local-eq firewall (`Firewall.lean` §8) lives, with
its quantification over cover branches — is the remaining frontier.
-/

namespace LeanStatefulAoc

namespace KProp

/-- Entailment of monotone propositions: pointwise implication. -/
def KLe (p q : KProp) : Prop := ∀ c, p.holds c → q.holds c

@[inherit_doc] scoped infix:50 " ≼ " => KProp.KLe

/-- Conjunction: pointwise. -/
def kAnd (p q : KProp) : KProp :=
  ⟨fun c => p.holds c ∧ q.holds c, fun hle h => ⟨p.mono hle h.1, q.mono hle h.2⟩⟩

/-- Disjunction: pointwise (union of up-sets is an up-set). -/
def kOr (p q : KProp) : KProp :=
  ⟨fun c => p.holds c ∨ q.holds c, fun hle h => h.imp (p.mono hle) (q.mono hle)⟩

/-- Kripke implication: forced at `c` when every extension forcing `p` forces `q`. -/
def kImp (p q : KProp) : KProp :=
  ⟨fun c => ∀ c', c ≤ c' → p.holds c' → q.holds c',
   fun hcd h c' hdc' hp => h c' (le_trans hcd hdc') hp⟩

/-! ### The Heyting-algebra laws -/

theorem KLe.refl (p : KProp) : p ≼ p := fun _ h => h
theorem KLe.trans {p q r : KProp} (h₁ : p ≼ q) (h₂ : q ≼ r) : p ≼ r :=
  fun c h => h₂ c (h₁ c h)

/-- Antisymmetry — needs propositional extensionality. -/
theorem KLe.antisymm {p q : KProp} (h₁ : p ≼ q) (h₂ : q ≼ p) : p = q := by
  cases p with | mk ph _ => cases q with | mk qh _ =>
  have : ph = qh := funext fun c => propext ⟨h₁ c, h₂ c⟩
  subst this; rfl

theorem le_kTop (p : KProp) : p ≼ kTop := fun _ _ => trivial
theorem kBot_le (p : KProp) : kBot ≼ p := fun _ h => h.elim

theorem kAnd_le_left (p q : KProp) : kAnd p q ≼ p := fun _ h => h.1
theorem kAnd_le_right (p q : KProp) : kAnd p q ≼ q := fun _ h => h.2
theorem le_kAnd {p q r : KProp} (h₁ : p ≼ q) (h₂ : p ≼ r) : p ≼ kAnd q r :=
  fun c h => ⟨h₁ c h, h₂ c h⟩

theorem le_kOr_left (p q : KProp) : p ≼ kOr p q := fun _ h => Or.inl h
theorem le_kOr_right (p q : KProp) : q ≼ kOr p q := fun _ h => Or.inr h
theorem kOr_le {p q r : KProp} (h₁ : p ≼ r) (h₂ : q ≼ r) : kOr p q ≼ r :=
  fun c h => h.elim (h₁ c) (h₂ c)

/-- **The defining Heyting adjunction**: `(· ⊓ q)` is left adjoint to `(q ⇨ ·)`.
This is what makes `kImp` the genuine Heyting implication, not just any
operation with the right type. -/
theorem kAnd_le_iff_le_kImp {p q r : KProp} : kAnd p q ≼ r ↔ p ≼ kImp q r := by
  constructor
  · intro h c hp c' hcc' hq
    exact h c' ⟨p.mono hcc' hp, hq⟩
  · intro h c hand
    exact h c hand.1 c (le_refl c) hand.2

/-- `kNot` is `kImp · ⊥`: the Heyting complement. -/
theorem kImp_kBot (p : KProp) : kImp p kBot = kNot p := rfl

/-! ### The internal "decidability" proposition, and when it fails

`kDec p := p ⊔ ¬p` is the internal "`p` is decidable / excluded middle for `p`".
The reusable core of non-Booleanness: `kDec p ≠ ⊤` whenever some condition
leaves `p` *undecided* (forces neither `p` nor `¬p`). Both K1's `φ` and the
Diaconescu obstruction (the equality of `2/~ₚ`'s two points, once internalized)
are instances — they are *generic* propositions, undecided at the root. -/

/-- The internal excluded middle / decidability of `p`. -/
def kDec (p : KProp) : KProp := kOr p (kNot p)

/-- `p` is undecided at `c`: neither `p` nor `¬p` is forced there. -/
def Undecided (p : KProp) (c : Cond) : Prop := ¬ p.holds c ∧ ¬ (kNot p).holds c

/-- **The reusable non-Booleanness core.** If `p` is undecided at any condition,
its internal decidability is not `⊤`. -/
theorem kDec_ne_top_of_undecided {p : KProp} {c : Cond} (h : Undecided p c) :
    kDec p ≠ kTop := by
  intro he
  have hb : (kDec p).holds c := by rw [he]; trivial
  rcases hb with hp | hn
  · exact h.1 hp
  · exact h.2 hn

/-! ### Excluded middle fails -/

/-- `φ` is a *generic* proposition: undecided at the base condition. The
firewall blocks `φ` (`protected_h₀`), density blocks `¬φ` (`kPhi_dense`). -/
theorem undecided_kPhi : Undecided kPhi base := by
  refine ⟨protected_h₀.not_forcesPhi, fun hn => ?_⟩
  obtain ⟨c', hle, hphi⟩ := kPhi_dense base
  exact hn c' hle hphi

/-- **Excluded middle fails in the algebra.** `φ ⊔ ¬φ ≠ ⊤`. A Boolean algebra
satisfies `p ⊔ pᶜ = ⊤` for every `p`; this Heyting algebra has a `p` (the
operational `φ`) where that law fails — so it is **not** Boolean. An instance of
the generic-undecidability core `kDec_ne_top_of_undecided`. -/
theorem kEM_fails : kDec kPhi ≠ kTop :=
  kDec_ne_top_of_undecided undecided_kPhi

/-- Packaged: the Kripke–Heyting algebra of truth values over single-valued
conditions is a Heyting algebra (laws above) in which excluded middle fails. -/
theorem heyting_em_fails : ∃ p : KProp, kDec p ≠ kTop :=
  ⟨kPhi, kEM_fails⟩

/-! ### A *symmetric* generic, and the two firewall regimes

K1's `φ` is an *asymmetric* generic: `φ` is forceable, but `¬φ` is forced
*nowhere* — one can always still commit a `true`. The equality of a genuine
two-point glued type (`2/~ₚ` with `P` genuinely two-valued-generic) is instead
*symmetric*: both the equal- and the unequal-verdict are forceable, on
incomparable branches.

`kVerdict` models exactly that. The designated bit is "key `nat 0` is committed
to `false`". Committing `nat 0 ↦ false` forces it; committing `nat 0 ↦ true`
forces its negation (single-valuedness blocks the other value); at the root
neither. So **both `kVerdict` and `¬kVerdict` are forceable** — the symmetric
structure `φ` lacks.

This sharpens the firewall into two regimes:

* *(a) premise unsuppliable* — asymmetric generic (`φ`): the deceq premise cannot
  be supplied at the root at all (`no_decision_phiGluing`), so `AC_dec` never
  starts. Degenerate; **done**.
* *(b) premise suppliable, value-blind* — symmetric generic (`kVerdict`): a local
  eq *can* commit a verdict per branch, supplying the premise; the firewall is
  then that the memoizer yields *no more* than that verdict (value-blindness
  over branches). This is the genuine Diaconescu firewall and is **open**.
-/

/-- A cache with pairwise-distinct keys is functional. -/
theorem cache_funct {l : List (V₀ × V₀)} (hkd : l.Pairwise fun p q => p.1 ≠ q.1)
    {a b₁ b₂ : V₀} (h₁ : (a, b₁) ∈ l) (h₂ : (a, b₂) ∈ l) : b₁ = b₂ := by
  induction l with
  | nil => exact absurd h₁ (List.not_mem_nil)
  | cons hd tl ih =>
    rw [List.pairwise_cons] at hkd
    rcases List.mem_cons.mp h₁ with he₁ | hm₁ <;> rcases List.mem_cons.mp h₂ with he₂ | hm₂
    · have : (a, b₁) = (a, b₂) := he₁.trans he₂.symm
      exact (Prod.ext_iff.mp this).2
    · have hne := hkd.1 (a, b₂) hm₂
      rw [← he₁] at hne; exact absurd rfl hne
    · have hne := hkd.1 (a, b₁) hm₁
      rw [← he₂] at hne; exact absurd rfl hne
    · exact ih hkd.2 hm₁ hm₂

/-- `kVerdict` forced at `h`: key `nat 0` is committed to `false` in cell `0`. -/
def ForcesVerdict (h : Heap V₀) : Prop :=
  ∃ cell, h[0]? = some cell ∧ (V₀.nat 0, V₀.bool false) ∈ cell.cache

theorem forcesVerdict_persists {c c' : Cond} (hle : c ≤ c')
    (h : ForcesVerdict c.1) : ForcesVerdict c'.1 := by
  obtain ⟨cell, hcell, hmem⟩ := h
  obtain ⟨cell', hcell', hLe⟩ := hle 0 cell hcell
  obtain ⟨p, hp⟩ := hLe.2.2
  exact ⟨cell', hcell', by rw [hp]; exact List.mem_append_right p hmem⟩

/-- The symmetric generic: "the designated bit was decided `false`". -/
def kVerdict : KProp := ⟨fun c => ForcesVerdict c.1, forcesVerdict_persists⟩

/-- Committing the designated bit to `b` from the base condition. -/
def commitBase (b : Bool) : Cond :=
  ⟨h₀.commit 0 (V₀.nat 0) (V₀.bool b),
   le_trans base.2.1 (Heap.le_commit h₀ 0 (V₀.nat 0) (V₀.bool b)), by
    intro cell hcell
    rw [Heap.commit, Heap.getElem?_updateCell_self] at hcell
    simp only [h₀, cell₀, List.getElem?_cons_zero, Option.map_some] at hcell
    obtain rfl := Option.some.inj hcell
    exact List.pairwise_singleton _ _⟩

theorem commitBase_cell (b : Bool) :
    (commitBase b).1[0]? = some ⟨eqCode, famFalse, [(V₀.nat 0, V₀.bool b)]⟩ := by
  change (h₀.commit 0 (V₀.nat 0) (V₀.bool b))[0]? = _
  rw [Heap.commit, Heap.getElem?_updateCell_self]
  rfl

/-- `kVerdict` is forced after committing `false`. -/
theorem kVerdict_holds_commit_false : kVerdict.holds (commitBase false) :=
  ⟨_, commitBase_cell false, List.mem_singleton.mpr rfl⟩

/-- `¬kVerdict` is forced after committing `true`: single-valuedness blocks any
later `false` commit at the same key. **This is the branch `φ` does not have.** -/
theorem kNot_kVerdict_holds_commit_true : (kNot kVerdict).holds (commitBase true) := by
  intro c' hle hv
  obtain ⟨cellf, hcellf, hmemf⟩ := hv
  obtain ⟨cellt, hcellt, hLe⟩ := hle 0 _ (commitBase_cell true)
  obtain ⟨p, hp⟩ := hLe.2.2
  have hmemt : (V₀.nat 0, V₀.bool true) ∈ cellt.cache := by
    rw [hp]; exact List.mem_append_right p (List.mem_singleton.mpr rfl)
  rw [hcellf] at hcellt
  obtain rfl := Option.some.inj hcellt
  have hkd := c'.2.2 _ hcellf
  exact absurd (cache_funct hkd hmemf hmemt) (by decide)

/-- `kVerdict` is undecided at the base condition — and, unlike `φ`, *both* it
and its negation are forceable above the base. -/
theorem undecided_kVerdict : Undecided kVerdict base := by
  refine ⟨?_, ?_⟩
  · rintro ⟨cell, hcell, hmem⟩
    simp only [base, h₀, cell₀, List.getElem?_cons_zero, Option.some.injEq] at hcell
    rw [← hcell] at hmem
    exact absurd hmem (List.not_mem_nil)
  · intro hn
    exact hn (commitBase false)
      (Heap.le_commit h₀ 0 (V₀.nat 0) (V₀.bool false)) kVerdict_holds_commit_false

/-- The internal decidability of the symmetric generic also fails — and here the
deceq premise is genuinely *suppliable* per branch (regime (b)), so what remains
is value-blindness, not unsuppliability. -/
theorem kVerdict_dec_fails : kDec kVerdict ≠ kTop :=
  kDec_ne_top_of_undecided undecided_kVerdict

end KProp

end LeanStatefulAoc
