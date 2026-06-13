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

/-! ### Excluded middle fails -/

/-- At the base condition neither `φ` nor `¬φ` is forced: the firewall blocks
`φ` (`protected_h₀`), density blocks `¬φ` (`kPhi_dense`). -/
theorem base_not_kOr_kPhi_kNot : ¬ (kOr kPhi (kNot kPhi)).holds base := by
  rintro (hp | hn)
  · exact protected_h₀.not_forcesPhi hp
  · obtain ⟨c', hle, hphi⟩ := kPhi_dense base
    exact hn c' hle hphi

/-- **Excluded middle fails in the algebra.** `φ ⊔ ¬φ ≠ ⊤`. A Boolean algebra
satisfies `p ⊔ pᶜ = ⊤` for every `p`; this Heyting algebra has a `p` (the
operational `φ`) where that law fails — so it is **not** Boolean. -/
theorem kEM_fails : kOr kPhi (kNot kPhi) ≠ kTop := by
  intro h
  exact base_not_kOr_kPhi_kNot (h ▸ trivial)

/-- Packaged: the Kripke–Heyting algebra of truth values over single-valued
conditions is a Heyting algebra (laws above) in which excluded middle fails. -/
theorem heyting_em_fails : ∃ p : KProp, kOr p (kNot p) ≠ kTop :=
  ⟨kPhi, kEM_fails⟩

end KProp

end LeanStatefulAoc
