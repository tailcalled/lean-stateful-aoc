import LeanStatefulAoc.Choice

/-!
# The Diaconescu firewall, formalized (K3, first result)

The slogan "`AC_dec` cannot bootstrap EM" (README) made precise in the
project's own terms. The Diaconescu obstruction is `2/~ₚ` — two points of
`Bool` glued iff a proposition `P` holds (`Glue P`). Its decidable equality is
*exactly* `P ∨ ¬P`: `⟦true⟧ = ⟦false⟧ ↔ P`.

The key result `acCell_glue_firewall`: an `AcCell (Glue P) B` — the data needed
to run the memoizer over this index — together with key codes for the two
points entails `P ∨ ¬P`. So `AC_dec` over `Glue P` *consumes* the excluded
middle for `P`; it never produces it. The memoizer adds nothing: routing a
query is the *only* way to interact with the cell (the syntax `F` exposes no
introspection — no key enumeration, cache-size, or cell-identity comparison),
and routing is precisely an eq-realizer call, which `sound` ties to index
equality, which here is `P`.

## Honest scope

This proves the firewall for the **global / pure** eq-code that `AcCell`
currently carries: building the cell requires `eqb` to *globally* decide
`P`. The genuinely hard frontier — an **effectful, only-locally-decidable** eq
realizer (`eqr : V₀ → V₀ → F V₀` that refines the condition to decide
equality on a cover, never deciding `P` globally) — is *not* settled here: that
the memoizer over such a local eq still leaks nothing is the open
`Realizes`-tier problem (`THEORY.md` §8). What is shown is that the soundness
*obligation* is the carrier of the obstruction, independent of effects.
-/

namespace LeanStatefulAoc

universe v

variable (P : Prop)

/-- The gluing relation on `Bool`: equal, or identified because `P` holds. -/
def glueRel (a b : Bool) : Prop := a = b ∨ P

theorem glueRel.refl (a : Bool) : glueRel P a a := Or.inl rfl

theorem glueRel.symm {a b : Bool} : glueRel P a b → glueRel P b a
  | Or.inl h => Or.inl h.symm
  | Or.inr h => Or.inr h

theorem glueRel.trans {a b c : Bool} : glueRel P a b → glueRel P b c → glueRel P a c
  | Or.inl h₁, Or.inl h₂ => Or.inl (h₁.trans h₂)
  | Or.inr h, _ => Or.inr h
  | _, Or.inr h => Or.inr h

/-- The setoid identifying the two booleans iff `P`. -/
def glueSetoid : Setoid Bool where
  r := glueRel P
  iseqv := ⟨glueRel.refl P, glueRel.symm P, glueRel.trans P⟩

/-- `2/~ₚ`: two points glued iff `P`. -/
def Glue : Type := Quotient (glueSetoid P)

/-- A boolean as a point of `Glue P`. -/
def Glue.mk (b : Bool) : Glue P := Quotient.mk (glueSetoid P) b

variable {P}

theorem glue_eq_iff {a b : Bool} : Glue.mk P a = Glue.mk P b ↔ (a = b ∨ P) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The two points of `Glue P` are equal **iff `P`** — its decidable equality
is the excluded middle for `P`. -/
theorem mk_true_eq_mk_false_iff : Glue.mk P true = Glue.mk P false ↔ P := by
  rw [glue_eq_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (by decide)
    · exact h
  · exact fun h => Or.inr h

/-- Deciding equality of the two points decides `P`. -/
def decidableP_of_decEqGlue (d : DecidableEq (Glue P)) : Decidable P :=
  decidable_of_iff _ mk_true_eq_mk_false_iff

/-- Conversely, deciding `P` decides equality on `Glue P`. -/
def decEqGlue_of_decidableP (d : Decidable P) : DecidableEq (Glue P) := by
  intro x y
  refine Quotient.recOnSubsingleton₂ x y fun a b => ?_
  exact decidable_of_iff _ (glue_eq_iff (a := a) (b := b)).symm

/-- A `Decidable` instance hands back the excluded middle for its proposition
(constructively — no `Classical`). -/
theorem em_of_decidable {Q : Prop} (d : Decidable Q) : Q ∨ ¬Q :=
  match d with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

/-- **The firewall.** Any `AcCell` over the Diaconescu index `Glue P`, together
with key codes realizing its two points, entails `P ∨ ¬P`. Building the data
that lets the memoizer run over `Glue P` already requires the excluded middle
for `P`; `AC_dec` therefore returns only the EM it was given.

The proof uses the *actual boolean* `C.eqb k₀ k₁` to decide `P` — it is
constructive, and the EM comes entirely from the soundness obligation on the
supplied eq-code, not from the memoizer. -/
theorem acCell_glue_firewall {B : Glue P → Type v} (C : AcCell (Glue P) B)
    {k₀ k₁ : V₀} (h₀ : C.KeyRel k₀ (Glue.mk P true))
    (h₁ : C.KeyRel k₁ (Glue.mk P false)) : P ∨ ¬P := by
  have hiff : C.eqb k₀ k₁ = true ↔ P :=
    (C.sound h₀ h₁).trans mk_true_eq_mk_false_iff
  cases hb : C.eqb k₀ k₁ with
  | false =>
    refine Or.inr fun hP => ?_
    have : (false : Bool) = true := hb ▸ hiff.mpr hP
    exact Bool.noConfusion this
  | true => exact Or.inl (hiff.mp hb)

/-- Restated as a decision procedure: the eq-code of any `AcCell` over
`Glue P` *is* a decision of `P`. -/
def acCell_glue_decidesP {B : Glue P → Type v} (C : AcCell (Glue P) B)
    {k₀ k₁ : V₀} (h₀ : C.KeyRel k₀ (Glue.mk P true))
    (h₁ : C.KeyRel k₁ (Glue.mk P false)) : Decidable P :=
  decidable_of_iff _ ((C.sound h₀ h₁).trans mk_true_eq_mk_false_iff)

/-- **Effects do not escape the firewall.** Internalize eq as an *effectful*
realizer `eqr : V₀ → V₀ → F V₀`. Suppose running it on the two `Glue P`
point-codes from some heap `h` terminates (`hrun`) with a verdict that is
*sound there* (`hsound`: the decoded boolean tracks semantic equality of the two
points). Then `P ∨ ¬P`, constructively.

The moral: a single run of the deterministic monad yields a *definite* verdict,
and a definite sound verdict on `Glue P` decides `P`. So allowing eq to read and
extend the heap buys nothing toward escaping the firewall. The only escape is
for `eqr` to have *no* terminating sound verdict from the root at all — genuine
per-branch (sheaf) genericity, where eq answers differently on different cover
branches and so decides `P` on *none*. That lives in the ⊩-semantics (the
quantification over branches), not in any single deterministic run; it is the
real open frontier (`THEORY.md` §8), and this lemma pins down that *effects per
se* are not it. -/
theorem effectful_glue_firewall {eqr : V₀ → V₀ → F V₀} {k₀ k₁ : V₀}
    {h : Heap V₀} {fuel : ℕ} {s : Step V₀ h}
    (_hrun : run isTrue₀ fuel (eqr k₀ k₁) h = some s)
    (hsound : isTrue₀ s.val = true ↔ Glue.mk P true = Glue.mk P false) :
    P ∨ ¬P := by
  rw [mk_true_eq_mk_false_iff] at hsound
  cases hb : isTrue₀ s.val with
  | false =>
    refine Or.inr fun hP => ?_
    have h1 : isTrue₀ s.val = true := hsound.mpr hP
    rw [hb] at h1
    exact Bool.noConfusion h1
  | true => exact Or.inl (hsound.mp hb)

/-! ## The firewall for an *internally undecided* equality (local case)

§8 above glues by an *external* `P : Prop`, which is globally decided-or-not.
The genuine local case glues by an *internal, generic* proposition — one
undecided at the root. K1's `φ` is exactly such a proposition
(`em_not_realized`). Here we glue `Bool`'s two points "equal ⟺ `φ`" and show
**no eq-realizer can decide that equality at the base condition** — recasting K1's
non-Booleanness directly as a Diaconescu firewall.

This is the conceptual bridge: *non-Booleanness and the Diaconescu firewall are
the same phenomenon* for the internal case. Supplying `AC_dec`'s `DecidableEq`
premise for the `φ`-glued type is *exactly* deciding `φ`, which K1 forbids — so
`AC_dec` cannot be invoked over it, and manufactures no EM.

Scope: this is the *no-global-decision* half. A genuinely *local* eq decides the
equality per cover branch (on extensions of `h₀`), not at `h₀` itself; that such
a local eq, wired into the memoizer, leaks nothing is the open branch-quantified
problem (`THEORY.md` §9). -/

/-- An eq-realizer **decides the `φ`-gluing** at heap `h` if, run on the two
glued point-codes, it terminates with a verdict that soundly tracks the points'
(generic) equality — `equal ⟺ φ`. This is the operational form of "supplying
`DecidableEq` of the `φ`-glued type at `h`": a `true` verdict realizes the
equality (`φ`), a `false` verdict its negation. -/
def DecidesPhiGluing (eqr : V₀ → V₀ → F V₀) (k₀ k₁ : V₀) (h : Heap V₀) : Prop :=
  ∃ (fuel : ℕ) (s : Step V₀ h),
    run isTrue₀ fuel (eqr k₀ k₁) h = some s ∧
    (if isTrue₀ s.val then ForcesPhi s.next else ForcesNegPhi s.next)

/-- **The internal/local firewall (no-global-decision half).** No eq-realizer
decides the `φ`-gluing at the base condition. The proof *is* K1's
`em_not_realized`: the eq-realizer applied to the two point-codes would be a
program deciding `φ ∨ ¬φ` at the root, which does not exist. Hence the
`DecidableEq` premise for the `φ`-glued type is unrealizable there, `AC_dec`
cannot be invoked, and no excluded middle leaks — for an equality that is
*genuinely only locally decidable*, unlike the global `P` of §8. -/
theorem no_decision_phiGluing (eqr : V₀ → V₀ → F V₀) (k₀ k₁ : V₀) :
    ¬ DecidesPhiGluing eqr k₀ k₁ h₀ := by
  rintro ⟨fuel, s, hrun, hverdict⟩
  exact em_not_realized ⟨eqr k₀ k₁, fuel, s, hrun, hverdict⟩

end LeanStatefulAoc
