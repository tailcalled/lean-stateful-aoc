import LeanStatefulAoc.Combinators
import LeanStatefulAoc.CodeEval

/-!
# Realizability tripos (Layer 2) — truth values and the entailment preorder

The truth values of the realizability topos are **realizability propositions**:
a relation `rel : CHeap → Code → Prop` ("code `e` realizes the proposition at
condition `h`"), closed under **expansion** (anti-reduction: if `e` steps to `e'`
and `e'` realizes, so does `e`). Closure under expansion is the standard
saturation condition that makes realizability well-behaved.

Entailment `P ⟹ Q` asks for a single realizer code `r` uniformly transporting a
realizer `a` of `P` to the realizer `r ⬝ a` of `Q`. Here the realizers are *pure*
combinators (the logical structure has no effects — those enter only with the
memoizer in Layer 3), so we reason with the pure reduction `Reds` from Layer 1;
the condition `h` is carried along unchanged.

This file: `RProp`, the entailment, and the **preorder** laws — reflexivity (the
identity combinator `I`) and transitivity (the composition combinator `B`, whose
reduction `B ⬝ f ⬝ g ⬝ x ↠ f ⬝ (g ⬝ x)` is proven from the `S`/`K` rules).
-/

namespace LeanStatefulAoc

open Code

/-- A realizability proposition: which codes realize it at each condition,
closed under expansion (anti-reduction). -/
structure RProp where
  /-- `rel h e`: code `e` realizes the proposition at condition `h`. -/
  rel : CHeap → Code → Prop
  /-- closure under a single expansion step -/
  exp : ∀ {h e e'}, Code.Red e e' → rel h e' → rel h e

/-- Closure under multi-step expansion. -/
theorem RProp.expReds (P : RProp) {h e e'} (r : Code.Reds e e') :
    P.rel h e' → P.rel h e := by
  induction r with
  | refl => exact id
  | tail _ r2 ih => exact fun hc => ih (P.exp r2 hc)

/-- Realizability entailment: one realizer transports `P` to `Q` uniformly. -/
def Entails (P Q : RProp) : Prop :=
  ∃ r : Code, ∀ h a, P.rel h a → Q.rel h (r ⬝ a)

@[inherit_doc] scoped infix:50 " ⟹ " => Entails

/-! ### The composition combinator -/

/-- `B = S (K S) K`, with `B ⬝ f ⬝ g ⬝ x ↠ f ⬝ (g ⬝ x)`. -/
def Code.B : Code := S ⬝ (K ⬝ S) ⬝ K

theorem Code.B_app (f g x : Code) : Code.Reds (B ⬝ f ⬝ g ⬝ x) (f ⬝ (g ⬝ x)) := by
  have h1 : Code.Reds (B ⬝ f) (S ⬝ (K ⬝ f)) :=
    .trans (.single Code.Red.s) (Code.Reds.appL (.single Code.Red.k) _)
  have h2 : Code.Reds (B ⬝ f ⬝ g ⬝ x) (S ⬝ (K ⬝ f) ⬝ g ⬝ x) :=
    Code.Reds.appL (Code.Reds.appL h1 g) x
  exact .trans h2
    (.trans (.single Code.Red.s) (Code.Reds.appL (.single Code.Red.k) _))

/-! ### The entailment preorder -/

theorem Entails.refl (P : RProp) : P ⟹ P :=
  ⟨Code.I, fun _ _ ha => P.expReds Code.Reds.i ha⟩

theorem Entails.trans {P Q R : RProp} (hPQ : P ⟹ Q) (hQR : Q ⟹ R) : P ⟹ R := by
  obtain ⟨r₁, hr₁⟩ := hPQ
  obtain ⟨r₂, hr₂⟩ := hQR
  refine ⟨Code.B ⬝ r₂ ⬝ r₁, fun h a ha => ?_⟩
  exact R.expReds (Code.B_app r₂ r₁ a) (hr₂ h (r₁ ⬝ a) (hr₁ h a ha))

/-! ### Top and bottom -/

/-- The true proposition: realized by anything. -/
def RProp.top : RProp := ⟨fun _ _ => True, fun _ _ => trivial⟩

/-- The false proposition: realized by nothing. -/
def RProp.bot : RProp := ⟨fun _ _ => False, fun _ h => h⟩

/-- `⊤` is the greatest element. -/
theorem Entails.le_top (P : RProp) : P ⟹ RProp.top := ⟨Code.I, fun _ _ _ => trivial⟩

/-- `⊥` is the least element (ex falso). -/
theorem Entails.bot_le (P : RProp) : RProp.bot ⟹ P := ⟨Code.I, fun _ _ h => h.elim⟩

/-! ### Conjunction (product) -/

/-- `P ⊓ Q` is realized by a pair `pr ⬝ a ⬝ b` of realizers. -/
def RProp.and (P Q : RProp) : RProp where
  rel h e := ∃ a b, Code.Reds e (Code.pr ⬝ a ⬝ b) ∧ P.rel h a ∧ Q.rel h b
  exp := fun r ⟨a, b, hred, hp, hq⟩ => ⟨a, b, Relation.ReflTransGen.head r hred, hp, hq⟩

@[inherit_doc] scoped infixl:60 " ⊓ᵣ " => RProp.and

/-- First projection. -/
theorem Entails.and_left (P Q : RProp) : P ⊓ᵣ Q ⟹ P :=
  ⟨Code.fst, fun _ _ ⟨_, _, hred, hp, _⟩ =>
    P.expReds (.trans (Code.Reds.appR Code.fst hred) (.single Code.Red.prL)) hp⟩

/-- Second projection. -/
theorem Entails.and_right (P Q : RProp) : P ⊓ᵣ Q ⟹ Q :=
  ⟨Code.snd, fun _ _ ⟨_, _, hred, _, hq⟩ =>
    Q.expReds (.trans (Code.Reds.appR Code.snd hred) (.single Code.Red.prR)) hq⟩

/-- Pairing — the universal property of the product. The realizer
`S ⬝ (B ⬝ pr ⬝ r₁) ⬝ r₂` is closed (no bracket abstraction needed). -/
theorem Entails.and_intro {R P Q : RProp} (hP : R ⟹ P) (hQ : R ⟹ Q) :
    R ⟹ P ⊓ᵣ Q := by
  obtain ⟨r₁, hr₁⟩ := hP
  obtain ⟨r₂, hr₂⟩ := hQ
  refine ⟨Code.S ⬝ (Code.B ⬝ Code.pr ⬝ r₁) ⬝ r₂, fun h a ha => ?_⟩
  refine ⟨r₁ ⬝ a, r₂ ⬝ a, ?_, hr₁ h a ha, hr₂ h a ha⟩
  exact .trans (.single Code.Red.s) (Code.Reds.appL (Code.B_app Code.pr r₁ a) (r₂ ⬝ a))

/-! ### Disjunction (coproduct) -/

/-- `P ⊔ Q` is realized by a tagged realizer `inl ⬝ a` (left) or `inr ⬝ b` (right). -/
def RProp.or (P Q : RProp) : RProp where
  rel h e :=
    (∃ a, Code.Reds e (Code.inl ⬝ a) ∧ P.rel h a) ∨
    (∃ b, Code.Reds e (Code.inr ⬝ b) ∧ Q.rel h b)
  exp := fun r hc => hc.imp
    (fun ⟨a, hred, hp⟩ => ⟨a, Relation.ReflTransGen.head r hred, hp⟩)
    (fun ⟨b, hred, hq⟩ => ⟨b, Relation.ReflTransGen.head r hred, hq⟩)

@[inherit_doc] scoped infixl:55 " ⊔ᵣ " => RProp.or

/-- Left injection. -/
theorem Entails.inl (P Q : RProp) : P ⟹ P ⊔ᵣ Q :=
  ⟨Code.inl, fun _ _ hp => Or.inl ⟨_, Code.Reds.refl, hp⟩⟩

/-- Right injection. -/
theorem Entails.inr (P Q : RProp) : Q ⟹ P ⊔ᵣ Q :=
  ⟨Code.inr, fun _ _ hq => Or.inr ⟨_, Code.Reds.refl, hq⟩⟩

/-- Case analysis — the universal property of the coproduct. With branches-before-
scrutinee `case`, the eliminator realizer is the closed term `case ⬝ r₁ ⬝ r₂`. -/
theorem Entails.or_elim {P Q R : RProp} (hP : P ⟹ R) (hQ : Q ⟹ R) :
    P ⊔ᵣ Q ⟹ R := by
  obtain ⟨r₁, hr₁⟩ := hP
  obtain ⟨r₂, hr₂⟩ := hQ
  refine ⟨Code.case ⬝ r₁ ⬝ r₂, fun h e he => ?_⟩
  rcases he with ⟨a, hred, hp⟩ | ⟨b, hred, hq⟩
  · exact R.expReds
      (.trans (Code.Reds.appR _ hred) (.single Code.Red.caseL)) (hr₁ h a hp)
  · exact R.expReds
      (.trans (Code.Reds.appR _ hred) (.single Code.Red.caseR)) (hr₂ h b hq)

/-! ### Implication (exponential) -/

/-- `P ⇒ Q` is realized by a code that maps every realizer of `P` to one of `Q`.
The condition `h` is fixed (Layer-2 realizers carry it unchanged). -/
def RProp.imp (P Q : RProp) : RProp where
  rel h e := ∀ a, P.rel h a → Q.rel h (e ⬝ a)
  exp := fun r hf a hpa => Q.exp (Code.Red.appL r) (hf a hpa)

@[inherit_doc] scoped infixr:53 " ⇨ᵣ " => RProp.imp

/-- Currying — half of the exponential adjunction `P ⊓ Q ⟹ R ↔ P ⟹ (Q ⇒ R)`.
Realizer `B ⬝ (B ⬝ r) ⬝ pr` applied to `p` then `q` reduces to `r ⬝ (pr ⬝ p ⬝ q)`. -/
theorem Entails.curry {P Q R : RProp} (hPQR : P ⊓ᵣ Q ⟹ R) : P ⟹ Q ⇨ᵣ R := by
  obtain ⟨r, hr⟩ := hPQR
  refine ⟨Code.B ⬝ (Code.B ⬝ r) ⬝ Code.pr, fun h p hp => ?_⟩
  intro q hq
  refine R.expReds ?_ (hr h (Code.pr ⬝ p ⬝ q) ⟨p, q, Code.Reds.refl, hp, hq⟩)
  exact .trans
    (Code.Reds.appL (Code.B_app (Code.B ⬝ r) Code.pr p) q)
    (Code.B_app r (Code.pr ⬝ p) q)

/-- Uncurrying — the other half of the adjunction. Realizer `S ⬝ (B ⬝ r ⬝ fst) ⬝ snd`
applied to a pair `pr ⬝ a ⬝ b` reduces to `(r ⬝ a) ⬝ b`. -/
theorem Entails.uncurry {P Q R : RProp} (hP : P ⟹ Q ⇨ᵣ R) : P ⊓ᵣ Q ⟹ R := by
  obtain ⟨r, hr⟩ := hP
  refine ⟨Code.S ⬝ (Code.B ⬝ r ⬝ Code.fst) ⬝ Code.snd,
    fun h e ⟨a, b, hred, hp, hq⟩ => ?_⟩
  have hfst : Code.Reds (Code.fst ⬝ e) a :=
    .trans (Code.Reds.appR Code.fst hred) (.single Code.Red.prL)
  have hsnd : Code.Reds (Code.snd ⬝ e) b :=
    .trans (Code.Reds.appR Code.snd hred) (.single Code.Red.prR)
  have hleft : Code.Reds (Code.B ⬝ r ⬝ Code.fst ⬝ e) (r ⬝ a) :=
    .trans (Code.B_app r Code.fst e) (Code.Reds.appR r hfst)
  refine R.expReds ?_ (hr h a hp b hq)
  exact .trans (.single Code.Red.s)
    (.trans (Code.Reds.appL hleft (Code.snd ⬝ e)) (Code.Reds.appR (r ⬝ a) hsnd))

/-- Modus ponens (the counit `(Q ⇒ R) ⊓ Q ⟹ R`), from uncurrying reflexivity. -/
theorem Entails.modus_ponens (Q R : RProp) : (Q ⇨ᵣ R) ⊓ᵣ Q ⟹ R :=
  Entails.uncurry (Entails.refl (Q ⇨ᵣ R))

/-! ### Quantifiers (adjoint to weakening)

For a predicate `φ : I → RProp` over an index type, `∀`/`∃` quantify out the index.
The defining feature of the *realizability* tripos: the adjunction transpose
**preserves the realizer** — the same code `r` witnesses both sides, because the
combinatory algebra absorbs the uniformity over `I`. -/

/-- Entailment of `I`-indexed predicates: one realizer, uniform in the index. -/
def EntailsI (I : Type) (φ ψ : I → RProp) : Prop :=
  ∃ r : Code, ∀ i h a, (φ i).rel h a → (ψ i).rel h (r ⬝ a)

/-- Universal quantifier: a single realizer must work at every index. -/
def RProp.all (I : Type) (φ : I → RProp) : RProp where
  rel h e := ∀ i, (φ i).rel h e
  exp := fun r hf i => (φ i).exp r (hf i)

/-- Existential quantifier: realized at some index (the witness is realizer-free). -/
def RProp.ex (I : Type) (φ : I → RProp) : RProp where
  rel h e := ∃ i, (φ i).rel h e
  exp := fun r ⟨i, hi⟩ => ⟨i, (φ i).exp r hi⟩

/-- `∀` is right adjoint to weakening: `(∀ i, P → φ i) ↔ P → ∀ i, φ i`, with the
**same** realizer on both sides. -/
theorem all_adjunction {I : Type} (P : RProp) (φ : I → RProp) :
    EntailsI I (fun _ => P) φ ↔ P ⟹ RProp.all I φ := by
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, fun h a ha i => hr i h a ha⟩
  · rintro ⟨r, hr⟩; exact ⟨r, fun i h a ha => hr h a ha i⟩

/-- `∃` is left adjoint to weakening: `(∀ i, φ i → Q) ↔ (∃ i, φ i) → Q`, with the
**same** realizer on both sides. -/
theorem ex_adjunction {I : Type} (φ : I → RProp) (Q : RProp) :
    EntailsI I φ (fun _ => Q) ↔ RProp.ex I φ ⟹ Q := by
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, fun h a ⟨i, hi⟩ => hr i h a hi⟩
  · rintro ⟨r, hr⟩; exact ⟨r, fun i h a ha => hr h a ⟨i, ha⟩⟩

/-- `∀`-elimination (the counit): instantiate at any index. -/
theorem Entails.all_elim {I : Type} (φ : I → RProp) (i : I) : RProp.all I φ ⟹ φ i :=
  ⟨Code.I, fun _ _ ha => (φ i).expReds Code.Reds.i (ha i)⟩

/-- `∃`-introduction (the unit): inject at any index. -/
theorem Entails.ex_intro {I : Type} (φ : I → RProp) (i : I) : φ i ⟹ RProp.ex I φ :=
  ⟨Code.I, fun _ _ ha => ⟨i, (φ i).expReds Code.Reds.i ha⟩⟩

end LeanStatefulAoc
