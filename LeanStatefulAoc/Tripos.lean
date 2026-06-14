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

end LeanStatefulAoc
