import LeanStatefulAoc.CodeEval

/-!
# Realizability tripos (Layer 2) — framework and entailment preorder

The truth values of the realizability topos are **realizability propositions**:
`RProp := CHeap → Code → Prop`, "code `e` realizes the proposition at condition
`h`". Entailment `Entails P Q` asks for a *single* realizer code that uniformly
transports a realizer of `P` to one of `Q` — where "transports" means the
effectful application `r ⬝ a`, run by `eval`, *produces* a realizer of `Q`. This
is the realizability tripos's order; the Heyting structure and quantifiers are
built on it.

This file: the `eval` equation lemmas (needed to reason about a well-founded
recursive evaluator), the `RProp`/`Produces`/`Entails` definitions, and the
**preorder** laws (reflexivity via the identity combinator, transitivity via
composition). The Heyting operations come next.
-/

namespace LeanStatefulAoc

open Code

/-! ### Realizability propositions and entailment -/

/-- A realizability proposition: which value-codes realize it at each condition. -/
def RProp : Type := CHeap → Code → Prop

/-- `e` produces, from condition `h`, a value realizing `Q`. -/
def Produces (h : CHeap) (e : Code) (Q : RProp) : Prop :=
  ∃ (fuel : Nat) (h' : CHeap) (v : Code), eval fuel h e = some (h', v) ∧ Q h' v

/-- Realizability entailment: one realizer `r` transports `P` to `Q` uniformly,
the effectful application `r ⬝ a` producing a realizer of `Q`. -/
def Entails (P Q : RProp) : Prop :=
  ∃ r : Code, ∀ h a, P h a → Produces h (r ⬝ a) Q

end LeanStatefulAoc
