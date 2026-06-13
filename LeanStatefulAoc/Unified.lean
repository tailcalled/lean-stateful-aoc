import LeanStatefulAoc.Choice
import LeanStatefulAoc.Heyting

/-!
# The headline: one model that validates `AC_dec` and refutes EM

K1 (non-Booleanness) and K2 (`AC_dec`) were each proven in their own bespoke
operational relation. The project's headline, though, is that **one** mutable-state
realizability model validates `AC_dec` *and* in it excluded middle fails. This
file assembles that single relation.

`Realizes C X c` is one Kripke-style realizability relation, over the common
condition space `Cond` (single-valued heaps), interpreting a small object
language `Ty`:

* `atom p` — a monotone proposition (a `KProp`), realizer-irrelevant;
* `or` / `imp` / `falsum` — the intuitionistic connectives (`imp _ falsum` is `¬`),
  with `imp` the standard Kripke clause;
* `choice` — the truncated choice conclusion `‖Π x:A. B x‖`, realized when the
  memoizer (the `AC_dec` program of `C`) produces a generic section.

The **headline theorem** (`headline`) is one statement about this *single*
relation: `choice` is realized at the base condition, while excluded middle
`φ ∨ ¬φ` is not. The two halves reduce to `boolCell_acDec` (K2) and
`undecided_kPhi` (K1) — but now they live in, and are theorems of, the *same*
`Realizes`.

Scope, honestly: this is a *minimal* unified relation — realizer-irrelevant on
the propositional fragment, with `AC_dec`'s premises (decidable equality, the
family) built into the concrete cell `C = boolCell` rather than appearing as
separate `imp` antecedents. It establishes "one Kripke-realizability relation,
both properties," not full MLTT soundness. But it is genuinely one relation, and
it removes the gap that K1 and K2 lived in different ones.
-/

namespace LeanStatefulAoc

universe u v

/-- A small object language hosting both excluded middle and the `AC_dec`
conclusion. -/
inductive Ty (A : Type u) (B : A → Type v) where
  /-- a monotone proposition, realizer-irrelevant -/
  | atom : KProp → Ty A B
  /-- disjunction -/
  | or : Ty A B → Ty A B → Ty A B
  /-- implication (`imp _ falsum` is negation) -/
  | imp : Ty A B → Ty A B → Ty A B
  /-- falsum -/
  | falsum : Ty A B
  /-- the truncated choice conclusion `‖Π x:A. B x‖` -/
  | choice : Ty A B

variable {A : Type u} {B : A → Type v}

/-- The single Kripke-realizability relation, over `Cond`, interpreting `Ty`. -/
def Realizes (C : AcCell A B) : Ty A B → Cond → Prop
  | .atom p, c => p.holds c
  | .or X Y, c => Realizes C X c ∨ Realizes C Y c
  | .imp X Y, c => ∀ c', c ≤ c' → Realizes C X c' → Realizes C Y c'
  | .falsum, _ => False
  | .choice, c => ∃ s : Step V₀ c.1, run isTrue₀ 2 C.acDecProg c.1 = some s ∧
      C.ValidAt c.1.length s.next ∧ C.GenericSection c.1.length

/-- Excluded middle for the generic `φ`, as an object-language formula. -/
def emFormula : Ty ℕ (fun _ => Bool) :=
  .or (.atom kPhi) (.imp (.atom kPhi) .falsum)

/-- **The headline.** In the *single* relation `Realizes boolCell`, over the
common condition space, the truncated `AC_dec` conclusion is realized at the base
condition, while excluded middle `φ ∨ ¬φ` is not. One model; `AC_dec` holds and
EM fails. -/
theorem headline :
    Realizes boolCell Ty.choice base ∧ ¬ Realizes boolCell emFormula base := by
  refine ⟨?_, ?_⟩
  · -- `choice` is realized (K2, via the memoizer of `boolCell`)
    obtain ⟨s, hrun, -, hv, hgs⟩ := boolCell_acDec base.1
    exact ⟨s, hrun, hv, hgs⟩
  · -- excluded middle is not realized (K1: `φ` is undecided at the base)
    rintro (hphi | hneg)
    · exact KProp.undecided_kPhi.1 hphi
    · exact KProp.undecided_kPhi.2 hneg

end LeanStatefulAoc
