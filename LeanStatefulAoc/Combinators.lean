import Mathlib.Logic.Relation

/-!
# Combinatory algebra of realizers (Layer 1 of the realizability topos)

The realizability topos needs realizers that *apply* to one another — realizers of
`→`/`∀`/`Π` are functions. This file builds the applicative foundation: a small
combinatory calculus `Code` (variables, `K`, `S`, application) with a reduction
relation, and proves **combinatory completeness** (`Code.lam_app`): bracket
abstraction `lam n M` behaves as `λ x_n. M`, i.e. `(lam n M) · N` reduces to
`M[x_n := N]`.

This is the pure core. Effects (`memo`/`alloc`, evaluated into the existing state
monad) and then the realizability tripos are layered on top later. Working with a
reduction relation + (later) fuel — the project's existing style — keeps things
constructive and sidesteps any need for confluence/Church–Rosser.
-/

namespace LeanStatefulAoc

/-- Combinatory terms: variables, the `K` and `S` combinators, and application. -/
inductive Code : Type where
  /-- a variable -/
  | var : Nat → Code
  /-- the `K` combinator (`K x y = x`) -/
  | K : Code
  /-- the `S` combinator (`S x y z = x z (y z)`) -/
  | S : Code
  /-- application -/
  | app : Code → Code → Code
  /-- the memoizing lookup-or-commit operation (`memo ⬝ loc ℓ ⬝ key`) -/
  | memo : Code
  /-- cell allocation (`alloc ⬝ eqcode ⬝ famcode` → a fresh `loc`) -/
  | alloc : Code
  /-- the "true" verdict code (for the eq guard) -/
  | tt : Code
  /-- the "false" verdict code -/
  | ff : Code
  /-- a cell location -/
  | loc : Nat → Code
  /-- pair constructor (`pr ⬝ a ⬝ b`) -/
  | pr : Code
  /-- first projection -/
  | fst : Code
  /-- second projection -/
  | snd : Code
  /-- left injection (`inl ⬝ a`) -/
  | inl : Code
  /-- right injection (`inr ⬝ b`) -/
  | inr : Code
  /-- case analysis (`case ⬝ s ⬝ f ⬝ g`) -/
  | case : Code
  /-- strict sequencing / bind (`seq ⬝ e ⬝ k`: force `e` once, then `k` on its
  value) — the effect-sequencing primitive that lets effectful realizers compose
  without call-by-name duplication -/
  | seq : Code
  deriving DecidableEq

@[inherit_doc] infixl:70 " ⬝ " => Code.app

open Code

/-- The identity combinator `I = S K K` (`I x = x`). -/
def Code.I : Code := S ⬝ K ⬝ K

/-- One-step reduction. -/
inductive Code.Red : Code → Code → Prop
  /-- `K x y → x` -/
  | k {x y} : Code.Red (K ⬝ x ⬝ y) x
  /-- `S x y z → x z (y z)` -/
  | s {x y z} : Code.Red (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  /-- reduce the function part -/
  | appL {f f' x} : Code.Red f f' → Code.Red (f ⬝ x) (f' ⬝ x)
  /-- reduce the argument part -/
  | appR {f x x'} : Code.Red x x' → Code.Red (f ⬝ x) (f ⬝ x')
  /-- `fst (pr a b) → a` -/
  | prL {a b} : Code.Red (fst ⬝ (pr ⬝ a ⬝ b)) a
  /-- `snd (pr a b) → b` -/
  | prR {a b} : Code.Red (snd ⬝ (pr ⬝ a ⬝ b)) b
  /-- `case f g (inl a) → f a` (branches before scrutinee) -/
  | caseL {f g a} : Code.Red (case ⬝ f ⬝ g ⬝ (inl ⬝ a)) (f ⬝ a)
  /-- `case f g (inr b) → g b` -/
  | caseR {f g b} : Code.Red (case ⬝ f ⬝ g ⬝ (inr ⬝ b)) (g ⬝ b)

/-- Multi-step reduction. -/
def Code.Reds : Code → Code → Prop := Relation.ReflTransGen Code.Red

theorem Code.Reds.refl {x : Code} : Code.Reds x x := Relation.ReflTransGen.refl

theorem Code.Reds.single {x y : Code} (h : Code.Red x y) : Code.Reds x y :=
  Relation.ReflTransGen.single h

theorem Code.Reds.trans {x y z : Code} (h₁ : Code.Reds x y) (h₂ : Code.Reds y z) :
    Code.Reds x z := Relation.ReflTransGen.trans h₁ h₂

/-- Multi-step reduction is a congruence in the function position. -/
theorem Code.Reds.appL {f f' : Code} (h : Code.Reds f f') (x : Code) :
    Code.Reds (f ⬝ x) (f' ⬝ x) :=
  Relation.ReflTransGen.lift (· ⬝ x) (fun _ _ => Code.Red.appL) h

/-- Multi-step reduction is a congruence in the argument position. -/
theorem Code.Reds.appR (f : Code) {x x' : Code} (h : Code.Reds x x') :
    Code.Reds (f ⬝ x) (f ⬝ x') :=
  Relation.ReflTransGen.lift (f ⬝ ·) (fun _ _ => Code.Red.appR) h

/-- `I x` reduces to `x`. -/
theorem Code.Reds.i {x : Code} : Code.Reds (I ⬝ x) x :=
  .trans (.single Code.Red.s) (.single Code.Red.k)

/-- Substitution of `var n` by `N`. -/
def Code.subst (n : Nat) (N : Code) : Code → Code
  | var m => if m = n then N else var m
  | app f x => app (Code.subst n N f) (Code.subst n N x)
  | c => c

/-- Bracket abstraction: `lam n M` is `λ x_n. M`, built from `K`, `S`, `I`. -/
def Code.lam (n : Nat) : Code → Code
  | var m => if m = n then I else K ⬝ var m
  | app f x => S ⬝ Code.lam n f ⬝ Code.lam n x
  | c => K ⬝ c

/-- **Combinatory completeness.** `(lam n M) · N` reduces to `M[x_n := N]`, so the
calculus can express every function definable from its variables — the property
that makes it a combinatory algebra and lets us build realizers for `→`/`∀`/`Π`. -/
theorem Code.lam_app (n : Nat) (N : Code) (M : Code) :
    Code.Reds (Code.lam n M ⬝ N) (Code.subst n N M) := by
  induction M with
  | var m =>
    by_cases h : m = n
    · simp only [Code.lam, Code.subst]; rw [if_pos h, if_pos h]
      exact Code.Reds.i
    · simp only [Code.lam, Code.subst]; rw [if_neg h, if_neg h]
      exact Code.Reds.single Code.Red.k
  | app f x ihf ihx =>
    simp only [Code.lam, Code.subst]
    exact .trans (.single Code.Red.s)
      (.trans (Code.Reds.appL ihf _) (Code.Reds.appR _ ihx))
  | _ => simp only [Code.lam, Code.subst]; exact Code.Reds.single Code.Red.k

end LeanStatefulAoc
