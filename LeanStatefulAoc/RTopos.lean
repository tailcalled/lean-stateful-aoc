import LeanStatefulAoc.Combinators
import LeanStatefulAoc.Tripos

/-!
# The realizability topos (Layer 3) — objects and morphisms via tripos-to-topos

The type formers we need — propositional truncation, the dependent product — are
fixed by **universal properties**, which live in the **equality** of objects, and
that equality must see the **world-state**. Two facts pin the construction down:

* Modest sets (PERs directly on codes) form a regular category but **not a topos**
  (no subobject classifier, not closed under quotients). The actual realizability
  topos is the **tripos-to-topos** completion: an object is an *arbitrary carrier
  type* together with a partial equality **valued in the tripos**, which is what
  makes it closed under quotients.
* The tripos here is `RProp`, whose truth values are **heap-indexed**
  (`rel : CHeap → Code → Prop`). Valuing the equality in `RProp` therefore threads
  the world-state through every object and morphism automatically.

So an object is `(carrier, ρ)` with `ρ x y : RProp` a symmetric, transitive (in the
entailment preorder `⟹`) partial equivalence. The diagonal `ρ x x` is the
**existence / extent** predicate `E x`: codes realizing it are the realizers of the
element `x` (at a given heap). A morphism is a tripos-valued **functional relation**
— strict, congruent, single-valued, total — the standard topos-of-a-tripos maps.

This file: the object and morphism structures and the identity morphism. Products,
the subobject classifier, truncation (as image) and `Π` build on top.
-/

namespace LeanStatefulAoc

open Code

/-- An object of the realizability topos (tripos-to-topos over the heap-indexed
tripos `RProp`): a carrier with a tripos-valued partial equality `rel x y` (`ρ`),
symmetric and transitive in the entailment preorder. World-state is threaded
because `RProp` is heap-indexed; `rel x x` is the existence/extent predicate. -/
structure Obj where
  /-- the underlying carrier type -/
  carrier : Type
  /-- `rel x y` (`ρ`): the truth value "`x` equals `y`", heap-indexed -/
  rel : carrier → carrier → RProp
  /-- `ρ` is symmetric -/
  symm : ∀ x y, rel x y ⟹ rel y x
  /-- `ρ` is transitive -/
  trans : ∀ x y z, rel x y ⊓ᵣ rel y z ⟹ rel x z

namespace Obj

/-- Existence / extent predicate `E x = ρ x x`: its realizers are the realizers of
the element `x`. -/
def ext (A : Obj) (x : A.carrier) : RProp := A.rel x x

/-- A related pair has a left extent: `ρ x y ⟹ E x`. -/
theorem rel_ext_left (A : Obj) (x y : A.carrier) : A.rel x y ⟹ A.rel x x :=
  Entails.trans (Entails.and_intro (Entails.refl _) (A.symm x y)) (A.trans x y x)

/-- A related pair has a right extent: `ρ x y ⟹ E y`. -/
theorem rel_ext_right (A : Obj) (x y : A.carrier) : A.rel x y ⟹ A.rel y y :=
  Entails.trans (Entails.and_intro (A.symm x y) (Entails.refl _)) (A.trans y x y)

/-! ### Morphisms (tripos-valued functional relations) -/

/-- A morphism `A ⟶ B`: a tripos-valued relation `rel x y` ("`x` is sent to `y`")
that is strict (defined on existing elements), congruent (respects both
equalities), single-valued, and total. These are the maps of the topos of a
tripos. -/
structure Hom (A B : Obj) where
  /-- the graph of the function, as a heap-indexed truth value -/
  rel : A.carrier → B.carrier → RProp
  /-- strictness in the domain: defined elements exist in `A` -/
  strict_dom : ∀ x y, rel x y ⟹ A.rel x x
  /-- strictness in the codomain: values exist in `B` -/
  strict_cod : ∀ x y, rel x y ⟹ B.rel y y
  /-- congruence: respects the equalities of `A` and `B` -/
  congr : ∀ x x' y y', A.rel x x' ⊓ᵣ B.rel y y' ⊓ᵣ rel x y ⟹ rel x' y'
  /-- single-valued: a point has at most one image -/
  sv : ∀ x y y', rel x y ⊓ᵣ rel x y' ⟹ B.rel y y'
  /-- total: every existing point has an image -/
  total : ∀ x, A.rel x x ⟹ RProp.ex B.carrier (fun y => rel x y)

/-- The identity morphism: its graph is the equality `ρ` itself. -/
def Hom.id (A : Obj) : Hom A A where
  rel := A.rel
  strict_dom := A.rel_ext_left
  strict_cod := A.rel_ext_right
  congr := by
    intro x x' y y'
    have hxx' : A.rel x x' ⊓ᵣ A.rel y y' ⊓ᵣ A.rel x y ⟹ A.rel x x' :=
      Entails.trans (Entails.and_left _ _) (Entails.and_left _ _)
    have hyy' : A.rel x x' ⊓ᵣ A.rel y y' ⊓ᵣ A.rel x y ⟹ A.rel y y' :=
      Entails.trans (Entails.and_left _ _) (Entails.and_right _ _)
    have hxy : A.rel x x' ⊓ᵣ A.rel y y' ⊓ᵣ A.rel x y ⟹ A.rel x y :=
      Entails.and_right _ _
    have hx'x : _ ⟹ A.rel x' x := Entails.trans hxx' (A.symm x x')
    have hx'y : _ ⟹ A.rel x' y :=
      Entails.trans (Entails.and_intro hx'x hxy) (A.trans x' x y)
    exact Entails.trans (Entails.and_intro hx'y hyy') (A.trans x' y y')
  sv := by
    intro x y y'
    have hxy : A.rel x y ⊓ᵣ A.rel x y' ⟹ A.rel x y := Entails.and_left _ _
    have hxy' : A.rel x y ⊓ᵣ A.rel x y' ⟹ A.rel x y' := Entails.and_right _ _
    have hyx : _ ⟹ A.rel y x := Entails.trans hxy (A.symm x y)
    exact Entails.trans (Entails.and_intro hyx hxy') (A.trans y x y')
  total := fun x => Entails.ex_intro (fun y => A.rel x y) x

end Obj

end LeanStatefulAoc
