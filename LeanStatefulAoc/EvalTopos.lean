import LeanStatefulAoc.EvalTripos

set_option linter.style.longLine false

/-!
# The realizability topos over the stateful PCA `(Code, eval)`

Layer 3, re-based: the tripos-to-topos construction, but over the **effectful** entailment
`Produces` (application is `eval`) rather than pure `Reds`. A fiber predicate `Pred X` is a
heap-indexed realizer family per `x : X`; the fiber order `PLe` (`⊢ₚ`) is a single realizer,
uniform over the carrier and heap, that *produces* a target realizer. Objects are
`EProp`-valued partial equivalence relations; morphisms are functional relations.

The fiber lemmas reuse the realizer-explicit cores from `EvalTripos` (`compProduces`,
`pairProduces`) so the effectful composition/pairing is proved once.
-/

namespace LeanStatefulAoc

namespace Eval

open Code

/-- A predicate over a carrier: the fiber `P(X)` of the realizability tripos. -/
abbrev Pred (X : Type) := X → EProp

/-- Uniform entailment in the fiber `P(X)`: one realizer, uniform over `X` and the heap,
that produces a target realizer. The order making `P` a tripos. -/
def PLe {X : Type} (φ ψ : Pred X) : Prop :=
  ∃ r : Code, ∀ x h a, (φ x).rel h a → (ψ x).Produces h (r ⬝ a)

@[inherit_doc] scoped infix:50 " ⊢ₚ " => PLe

theorem PLe.refl {X : Type} (φ : Pred X) : φ ⊢ₚ φ :=
  ⟨Code.I, fun x _ _ ha => by
    obtain ⟨h', v, hev, hv⟩ := (φ x).ev ha
    exact ⟨h', v, Evaluates.I hev, hv⟩⟩

theorem PLe.trans {X : Type} {φ ψ χ : Pred X} (h₁ : φ ⊢ₚ ψ) (h₂ : ψ ⊢ₚ χ) : φ ⊢ₚ χ := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨Code.compR r₂ r₁, fun x h a ha =>
    EProp.compProduces (fun h' a' => hr₁ x h' a') (fun h' a' => hr₂ x h' a') h a ha⟩

/-- Reindexing along `f : Y → X` (the substitution functor `P(f)`): same realizer. -/
theorem PLe.reindex {X Y : Type} {φ ψ : Pred X} (f : Y → X) (h : φ ⊢ₚ ψ) :
    (fun y => φ (f y)) ⊢ₚ (fun y => ψ (f y)) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun y => hr (f y)⟩

/-- Pointwise first projection (uniform realizer `fst`). -/
theorem PLe.and_left {X : Type} (φ ψ : Pred X) : (fun x => φ x ⊓ₑ ψ x) ⊢ₚ φ :=
  ⟨Code.fst, by rintro x h a ⟨p, q, rfl, hp, _⟩; exact ⟨h, p, Evaluates.fstβ, hp⟩⟩

/-- Pointwise second projection (uniform realizer `snd`). -/
theorem PLe.and_right {X : Type} (φ ψ : Pred X) : (fun x => φ x ⊓ₑ ψ x) ⊢ₚ ψ :=
  ⟨Code.snd, by rintro x h a ⟨p, q, rfl, _, hq⟩; exact ⟨h, q, Evaluates.sndβ, hq⟩⟩

/-- Pointwise effectful pairing (uniform realizer `pairR r₁ r₂`). -/
theorem PLe.and_intro {X : Type} {ρ φ ψ : Pred X} (h₁ : ρ ⊢ₚ φ) (h₂ : ρ ⊢ₚ ψ) :
    ρ ⊢ₚ (fun x => φ x ⊓ₑ ψ x) := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨Code.pairR r₁ r₂, fun x h a ha =>
    EProp.pairProduces (fun h' a' => hr₁ x h' a') (fun h' a' => hr₂ x h' a') h a ha⟩

/-- Existential introduction at a chosen witness `w x` (uniform realizer `I`). -/
theorem PLe.ex_intro {X I : Type} (φ : X → I → EProp) (w : X → I) :
    (fun x => φ x (w x)) ⊢ₚ (fun x => EProp.ex I (fun i => φ x i)) :=
  ⟨Code.I, fun x _ _ ha => by
    obtain ⟨h', v, hev, hv⟩ := (φ x (w x)).ev ha
    exact ⟨h', v, Evaluates.I hev, w x, hv⟩⟩

/-- Existential elimination: map out of `∃ i, φ x i` into an `i`-independent target by
mapping out of `φ x i` uniformly (same realizer — `∃` keeps it). -/
theorem PLe.ex_elim {X I : Type} {φ : X → I → EProp} {ψ : Pred X}
    (h : (fun p : X × I => φ p.1 p.2) ⊢ₚ (fun p => ψ p.1)) :
    (fun x => EProp.ex I (fun i => φ x i)) ⊢ₚ ψ := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun x hh a ⟨i, hi⟩ => hr (x, i) hh a hi⟩

/-- Existential monotonicity: a uniform map on the bodies lifts to the `∃`s. -/
theorem PLe.ex_mono {X I : Type} {φ ψ : X → I → EProp}
    (h : (fun p : X × I => φ p.1 p.2) ⊢ₚ (fun p => ψ p.1 p.2)) :
    (fun x => EProp.ex I (fun i => φ x i)) ⊢ₚ (fun x => EProp.ex I (fun i => ψ x i)) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, fun x hh a ⟨i, hi⟩ => ?_⟩
  obtain ⟨h', v, hev, hv⟩ := hr (x, i) hh a hi
  exact ⟨h', v, hev, i, hv⟩

/-- Left injection into a fiberwise coproduct (uniform realizer `inl`). -/
theorem PLe.inl {X : Type} (φ ψ : Pred X) : φ ⊢ₚ (fun x => φ x ⊔ₑ ψ x) :=
  ⟨Code.inl, fun _ h a ha => ⟨h, Code.inl ⬝ a, Evaluates.inlVal, Or.inl ⟨a, rfl, ha⟩⟩⟩

/-- Right injection into a fiberwise coproduct (uniform realizer `inr`). -/
theorem PLe.inr {X : Type} (φ ψ : Pred X) : ψ ⊢ₚ (fun x => φ x ⊔ₑ ψ x) :=
  ⟨Code.inr, fun _ h a ha => ⟨h, Code.inr ⬝ a, Evaluates.inrVal, Or.inr ⟨a, rfl, ha⟩⟩⟩

/-- Frobenius reciprocity: `ρ ⊓ ∃ i. φ i ⊢ ∃ i. (ρ ⊓ φ i)` (realizer `I`: the pair is reused). -/
theorem PLe.frobenius {X I : Type} (ρ : Pred X) (φ : X → I → EProp) :
    (fun x => ρ x ⊓ₑ EProp.ex I (fun i => φ x i)) ⊢ₚ
      (fun x => EProp.ex I (fun i => ρ x ⊓ₑ φ x i)) := by
  refine ⟨Code.I, fun x h a ha => ?_⟩
  obtain ⟨p, e, rfl, hp, i, hi⟩ := ha
  exact ⟨h, pr ⬝ p ⬝ e, Evaluates.I Evaluates.prVal, i, p, e, rfl, hp, hi⟩

/-- A conjunction of two existentials pulls out to a double existential (realizer `I`). -/
theorem PLe.ex_and_ex {X I J : Type} (φ : X → I → EProp) (ψ : X → J → EProp) :
    (fun x => EProp.ex I (fun i => φ x i) ⊓ₑ EProp.ex J (fun j => ψ x j)) ⊢ₚ
      (fun x => EProp.ex I (fun i => EProp.ex J (fun j => φ x i ⊓ₑ ψ x j))) := by
  refine ⟨Code.I, fun x h a ha => ?_⟩
  obtain ⟨p, q, rfl, ⟨i, hp⟩, j, hq⟩ := ha
  exact ⟨h, pr ⬝ p ⬝ q, Evaluates.I Evaluates.prVal, i, j, p, q, rfl, hp, hq⟩

/-! ### Objects -/

/-- An object of the realizability topos: a carrier with an `EProp`-valued partial
equivalence relation `rel x y` (`ρ`), symmetric and transitive **uniformly**. -/
structure Obj where
  /-- the underlying carrier type -/
  carrier : Type
  /-- `rel x y` (`ρ`): the heap-indexed truth value "`x` equals `y`" -/
  rel : carrier → carrier → EProp
  /-- `ρ` is symmetric (uniformly) -/
  symm : (fun p : carrier × carrier => rel p.1 p.2) ⊢ₚ (fun p => rel p.2 p.1)
  /-- `ρ` is transitive (uniformly) -/
  trans : (fun p : carrier × carrier × carrier => rel p.1 p.2.1 ⊓ₑ rel p.2.1 p.2.2)
            ⊢ₚ (fun p => rel p.1 p.2.2)

namespace Obj

/-- Existence / extent predicate `E x = ρ x x`. -/
def ext (A : Obj) (x : A.carrier) : EProp := A.rel x x

/-- Left extent, uniformly: `ρ x y ⊢ E x`. -/
theorem rel_ext_left (A : Obj) :
    (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ (fun p => A.rel p.1 p.1) := by
  have hand : (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ
      (fun p => A.rel p.1 p.2 ⊓ₑ A.rel p.2 p.1) := PLe.and_intro (PLe.refl _) A.symm
  have htr := PLe.reindex (fun p : A.carrier × A.carrier => (p.1, p.2, p.1)) A.trans
  exact PLe.trans hand htr

/-- Right extent, uniformly: `ρ x y ⊢ E y`. -/
theorem rel_ext_right (A : Obj) :
    (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ (fun p => A.rel p.2 p.2) := by
  have hand : (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ
      (fun p => A.rel p.2 p.1 ⊓ₑ A.rel p.1 p.2) := PLe.and_intro A.symm (PLe.refl _)
  have htr := PLe.reindex (fun p : A.carrier × A.carrier => (p.2, p.1, p.2)) A.trans
  exact PLe.trans hand htr

end Obj

/-! ### Morphisms (tripos-valued functional relations) -/

/-- A morphism `A ⟶ B`: an `EProp`-valued relation `rel x y` that is strict, congruent,
single-valued, and total — all **uniformly**. -/
structure Hom (A B : Obj) where
  /-- the graph of the function, as a heap-indexed truth value -/
  rel : A.carrier → B.carrier → EProp
  /-- strict in the domain -/
  strict_dom : (fun p : A.carrier × B.carrier => rel p.1 p.2) ⊢ₚ (fun p => A.rel p.1 p.1)
  /-- strict in the codomain -/
  strict_cod : (fun p : A.carrier × B.carrier => rel p.1 p.2) ⊢ₚ (fun p => B.rel p.2 p.2)
  /-- congruent: respects both equalities -/
  congr : (fun p : A.carrier × A.carrier × B.carrier × B.carrier =>
            A.rel p.1 p.2.1 ⊓ₑ B.rel p.2.2.1 p.2.2.2 ⊓ₑ rel p.1 p.2.2.1)
            ⊢ₚ (fun p => rel p.2.1 p.2.2.2)
  /-- single-valued -/
  sv : (fun p : A.carrier × B.carrier × B.carrier => rel p.1 p.2.1 ⊓ₑ rel p.1 p.2.2)
        ⊢ₚ (fun p => B.rel p.2.1 p.2.2)
  /-- total -/
  total : (fun x : A.carrier => A.rel x x) ⊢ₚ (fun x => EProp.ex B.carrier (fun y => rel x y))

/-- The identity morphism: its graph is the equality `ρ` itself. -/
def Hom.id (A : Obj) : Hom A A where
  rel := A.rel
  strict_dom := A.rel_ext_left
  strict_cod := A.rel_ext_right
  total := PLe.ex_intro (fun x y => A.rel x y) (fun x => x)
  congr := by
    have h_xx' := PLe.trans
      (PLe.and_left (X := A.carrier × A.carrier × A.carrier × A.carrier)
        (fun p => A.rel p.1 p.2.1 ⊓ₑ A.rel p.2.2.1 p.2.2.2) (fun p => A.rel p.1 p.2.2.1))
      (PLe.and_left (fun p : A.carrier × A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1)
        (fun p => A.rel p.2.2.1 p.2.2.2))
    have h_yy' := PLe.trans
      (PLe.and_left (X := A.carrier × A.carrier × A.carrier × A.carrier)
        (fun p => A.rel p.1 p.2.1 ⊓ₑ A.rel p.2.2.1 p.2.2.2) (fun p => A.rel p.1 p.2.2.1))
      (PLe.and_right (fun p : A.carrier × A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1)
        (fun p => A.rel p.2.2.1 p.2.2.2))
    have h_xy := PLe.and_right
      (fun p : A.carrier × A.carrier × A.carrier × A.carrier =>
        A.rel p.1 p.2.1 ⊓ₑ A.rel p.2.2.1 p.2.2.2)
      (fun p => A.rel p.1 p.2.2.1)
    have h_x'x := PLe.trans h_xx'
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier × A.carrier => (p.1, p.2.1)) A.symm)
    have h_x'y := PLe.trans (PLe.and_intro h_x'x h_xy)
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier × A.carrier =>
        (p.2.1, p.1, p.2.2.1)) A.trans)
    exact PLe.trans (PLe.and_intro h_x'y h_yy')
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier × A.carrier =>
        (p.2.1, p.2.2.1, p.2.2.2)) A.trans)
  sv := by
    have h_xy := PLe.and_left
      (fun p : A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1) (fun p => A.rel p.1 p.2.2)
    have h_xy' := PLe.and_right
      (fun p : A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1) (fun p => A.rel p.1 p.2.2)
    have h_yx := PLe.trans h_xy
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier => (p.1, p.2.1)) A.symm)
    exact PLe.trans (PLe.and_intro h_yx h_xy')
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier => (p.2.1, p.1, p.2.2)) A.trans)

/-- Composition of morphisms: the relational composite `(G ∘ F) x z = ∃ y, F x y ⊓ G y z`. -/
def Hom.comp {A B C : Obj} (F : Hom A B) (G : Hom B C) : Hom A C where
  rel x z := EProp.ex B.carrier (fun y => F.rel x y ⊓ₑ G.rel y z)
  strict_dom := by
    apply PLe.ex_elim
    exact PLe.trans
      (PLe.and_left (fun q : (A.carrier × C.carrier) × B.carrier => F.rel q.1.1 q.2)
        (fun q => G.rel q.2 q.1.2))
      (PLe.reindex (fun q : (A.carrier × C.carrier) × B.carrier => (q.1.1, q.2)) F.strict_dom)
  strict_cod := by
    apply PLe.ex_elim
    exact PLe.trans
      (PLe.and_right (fun q : (A.carrier × C.carrier) × B.carrier => F.rel q.1.1 q.2)
        (fun q => G.rel q.2 q.1.2))
      (PLe.reindex (fun q : (A.carrier × C.carrier) × B.carrier => (q.2, q.1.2)) G.strict_cod)
  total := by
    have hGtot : (fun p : A.carrier × B.carrier => F.rel p.1 p.2) ⊢ₚ
        (fun p => EProp.ex C.carrier (fun z => G.rel p.2 z)) :=
      PLe.trans F.strict_cod (PLe.reindex (fun p : A.carrier × B.carrier => p.2) G.total)
    have hinner : (fun q : (A.carrier × B.carrier) × C.carrier =>
          F.rel q.1.1 q.1.2 ⊓ₑ G.rel q.1.2 q.2) ⊢ₚ
        (fun q => EProp.ex B.carrier (fun y => F.rel q.1.1 y ⊓ₑ G.rel y q.2)) :=
      PLe.ex_intro
        (fun q : (A.carrier × B.carrier) × C.carrier =>
          fun y => F.rel q.1.1 y ⊓ₑ G.rel y q.2)
        (fun q => q.1.2)
    have hyp : (fun p : A.carrier × B.carrier => F.rel p.1 p.2) ⊢ₚ
        (fun p => EProp.ex C.carrier (fun z =>
          EProp.ex B.carrier (fun y => F.rel p.1 y ⊓ₑ G.rel y z))) :=
      PLe.trans (PLe.and_intro (PLe.refl _) hGtot)
        (PLe.trans (PLe.frobenius (fun p : A.carrier × B.carrier => F.rel p.1 p.2)
          (fun p z => G.rel p.2 z)) (PLe.ex_mono hinner))
    exact PLe.trans F.total (PLe.ex_elim hyp)
  sv := by
    refine PLe.trans (PLe.ex_and_ex
      (fun p : A.carrier × C.carrier × C.carrier => fun y => F.rel p.1 y ⊓ₑ G.rel y p.2.1)
      (fun p : A.carrier × C.carrier × C.carrier => fun y => F.rel p.1 y ⊓ₑ G.rel y p.2.2)) ?_
    apply PLe.ex_elim
    apply PLe.ex_elim
    have hFxy : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ₑ G.rel q.1.2 q.1.1.2.1) ⊓ₑ
          (F.rel q.1.1.1 q.2 ⊓ₑ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => F.rel q.1.1.1 q.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hGyz1 : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ₑ G.rel q.1.2 q.1.1.2.1) ⊓ₑ
          (F.rel q.1.1.1 q.2 ⊓ₑ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => G.rel q.1.2 q.1.1.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hFxy' : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ₑ G.rel q.1.2 q.1.1.2.1) ⊓ₑ
          (F.rel q.1.1.1 q.2 ⊓ₑ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => F.rel q.1.1.1 q.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hGy'z2 : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ₑ G.rel q.1.2 q.1.1.2.1) ⊓ₑ
          (F.rel q.1.1.1 q.2 ⊓ₑ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => G.rel q.2 q.1.1.2.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_right _ _)
    have hyy' := PLe.trans (PLe.and_intro hFxy hFxy')
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.1.1.1, q.1.2, q.2)) F.sv)
    have hCz2 := PLe.trans hGy'z2
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.2, q.1.1.2.2)) G.strict_cod)
    have hy'y := PLe.trans hyy'
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.1.2, q.2)) B.symm)
    have hGyz2 := PLe.trans (PLe.and_intro (PLe.and_intro hy'y hCz2) hGy'z2)
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.2, q.1.2, q.1.1.2.2, q.1.1.2.2)) G.congr)
    exact PLe.trans (PLe.and_intro hGyz1 hGyz2)
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.1.2, q.1.1.2.1, q.1.1.2.2)) G.sv)
  congr := by
    refine PLe.trans (PLe.frobenius
      (fun p : A.carrier × A.carrier × C.carrier × C.carrier =>
        A.rel p.1 p.2.1 ⊓ₑ C.rel p.2.2.1 p.2.2.2)
      (fun p => fun y => F.rel p.1 y ⊓ₑ G.rel y p.2.2.1)) ?_
    apply PLe.ex_elim
    have hAxx' : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ₑ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ₑ
          (F.rel q.1.1 q.2 ⊓ₑ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => A.rel q.1.1 q.1.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hCzz' : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ₑ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ₑ
          (F.rel q.1.1 q.2 ⊓ₑ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => C.rel q.1.2.2.1 q.1.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hFxy : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ₑ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ₑ
          (F.rel q.1.1 q.2 ⊓ₑ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => F.rel q.1.1 q.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hGyz : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ₑ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ₑ
          (F.rel q.1.1 q.2 ⊓ₑ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => G.rel q.2 q.1.2.2.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_right _ _)
    have hByy := PLe.trans hFxy
      (PLe.reindex (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (q.1.1, q.2)) F.strict_cod)
    have hFx'y := PLe.trans (PLe.and_intro (PLe.and_intro hAxx' hByy) hFxy)
      (PLe.reindex (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (q.1.1, q.1.2.1, q.2, q.2)) F.congr)
    have hGyz' := PLe.trans (PLe.and_intro (PLe.and_intro hByy hCzz') hGyz)
      (PLe.reindex (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (q.2, q.2, q.1.2.2.1, q.1.2.2.2)) G.congr)
    exact PLe.trans (PLe.and_intro hFx'y hGyz')
      (PLe.ex_intro
        (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
          fun y' => F.rel q.1.2.1 y' ⊓ₑ G.rel y' q.1.2.2.2)
        (fun q => q.2))

/-- Equality of parallel morphisms: their graphs mutually entail. -/
def HomEq {A B : Obj} (F G : Hom A B) : Prop :=
  ((fun p : A.carrier × B.carrier => F.rel p.1 p.2) ⊢ₚ (fun p => G.rel p.1 p.2)) ∧
    ((fun p : A.carrier × B.carrier => G.rel p.1 p.2) ⊢ₚ (fun p => F.rel p.1 p.2))

/-- Left identity law: `id ∘ F = F`. -/
theorem Hom.id_comp {A B : Obj} (F : Hom A B) : HomEq (Hom.comp (Hom.id A) F) F := by
  constructor
  · apply PLe.ex_elim
    have hAxy : (fun q : (A.carrier × B.carrier) × A.carrier =>
        A.rel q.1.1 q.2 ⊓ₑ F.rel q.2 q.1.2) ⊢ₚ (fun q => A.rel q.1.1 q.2) := PLe.and_left _ _
    have hFyz : (fun q : (A.carrier × B.carrier) × A.carrier =>
        A.rel q.1.1 q.2 ⊓ₑ F.rel q.2 q.1.2) ⊢ₚ (fun q => F.rel q.2 q.1.2) := PLe.and_right _ _
    have hAyx := PLe.trans hAxy
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier => (q.1.1, q.2)) A.symm)
    have hBzz := PLe.trans hFyz
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier => (q.2, q.1.2)) F.strict_cod)
    exact PLe.trans (PLe.and_intro (PLe.and_intro hAyx hBzz) hFyz)
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier =>
        (q.2, q.1.1, q.1.2, q.1.2)) F.congr)
  · exact PLe.trans (PLe.and_intro F.strict_dom (PLe.refl _))
      (PLe.ex_intro (fun p : A.carrier × B.carrier => fun y => A.rel p.1 y ⊓ₑ F.rel y p.2)
        (fun p => p.1))

/-- Right identity law: `F ∘ id = F`. -/
theorem Hom.comp_id {A B : Obj} (F : Hom A B) : HomEq (Hom.comp F (Hom.id B)) F := by
  constructor
  · apply PLe.ex_elim
    have hFxy : (fun q : (A.carrier × B.carrier) × B.carrier =>
        F.rel q.1.1 q.2 ⊓ₑ B.rel q.2 q.1.2) ⊢ₚ (fun q => F.rel q.1.1 q.2) := PLe.and_left _ _
    have hByz : (fun q : (A.carrier × B.carrier) × B.carrier =>
        F.rel q.1.1 q.2 ⊓ₑ B.rel q.2 q.1.2) ⊢ₚ (fun q => B.rel q.2 q.1.2) := PLe.and_right _ _
    have hAxx := PLe.trans hFxy
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier => (q.1.1, q.2)) F.strict_dom)
    exact PLe.trans (PLe.and_intro (PLe.and_intro hAxx hByz) hFxy)
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier =>
        (q.1.1, q.1.1, q.2, q.1.2)) F.congr)
  · exact PLe.trans (PLe.and_intro (PLe.refl _) F.strict_cod)
      (PLe.ex_intro (fun p : A.carrier × B.carrier => fun y => F.rel p.1 y ⊓ₑ B.rel y p.2)
        (fun p => p.2))

/-- Uncurry a double existential into one over the product index (realizer `I`). -/
theorem PLe.ex_pair {X I J : Type} (φ : X → I → J → EProp) :
    (fun x => EProp.ex I (fun i => EProp.ex J (fun j => φ x i j))) ⊢ₚ
      (fun x => EProp.ex (I × J) (fun p => φ x p.1 p.2)) := by
  refine ⟨Code.I, fun x h a ha => ?_⟩
  obtain ⟨i, j, hij⟩ := ha
  obtain ⟨h', v, hev, hv⟩ := (φ x i j).ev hij
  exact ⟨h', v, Evaluates.I hev, (i, j), hv⟩

/-! ### Binary products -/

def prod (A B : Obj) : Obj where
  carrier := A.carrier × B.carrier
  rel p q := A.rel p.1 q.1 ⊓ₑ B.rel p.2 q.2
  symm := by
    have hA := PLe.trans
      (PLe.and_left (fun p : (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.1.1 p.2.1) (fun p => B.rel p.1.2 p.2.2))
      (PLe.reindex (fun p : (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (p.1.1, p.2.1)) A.symm)
    have hB := PLe.trans
      (PLe.and_right (fun p : (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.1.1 p.2.1) (fun p => B.rel p.1.2 p.2.2))
      (PLe.reindex (fun p : (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (p.1.2, p.2.2)) B.symm)
    exact PLe.and_intro hA hB
  trans := by
    have hA1 := PLe.trans
      (PLe.and_left (X := (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier)
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ₑ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ₑ B.rel p.2.1.2 p.2.2.2))
      (PLe.and_left (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.1.1 p.2.1.1) (fun p => B.rel p.1.2 p.2.1.2))
    have hA2 := PLe.trans
      (PLe.and_right (X := (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier)
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ₑ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ₑ B.rel p.2.1.2 p.2.2.2))
      (PLe.and_left (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.2.1.1 p.2.2.1) (fun p => B.rel p.2.1.2 p.2.2.2))
    have hB1 := PLe.trans
      (PLe.and_left (X := (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier)
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ₑ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ₑ B.rel p.2.1.2 p.2.2.2))
      (PLe.and_right (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.1.1 p.2.1.1) (fun p => B.rel p.1.2 p.2.1.2))
    have hB2 := PLe.trans
      (PLe.and_right (X := (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier)
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ₑ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ₑ B.rel p.2.1.2 p.2.2.2))
      (PLe.and_right (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.2.1.1 p.2.2.1) (fun p => B.rel p.2.1.2 p.2.2.2))
    have hA := PLe.trans (PLe.and_intro hA1 hA2)
      (PLe.reindex (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (p.1.1, p.2.1.1, p.2.2.1)) A.trans)
    have hB := PLe.trans (PLe.and_intro hB1 hB2)
      (PLe.reindex (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (p.1.2, p.2.1.2, p.2.2.2)) B.trans)
    exact PLe.and_intro hA hB

/-- First projection `π₁ : A × B ⟶ A`. -/
def Hom.fst (A B : Obj) : Hom (prod A B) A where
  rel p a' := A.rel p.1 a' ⊓ₑ B.rel p.2 p.2
  strict_dom := by
    have hA := PLe.trans
      (PLe.and_left (fun q : (A.carrier × B.carrier) × A.carrier => A.rel q.1.1 q.2)
        (fun q => B.rel q.1.2 q.1.2))
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier => (q.1.1, q.2)) A.rel_ext_left)
    have hB := PLe.and_right
      (fun q : (A.carrier × B.carrier) × A.carrier => A.rel q.1.1 q.2) (fun q => B.rel q.1.2 q.1.2)
    exact PLe.and_intro hA hB
  strict_cod := PLe.trans
    (PLe.and_left (fun q : (A.carrier × B.carrier) × A.carrier => A.rel q.1.1 q.2)
      (fun q => B.rel q.1.2 q.1.2))
    (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier => (q.1.1, q.2)) A.rel_ext_right)
  congr := by
    -- q : (A×B)×(A×B)×A×A ; p=q.1, p'=q.2.1, a'=q.2.2.1, a''=q.2.2.2
    have hpp'A : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ A.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (A.rel q.1.1 q.2.2.1 ⊓ₑ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.1.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_left _ _))
    have hBpp' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ A.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (A.rel q.1.1 q.2.2.1 ⊓ₑ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => B.rel q.1.2 q.2.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_right _ _))
    have ha'a'' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ A.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (A.rel q.1.1 q.2.2.1 ⊓ₑ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.2.2.1 q.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hpa' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ A.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (A.rel q.1.1 q.2.2.1 ⊓ₑ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.2.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    -- A.rel p'.1 a''
    have hp'p := PLe.trans hpp'A
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.1.1, q.2.1.1)) A.symm)
    have hp'a' := PLe.trans (PLe.and_intro hp'p hpa')
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.2.1.1, q.1.1, q.2.2.1)) A.trans)
    have hp'a'' := PLe.trans (PLe.and_intro hp'a' ha'a'')
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.2.1.1, q.2.2.1, q.2.2.2)) A.trans)
    -- B.rel p'.2 p'.2
    have hBp' := PLe.trans hBpp'
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.1.2, q.2.1.2)) B.rel_ext_right)
    exact PLe.and_intro hp'a'' hBp'
  sv := by
    -- q : (A×B)×A×A ; p=q.1, a'=q.2.1, a''=q.2.2
    have hpa' : (fun q : (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1 ⊓ₑ B.rel q.1.2 q.1.2) ⊓ₑ
          (A.rel q.1.1 q.2.2 ⊓ₑ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hpa'' : (fun q : (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1 ⊓ₑ B.rel q.1.2 q.1.2) ⊓ₑ
          (A.rel q.1.1 q.2.2 ⊓ₑ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have ha'p := PLe.trans hpa'
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.1.1, q.2.1)) A.symm)
    exact PLe.trans (PLe.and_intro ha'p hpa'')
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.2.1, q.1.1, q.2.2)) A.trans)
  total := PLe.ex_intro
    (fun (p : A.carrier × B.carrier) => fun a' => A.rel p.1 a' ⊓ₑ B.rel p.2 p.2) (fun p => p.1)

/-- Second projection `π₂ : A × B ⟶ B`. -/
def Hom.snd (A B : Obj) : Hom (prod A B) B where
  rel p b' := B.rel p.2 b' ⊓ₑ A.rel p.1 p.1
  strict_dom := by
    have hB := PLe.trans
      (PLe.and_left (fun q : (A.carrier × B.carrier) × B.carrier => B.rel q.1.2 q.2)
        (fun q => A.rel q.1.1 q.1.1))
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier => (q.1.2, q.2)) B.rel_ext_left)
    have hA := PLe.and_right
      (fun q : (A.carrier × B.carrier) × B.carrier => B.rel q.1.2 q.2) (fun q => A.rel q.1.1 q.1.1)
    -- need (prod A B).rel p p = A.rel p.1 p.1 ⊓ₑ B.rel p.2 p.2
    exact PLe.and_intro hA hB
  strict_cod := PLe.trans
    (PLe.and_left (fun q : (A.carrier × B.carrier) × B.carrier => B.rel q.1.2 q.2)
      (fun q => A.rel q.1.1 q.1.1))
    (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier => (q.1.2, q.2)) B.rel_ext_right)
  congr := by
    have hpp'B : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ B.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (B.rel q.1.2 q.2.2.1 ⊓ₑ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_right _ _))
    have hApp' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ B.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (B.rel q.1.2 q.2.2.1 ⊓ₑ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => A.rel q.1.1 q.2.1.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_left _ _))
    have hb'b'' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ B.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (B.rel q.1.2 q.2.2.1 ⊓ₑ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.2.2.1 q.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hpb' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ₑ B.rel q.1.2 q.2.1.2 ⊓ₑ B.rel q.2.2.1 q.2.2.2) ⊓ₑ
          (B.rel q.1.2 q.2.2.1 ⊓ₑ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.2.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hp'p := PLe.trans hpp'B
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (q.1.2, q.2.1.2)) B.symm)
    have hp'b' := PLe.trans (PLe.and_intro hp'p hpb')
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (q.2.1.2, q.1.2, q.2.2.1)) B.trans)
    have hp'b'' := PLe.trans (PLe.and_intro hp'b' hb'b'')
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (q.2.1.2, q.2.2.1, q.2.2.2)) B.trans)
    have hAp' := PLe.trans hApp'
      (PLe.reindex (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (q.1.1, q.2.1.1)) A.rel_ext_right)
    exact PLe.and_intro hp'b'' hAp'
  sv := by
    have hpb' : (fun q : (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (B.rel q.1.2 q.2.1 ⊓ₑ A.rel q.1.1 q.1.1) ⊓ₑ
          (B.rel q.1.2 q.2.2 ⊓ₑ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hpb'' : (fun q : (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (B.rel q.1.2 q.2.1 ⊓ₑ A.rel q.1.1 q.1.1) ⊓ₑ
          (B.rel q.1.2 q.2.2 ⊓ₑ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hb'p := PLe.trans hpb'
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (q.1.2, q.2.1)) B.symm)
    exact PLe.trans (PLe.and_intro hb'p hpb'')
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (q.2.1, q.1.2, q.2.2)) B.trans)
  total := PLe.trans
    (PLe.and_intro
      (PLe.and_right (fun p : A.carrier × B.carrier => A.rel p.1 p.1) (fun p => B.rel p.2 p.2))
      (PLe.and_left (fun p : A.carrier × B.carrier => A.rel p.1 p.1) (fun p => B.rel p.2 p.2)))
    (PLe.ex_intro
      (fun (p : A.carrier × B.carrier) => fun b' => B.rel p.2 b' ⊓ₑ A.rel p.1 p.1) (fun p => p.2))

/-- Pairing `⟨f, g⟩ : C ⟶ A × B`, the universal map into the product. -/
def Hom.pair {C A B : Obj} (f : Hom C A) (g : Hom C B) : Hom C (prod A B) where
  rel c p := f.rel c p.1 ⊓ₑ g.rel c p.2
  strict_dom := PLe.trans
    (PLe.and_left (fun w : C.carrier × A.carrier × B.carrier => f.rel w.1 w.2.1)
      (fun w => g.rel w.1 w.2.2))
    (PLe.reindex (fun w : C.carrier × A.carrier × B.carrier => (w.1, w.2.1)) f.strict_dom)
  strict_cod := by
    have hA := PLe.trans
      (PLe.and_left (fun w : C.carrier × A.carrier × B.carrier => f.rel w.1 w.2.1)
        (fun w => g.rel w.1 w.2.2))
      (PLe.reindex (fun w : C.carrier × A.carrier × B.carrier => (w.1, w.2.1)) f.strict_cod)
    have hB := PLe.trans
      (PLe.and_right (fun w : C.carrier × A.carrier × B.carrier => f.rel w.1 w.2.1)
        (fun w => g.rel w.1 w.2.2))
      (PLe.reindex (fun w : C.carrier × A.carrier × B.carrier => (w.1, w.2.2)) g.strict_cod)
    exact PLe.and_intro hA hB
  congr := by
    -- q : C×C×(A×B)×(A×B) ; c=q.1 c'=q.2.1 (a,b)=q.2.2.1 (a',b')=q.2.2.2
    have hCcc' : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ₑ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ₑ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ₑ
          (f.rel q.1 q.2.2.1.1 ⊓ₑ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => C.rel q.1 q.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hAaa' : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ₑ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ₑ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ₑ
          (f.rel q.1 q.2.2.1.1 ⊓ₑ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => A.rel q.2.2.1.1 q.2.2.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_right _ _) (PLe.and_left _ _))
    have hBbb' : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ₑ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ₑ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ₑ
          (f.rel q.1 q.2.2.1.1 ⊓ₑ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => B.rel q.2.2.1.2 q.2.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_right _ _) (PLe.and_right _ _))
    have hfca : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ₑ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ₑ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ₑ
          (f.rel q.1 q.2.2.1.1 ⊓ₑ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => f.rel q.1 q.2.2.1.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hgcb : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ₑ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ₑ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ₑ
          (f.rel q.1 q.2.2.1.1 ⊓ₑ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => g.rel q.1 q.2.2.1.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_right _ _)
    have hf := PLe.trans (PLe.and_intro (PLe.and_intro hCcc' hAaa') hfca)
      (PLe.reindex (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (q.1, q.2.1, q.2.2.1.1, q.2.2.2.1)) f.congr)
    have hg := PLe.trans (PLe.and_intro (PLe.and_intro hCcc' hBbb') hgcb)
      (PLe.reindex (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (q.1, q.2.1, q.2.2.1.2, q.2.2.2.2)) g.congr)
    exact PLe.and_intro hf hg
  sv := by
    -- q : C×(A×B)×(A×B) ; c=q.1 (a,b)=q.2.1 (a',b')=q.2.2
    have hfa : (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (f.rel q.1 q.2.1.1 ⊓ₑ g.rel q.1 q.2.1.2) ⊓ₑ
          (f.rel q.1 q.2.2.1 ⊓ₑ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => f.rel q.1 q.2.1.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hfa' : (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (f.rel q.1 q.2.1.1 ⊓ₑ g.rel q.1 q.2.1.2) ⊓ₑ
          (f.rel q.1 q.2.2.1 ⊓ₑ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => f.rel q.1 q.2.2.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hgb : (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (f.rel q.1 q.2.1.1 ⊓ₑ g.rel q.1 q.2.1.2) ⊓ₑ
          (f.rel q.1 q.2.2.1 ⊓ₑ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => g.rel q.1 q.2.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hgb' : (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (f.rel q.1 q.2.1.1 ⊓ₑ g.rel q.1 q.2.1.2) ⊓ₑ
          (f.rel q.1 q.2.2.1 ⊓ₑ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => g.rel q.1 q.2.2.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_right _ _)
    have hA := PLe.trans (PLe.and_intro hfa hfa')
      (PLe.reindex (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (q.1, q.2.1.1, q.2.2.1)) f.sv)
    have hB := PLe.trans (PLe.and_intro hgb hgb')
      (PLe.reindex (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (q.1, q.2.1.2, q.2.2.2)) g.sv)
    exact PLe.and_intro hA hB
  total := PLe.trans (PLe.and_intro f.total g.total)
    (PLe.trans
      (PLe.ex_and_ex (fun (c : C.carrier) => fun a => f.rel c a)
        (fun (c : C.carrier) => fun b => g.rel c b))
      (PLe.ex_pair (fun (c : C.carrier) => fun a b => f.rel c a ⊓ₑ g.rel c b)))

/-! ### Terminal object, propositions, and truncation -/

/-- The terminal object `1`: a single element, always-true equality. -/
def one : Obj where
  carrier := Unit
  rel _ _ := EProp.top
  symm := PLe.refl _
  trans := PLe.and_left _ _

/-- A proposition (subobject of `1`) presented by a truth value `P`. -/
def prop (P : EProp) : Obj where
  carrier := Unit
  rel _ _ := P
  symm := PLe.refl _
  trans := PLe.and_left _ _

/-- An object is a **proposition** (subsingleton): `E x ⊓ E y ⊢ ρ x y`. -/
def ObjIsProp (Q : Obj) : Prop :=
  (fun p : Q.carrier × Q.carrier => Q.rel p.1 p.1 ⊓ₑ Q.rel p.2 p.2) ⊢ₚ (fun p => Q.rel p.1 p.2)

theorem prop_isProp (P : EProp) : ObjIsProp (prop P) := PLe.and_left _ _

/-- Propositional truncation `‖A‖` = the support of `A`: `∃ x, E_A x` (witness-preserving). -/
def trunc (A : Obj) : Obj := prop (EProp.ex A.carrier (fun x => A.rel x x))

theorem trunc_isProp (A : Obj) : ObjIsProp (trunc A) := prop_isProp _

/-- Swap two existential quantifiers (realizer `I`). -/
theorem PLe.ex_swap {X I J : Type} (φ : X → I → J → EProp) :
    (fun x => EProp.ex I (fun i => EProp.ex J (fun j => φ x i j))) ⊢ₚ
      (fun x => EProp.ex J (fun j => EProp.ex I (fun i => φ x i j))) := by
  refine ⟨Code.I, fun x h a ⟨i, j, hij⟩ => ?_⟩
  obtain ⟨h', v, hev, hv⟩ := (φ x i j).ev hij
  exact ⟨h', v, Evaluates.I hev, j, i, hv⟩

/-- The truncation unit `η : A ⟶ ‖A‖`. -/
def Hom.toTrunc (A : Obj) : Hom A (trunc A) where
  rel x _ := A.rel x x
  strict_dom := PLe.refl _
  strict_cod :=
    PLe.ex_intro (fun (p : A.carrier × Unit) => fun x => A.rel x x) (fun p => p.1)
  congr := by
    have hxx' : (fun p : A.carrier × A.carrier × Unit × Unit =>
        A.rel p.1 p.2.1 ⊓ₑ (trunc A).rel p.2.2.1 p.2.2.2 ⊓ₑ A.rel p.1 p.1) ⊢ₚ
        (fun p => A.rel p.1 p.2.1) := PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    exact PLe.trans hxx'
      (PLe.reindex (fun p : A.carrier × A.carrier × Unit × Unit => (p.1, p.2.1)) A.rel_ext_right)
  sv := by
    have hxx : (fun p : A.carrier × Unit × Unit => A.rel p.1 p.1 ⊓ₑ A.rel p.1 p.1) ⊢ₚ
        (fun p => A.rel p.1 p.1) := PLe.and_left _ _
    exact PLe.trans hxx
      (PLe.ex_intro (fun (p : A.carrier × Unit × Unit) => fun x => A.rel x x) (fun p => p.1))
  total := PLe.ex_intro (fun (x : A.carrier) => fun (_ : Unit) => A.rel x x) (fun _ => ())

/-- **Universal property of `‖A‖` (the recursor).** Any morphism `A ⟶ Q` into a
proposition `Q` factors through the unit `η : A ⟶ ‖A‖`. The graph is
`g _ y = ∃ x, f x y` — it keeps `f`'s realizers (the witness `x` hidden), so this is
the witness-preserving truncation, and the factoring map exists exactly because `Q`
is a subsingleton. -/
def Hom.truncRec {A Q : Obj} (hQ : ObjIsProp Q) (f : Hom A Q) : Hom (trunc A) Q where
  rel _ y := EProp.ex A.carrier (fun x => f.rel x y)
  strict_dom :=
    PLe.ex_mono (PLe.reindex (fun q : (Unit × Q.carrier) × A.carrier => (q.2, q.1.2)) f.strict_dom)
  strict_cod :=
    PLe.ex_elim (PLe.reindex (fun q : (Unit × Q.carrier) × A.carrier => (q.2, q.1.2)) f.strict_cod)
  total := by
    have h1 : (fun u : Unit => EProp.ex A.carrier (fun x => A.rel x x)) ⊢ₚ
        (fun u => EProp.ex A.carrier (fun x => EProp.ex Q.carrier (fun y => f.rel x y))) :=
      PLe.ex_mono (PLe.reindex (fun q : Unit × A.carrier => q.2) f.total)
    exact PLe.trans h1
      (PLe.ex_swap (fun (_ : Unit) (x : A.carrier) (y : Q.carrier) => f.rel x y))
  sv := by
    refine PLe.trans (PLe.ex_and_ex
      (fun p : Unit × Q.carrier × Q.carrier => fun x => f.rel x p.2.1)
      (fun p : Unit × Q.carrier × Q.carrier => fun x => f.rel x p.2.2)) ?_
    apply PLe.ex_elim
    apply PLe.ex_elim
    -- q : ((Unit×Q×Q)×A)×A ; y=q.1.1.2.1 y'=q.1.1.2.2 x=q.1.2 x'=q.2
    have hEy := PLe.trans
      (PLe.and_left (fun q : ((Unit × Q.carrier × Q.carrier) × A.carrier) × A.carrier =>
        f.rel q.1.2 q.1.1.2.1) (fun q => f.rel q.2 q.1.1.2.2))
      (PLe.reindex (fun q : ((Unit × Q.carrier × Q.carrier) × A.carrier) × A.carrier =>
        (q.1.2, q.1.1.2.1)) f.strict_cod)
    have hEy' := PLe.trans
      (PLe.and_right (fun q : ((Unit × Q.carrier × Q.carrier) × A.carrier) × A.carrier =>
        f.rel q.1.2 q.1.1.2.1) (fun q => f.rel q.2 q.1.1.2.2))
      (PLe.reindex (fun q : ((Unit × Q.carrier × Q.carrier) × A.carrier) × A.carrier =>
        (q.2, q.1.1.2.2)) f.strict_cod)
    exact PLe.trans (PLe.and_intro hEy hEy')
      (PLe.reindex (fun q : ((Unit × Q.carrier × Q.carrier) × A.carrier) × A.carrier =>
        (q.1.1.2.1, q.1.1.2.2)) hQ)
  congr := by
    have hQyy' : (fun p : Unit × Unit × Q.carrier × Q.carrier =>
        (trunc A).rel p.1 p.2.1 ⊓ₑ Q.rel p.2.2.1 p.2.2.2 ⊓ₑ
          EProp.ex A.carrier (fun x => f.rel x p.2.2.1)) ⊢ₚ
        (fun p => Q.rel p.2.2.1 p.2.2.2) := PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hex : (fun p : Unit × Unit × Q.carrier × Q.carrier =>
        (trunc A).rel p.1 p.2.1 ⊓ₑ Q.rel p.2.2.1 p.2.2.2 ⊓ₑ
          EProp.ex A.carrier (fun x => f.rel x p.2.2.1)) ⊢ₚ
        (fun p => EProp.ex A.carrier (fun x => f.rel x p.2.2.1)) := PLe.and_right _ _
    refine PLe.trans (PLe.and_intro hQyy' hex)
      (PLe.trans (PLe.frobenius
        (fun p : Unit × Unit × Q.carrier × Q.carrier => Q.rel p.2.2.1 p.2.2.2)
        (fun p => fun x => f.rel x p.2.2.1)) ?_)
    apply PLe.ex_mono
    -- q : (Unit×Unit×Q×Q)×A ; y=q.1.2.2.1 y'=q.1.2.2.2 x=q.2
    have hQ' : (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        Q.rel q.1.2.2.1 q.1.2.2.2 ⊓ₑ f.rel q.2 q.1.2.2.1) ⊢ₚ
        (fun q => Q.rel q.1.2.2.1 q.1.2.2.2) := PLe.and_left _ _
    have hfxy : (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        Q.rel q.1.2.2.1 q.1.2.2.2 ⊓ₑ f.rel q.2 q.1.2.2.1) ⊢ₚ
        (fun q => f.rel q.2 q.1.2.2.1) := PLe.and_right _ _
    have hExx := PLe.trans hfxy
      (PLe.reindex (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        (q.2, q.1.2.2.1)) f.strict_dom)
    exact PLe.trans (PLe.and_intro (PLe.and_intro hExx hQ') hfxy)
      (PLe.reindex (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        (q.2, q.2, q.1.2.2.1, q.1.2.2.2)) f.congr)

/-! ### Comprehension (subobjects) -/

/-- The subobject `{x : X | φ x}` carved by a predicate `φ` that **respects** the
equality of `X` (`ρ_X x y ⊓ φ x ⊢ φ y`). Its equality is `ρ_X x y ⊓ φ x`. This is
comprehension; the section object `Π_A p` is an instance (`φ = "is a section"`). -/
def Obj.sub (X : Obj) (φ : X.carrier → EProp)
    (hresp : (fun p : X.carrier × X.carrier => X.rel p.1 p.2 ⊓ₑ φ p.1) ⊢ₚ (fun p => φ p.2)) :
    Obj where
  carrier := X.carrier
  rel x y := X.rel x y ⊓ₑ φ x
  symm := by
    refine PLe.and_intro (PLe.trans (PLe.and_left _ _) X.symm) hresp
  trans := by
    refine PLe.and_intro ?_ ?_
    · have hxy : (fun p : X.carrier × X.carrier × X.carrier =>
          (X.rel p.1 p.2.1 ⊓ₑ φ p.1) ⊓ₑ (X.rel p.2.1 p.2.2 ⊓ₑ φ p.2.1)) ⊢ₚ
          (fun p => X.rel p.1 p.2.1) := PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
      have hyz : (fun p : X.carrier × X.carrier × X.carrier =>
          (X.rel p.1 p.2.1 ⊓ₑ φ p.1) ⊓ₑ (X.rel p.2.1 p.2.2 ⊓ₑ φ p.2.1)) ⊢ₚ
          (fun p => X.rel p.2.1 p.2.2) := PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
      exact PLe.trans (PLe.and_intro hxy hyz) X.trans
    · exact PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)

/-! ### Dependent families as display maps -/

/-- A dependent family over `A` = a display map `p : E ⟶ A`, i.e. an object of the
slice category `T/A`. The fibre over `x` is the pullback along `x`; the dependent
product `Π_A` is the object of sections (built below). -/
structure Family (A : Obj) where
  /-- the total space `E` -/
  total : Obj
  /-- the display map `p : E ⟶ A` -/
  proj : Hom total A

/-- Left congruence of a morphism: `ρ_E e e' ⊓ p e x ⊢ p e' x` (the graph respects
the domain's equality). Derived from `congr` + `strict_cod`. -/
theorem Obj.Hom.congr_left {E A : Obj} (p : Hom E A) :
    (fun q : E.carrier × E.carrier × A.carrier => E.rel q.1 q.2.1 ⊓ₑ p.rel q.1 q.2.2) ⊢ₚ
      (fun q => p.rel q.2.1 q.2.2) := by
  have hEee' : (fun q : E.carrier × E.carrier × A.carrier => E.rel q.1 q.2.1 ⊓ₑ p.rel q.1 q.2.2)
      ⊢ₚ (fun q => E.rel q.1 q.2.1) := PLe.and_left _ _
  have hpex : (fun q : E.carrier × E.carrier × A.carrier => E.rel q.1 q.2.1 ⊓ₑ p.rel q.1 q.2.2)
      ⊢ₚ (fun q => p.rel q.1 q.2.2) := PLe.and_right _ _
  have hAxx := PLe.trans hpex
    (PLe.reindex (fun q : E.carrier × E.carrier × A.carrier => (q.1, q.2.2)) p.strict_cod)
  exact PLe.trans (PLe.and_intro (PLe.and_intro hEee' hAxx) hpex)
    (PLe.reindex (fun q : E.carrier × E.carrier × A.carrier => (q.1, q.2.1, q.2.2, q.2.2)) p.congr)

/-! ### Exponentials -/

/-- The graph-equality of the exponential `B ^ A` at functions `f, g`: a *value* `c` that, at
any future heap, sends a realizer of `ρ_A x x'` to a producer of `ρ_B (f x) (g x')`. Same
Kripke+value shape as `EProp.imp`, indexed over the inputs `x, x'`. -/
def expnRel {A B : Obj} (f g : A.carrier → B.carrier) : EProp where
  rel h c := IsVal c ∧
    ∀ h' (x x' : A.carrier) a, HLe h h' → (A.rel x x').rel h' a →
      (B.rel (f x) (g x')).Produces h' (c ⬝ a)
  ev := by rintro h c ⟨hv, hcond⟩; exact ⟨h, c, hv h, hv, hcond⟩
  mono := by
    rintro h h' c hle ⟨hv, hcond⟩
    exact ⟨hv, fun h'' x x' a hle'' ha => hcond h'' x x' a (HLe.trans hle hle'') ha⟩

/-- Builder combinator inside `symmR`: `symmG sB ⬝ c ↠ S (S(K seq) c) (K(K sB) c)`. -/
def symmG (sB : Code) : Code := S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ seq))) ⬝ (K ⬝ (K ⬝ sB))

/-- Realizer for the exponential's symmetry: `symmR sA sB ⬝ c` evaluates to the value that, on
input `a`, runs the seq-forced pipeline `sB · (c · (sA · a))`. -/
def symmR (sA sB : Code) : Code :=
  Code.B ⬝ (S ⬝ (S ⬝ (K ⬝ seq) ⬝ sA)) ⬝ (Code.B ⬝ K ⬝ symmG sB)

/-- The value `symmG sB ⬝ c` evaluates to, at any heap. -/
theorem symmG_eval {sB c : Code} (hp : CHeap) :
    Evaluates hp (symmG sB ⬝ c) hp (S ⬝ (S ⬝ (K ⬝ seq) ⬝ c) ⬝ (K ⬝ (K ⬝ sB) ⬝ c)) := by
  simp only [symmG]
  apply Evaluates.headS
  refine Evaluates.mk_app (h2 := hp) (fv := S ⬝ (S ⬝ (K ⬝ seq) ⬝ c)) ?_ ⟨1, by simp only [applyV]⟩
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.Sval) ⟨1, by simp only [applyV]⟩)

/-- **The exponential's equality is symmetric.** The realizer composes A's symmetry, the
witness `c`, and B's symmetry, each stage `seq`-forced so the next stage receives a value. -/
theorem expn_symm {A B : Obj} :
    (fun p : (A.carrier → B.carrier) × (A.carrier → B.carrier) => expnRel p.1 p.2) ⊢ₚ
      (fun p => expnRel p.2 p.1) := by
  obtain ⟨sA, hsA⟩ := A.symm
  obtain ⟨sB, hsB⟩ := B.symm
  refine ⟨symmR sA sB, ?_⟩
  rintro ⟨f, g⟩ h c ⟨hcv, hc⟩
  refine ⟨h, S ⬝ (S ⬝ (K ⬝ seq) ⬝ sA) ⬝ (Code.B ⬝ K ⬝ symmG sB ⬝ c),
    by simp only [symmR]
       exact Evaluates.Bsim (Evaluates.mk_app Evaluates.S1 ⟨1, by simp only [applyV]⟩),
    fun _ => Evaluates.S2, ?_⟩
  rintro h₃ x x' a hle₃ ha
  -- transport  V ⬝ a  ←  seq (sA ⬝ a) (cont ⬝ a)   via headSeqK
  suffices hseq : (B.rel (g x) (f x')).Produces h₃
      (seq ⬝ (sA ⬝ a) ⬝ (Code.B ⬝ K ⬝ symmG sB ⬝ c ⬝ a)) by
    obtain ⟨hh, w, ev, hw⟩ := hseq
    exact ⟨hh, w, Evaluates.headSeqK ev, hw⟩
  -- stage A : sA ⬝ a → a' realizing ρ_A x' x
  refine EProp.Produces.bindH (hsA (x, x') h₃ a ha) (fun ph a' hlep ha' => ?_)
  -- continuation head  B K (symmG sB) ⬝ c ⬝ a  evaluates to  symm2 := S (S(K seq) c) (K(K sB) c)
  have hcont : Evaluates ph (Code.B ⬝ K ⬝ symmG sB ⬝ c ⬝ a) ph
      (S ⬝ (S ⬝ (K ⬝ seq) ⬝ c) ⬝ (K ⬝ (K ⬝ sB) ⬝ c)) :=
    Evaluates.appHeadSwap (Evaluates.Bsim Evaluates.K1) Evaluates.K1 (Evaluates.headK (symmG_eval ph))
  refine EProp.Produces.headEq (g' := S ⬝ (S ⬝ (K ⬝ seq) ⬝ c) ⬝ (K ⬝ (K ⬝ sB) ⬝ c)) (k := a')
    (fun hh v hev => by obtain ⟨rfl, rfl⟩ := Evaluates.deterministic hev Evaluates.S2; exact hcont) ?_
  -- now produce from  symm2 ⬝ a'  =  S (S(K seq) c) (K(K sB) c) ⬝ a'  →  (X ⬝ a')(Y ⬝ a')
  have hXa' : Evaluates ph (S ⬝ (K ⬝ seq) ⬝ c ⬝ a') ph (seq ⬝ (c ⬝ a')) :=
    Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.seqv) ⟨1, by simp only [applyV]⟩)
  obtain ⟨hh2, w2, ev2, hw2⟩ :
      (B.rel (g x) (f x')).Produces ph
        ((S ⬝ (K ⬝ seq) ⬝ c ⬝ a') ⬝ (K ⬝ (K ⬝ sB) ⬝ c ⬝ a')) := by
    refine EProp.Produces.headEq (g' := seq ⬝ (c ⬝ a')) (k := K ⬝ (K ⬝ sB) ⬝ c ⬝ a')
      (fun hh v hev => by obtain ⟨rfl, rfl⟩ := Evaluates.deterministic hev Evaluates.seqVal; exact hXa') ?_
    -- stage c : run c ⬝ a' → b realizing ρ_B (f x') (g x)
    refine EProp.Produces.bindH (hc ph x' x a' (HLe.trans hle₃ hlep) ha') (fun ph2 b hlep2 hb => ?_)
    -- stage B : continuation  K (K sB) c ⬝ a' ⬝ b  ↠  sB ⬝ b
    refine EProp.Produces.headEq (g' := sB) (k := b) (fun hh v hev => ?_) (hsB (f x', g x) ph2 b hb)
    exact Evaluates.appHeadSwap (Evaluates.headK Evaluates.K1) Evaluates.K1 (Evaluates.headK hev)
  exact ⟨hh2, w2, Evaluates.headS ev2, hw2⟩

/-- The closed continuation of the transitivity realizer: `transCont eBt ⬝ b₁ ⬝ b₂` runs
`seq · (pr · b₁ · b₂) · eBt`, i.e. it pairs the two `B`-realizers, `seq`-forces the pair to a
value, and feeds it to `B`'s transitivity realizer `eBt`. -/
def transCont (eBt : Code) : Code :=
  S ⬝ (S ⬝ (K ⬝ S) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ pr)) ⬝ (K ⬝ (K ⬝ eBt))

theorem transCont_step {eBt b₁ : Code} (hp : CHeap) :
    Evaluates hp (transCont eBt ⬝ b₁) hp
      (S ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ pr ⬝ b₁) ⬝ (K ⬝ (K ⬝ eBt) ⬝ b₁)) := by
  simp only [transCont]
  apply Evaluates.headS
  refine Evaluates.mk_app (h2 := hp) (fv := S ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ pr ⬝ b₁)) ?_
    ⟨1, by simp only [applyV]⟩
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.Sval) ⟨1, by simp only [applyV]⟩)

/-- `B · (B seq) · pr · b₁ · b₂ ↠ seq · (pr · b₁ · b₂)`: the seq-with-one-argument value. -/
theorem transBseqpr_eval {b₁ b₂ : Code} (hp : CHeap) :
    Evaluates hp (Code.B ⬝ (Code.B ⬝ seq) ⬝ pr ⬝ b₁ ⬝ b₂) hp (seq ⬝ (pr ⬝ b₁ ⬝ b₂)) := by
  have hg : Evaluates hp (Code.B ⬝ (Code.B ⬝ seq) ⬝ pr ⬝ b₁) hp (S ⬝ (K ⬝ seq) ⬝ (pr ⬝ b₁)) :=
    Evaluates.Bsim (Evaluates.mk_app Evaluates.B1 ⟨1, by simp only [applyV]⟩)
  refine Evaluates.appHeadSwap hg Evaluates.S2 ?_
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.seqv) ⟨1, by simp only [applyV]⟩)

/-- **The transitivity continuation is correct.** If `pr · b₁ · b₂` realises a conjunction `Q`
at `hp` and `B`'s transitivity realizer `eBt` carries `Q` to `R`, then `transCont eBt ⬝ b₁ ⬝ b₂`
produces an `R`-realizer. -/
theorem transCont_produces {eBt b₁ b₂ : Code} {Q R : EProp} (hp : CHeap)
    (hpair : Q.rel hp (pr ⬝ b₁ ⬝ b₂))
    (hBt : ∀ h' v, HLe hp h' → Q.rel h' v → R.Produces h' (eBt ⬝ v)) :
    R.Produces hp (transCont eBt ⬝ b₁ ⬝ b₂) := by
  -- produce R from the clean seq-form, then transport back along the combinator's reduction
  have hseq : R.Produces hp (seq ⬝ (pr ⬝ b₁ ⬝ b₂) ⬝ (K ⬝ (K ⬝ eBt) ⬝ b₁ ⬝ b₂)) := by
    refine EProp.Produces.bindH ⟨hp, pr ⬝ b₁ ⬝ b₂, Evaluates.prVal, hpair⟩ (fun h' v hle hv => ?_)
    -- continuation  K (K eBt) b₁ b₂ ⬝ v  ↠  eBt ⬝ v
    refine EProp.Produces.headEq (g' := eBt) (k := v) (fun hh w hev => ?_) (hBt h' v hle hv)
    exact Evaluates.appHeadSwap (Evaluates.headK Evaluates.K1) Evaluates.K1 (Evaluates.headK hev)
  obtain ⟨hh, w, ev, hw⟩ := hseq
  refine ⟨hh, w, ?_, hw⟩
  -- transCont eBt b₁ ⬝ b₂  ←  (cval) ⬝ b₂  ←  seq-form
  refine Evaluates.appHeadSwap (transCont_step hp) Evaluates.S2 ?_
  apply Evaluates.headS
  exact Evaluates.appHeadSwap (transBseqpr_eval hp) Evaluates.seqVal ev

/-- Left branch builder: `transU ⬝ e ⬝ a ↠ seq · (fst · e · a)` — feeds `a` to `c₁ = fst e`
under a `seq`, the head of the outer pipeline. -/
def transU : Code := Code.B ⬝ (S ⬝ (K ⬝ seq)) ⬝ fst

theorem transU_eval {e : Code} (hp : CHeap) :
    Evaluates hp (transU ⬝ e) hp (S ⬝ (K ⬝ seq) ⬝ (fst ⬝ e)) :=
  Evaluates.Bsim (Evaluates.mk_app Evaluates.S1 ⟨1, by simp only [applyV]⟩)

theorem transU_apply {e a : Code} (hp : CHeap) :
    Evaluates hp (transU ⬝ e ⬝ a) hp (seq ⬝ (fst ⬝ e ⬝ a)) := by
  refine Evaluates.appHeadSwap (transU_eval hp) Evaluates.S2 ?_
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.seqv) ⟨1, by simp only [applyV]⟩)

/-- `transDofAbs eAr ⬝ e ↠ S · (S · (K seq) · eAr) · (B · K · snd · e)`: the abstracted form of
`transDof eAr (snd e)`; on an extra `a` it runs `seq · (eAr · a) · (snd · e)`. -/
def transDofAbs (eAr : Code) : Code := Code.B ⬝ (S ⬝ (S ⬝ (K ⬝ seq) ⬝ eAr)) ⬝ (Code.B ⬝ K ⬝ snd)

theorem transDofAbs_eval {eAr e : Code} (hp : CHeap) :
    Evaluates hp (transDofAbs eAr ⬝ e) hp
      (S ⬝ (S ⬝ (K ⬝ seq) ⬝ eAr) ⬝ (Code.B ⬝ K ⬝ snd ⬝ e)) :=
  Evaluates.Bsim (Evaluates.mk_app Evaluates.S1 ⟨1, by simp only [applyV]⟩)

/-- Transport: a full run of `seq · (eAr · a) · (B K snd e a)` lifts to `transDofAbs eAr · e · a`
(the right input's `b₂`-producer). -/
theorem transDofAbs_apply {eAr e a : Code} {hp hh : CHeap} {w : Code}
    (hev : Evaluates hp (seq ⬝ (eAr ⬝ a) ⬝ (Code.B ⬝ K ⬝ snd ⬝ e ⬝ a)) hh w) :
    Evaluates hp (transDofAbs eAr ⬝ e ⬝ a) hh w :=
  Evaluates.appHeadSwap (transDofAbs_eval hp) Evaluates.S2 (Evaluates.headSeqK hev)

/-- Right branch builder. `transV (transDofAbs eAr) (transCont eBt) ⬝ e ⬝ a ⬝ b₁` runs
`seq · (transDofAbs eAr · e · a) · (transCont eBt · b₁)`: produce `b₂` from the right input,
then pair it with `b₁` and compose via `B`-transitivity. -/
def transV (r cont : Code) : Code :=
  S ⬝ (Code.B ⬝ S ⬝ (Code.B ⬝ (Code.B ⬝ S) ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝
      (Code.B ⬝ (Code.B ⬝ seq) ⬝ r)))) ⬝ (K ⬝ (K ⬝ cont))

/-- `va3 · e · a ↠ seq · (r · e · a)` (a `seq`-with-one-argument value). -/
theorem transVA3 {r e a : Code} (hp : CHeap) :
    Evaluates hp (Code.B ⬝ (Code.B ⬝ seq) ⬝ r ⬝ e ⬝ a) hp
      (seq ⬝ (r ⬝ e ⬝ a)) := by
  have hg : Evaluates hp (Code.B ⬝ (Code.B ⬝ seq) ⬝ r ⬝ e) hp
      (S ⬝ (K ⬝ seq) ⬝ (r ⬝ e)) :=
    Evaluates.Bsim (Evaluates.mk_app Evaluates.B1 ⟨1, by simp only [applyV]⟩)
  refine Evaluates.appHeadSwap hg Evaluates.S2 ?_
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.seqv) ⟨1, by simp only [applyV]⟩)

/-- `va2 · e · a ↠ K · (va3 · e · a)`. -/
theorem transVA2 {r e a : Code} (hp : CHeap) :
    Evaluates hp (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r) ⬝ e ⬝ a)
      hp (K ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r ⬝ e ⬝ a)) := by
  have hg : Evaluates hp (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r) ⬝ e) hp
      (S ⬝ (K ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r ⬝ e)) :=
    Evaluates.Bsim (Evaluates.mk_app Evaluates.B1 ⟨1, by simp only [applyV]⟩)
  refine Evaluates.appHeadSwap hg Evaluates.S2 ?_
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.Kval) ⟨1, by simp only [applyV]⟩)

/-- `va1 · e · a ↠ S · (va2 · e · a)`. -/
theorem transVA1 {r e a : Code} (hp : CHeap) :
    Evaluates hp (Code.B ⬝ (Code.B ⬝ S) ⬝
      (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r)) ⬝ e ⬝ a) hp
      (S ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r) ⬝ e ⬝ a)) := by
  have hg : Evaluates hp (Code.B ⬝ (Code.B ⬝ S) ⬝
      (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r)) ⬝ e) hp
      (S ⬝ (K ⬝ S) ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r) ⬝ e)) :=
    Evaluates.Bsim (Evaluates.mk_app Evaluates.B1 ⟨1, by simp only [applyV]⟩)
  refine Evaluates.appHeadSwap hg Evaluates.S2 ?_
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.Sval) ⟨1, by simp only [applyV]⟩)

/-- `transV r cont · e · a` evaluates to the `headSeqK`-shaped value `cval2`. -/
theorem transV_ea {r cont e a : Code} (hp : CHeap) :
    Evaluates hp (transV r cont ⬝ e ⬝ a) hp
      (S ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r) ⬝ e ⬝ a) ⬝
        (K ⬝ (K ⬝ cont) ⬝ e ⬝ a)) := by
  simp only [transV]
  have he : Evaluates hp (S ⬝ (Code.B ⬝ S ⬝ (Code.B ⬝ (Code.B ⬝ S) ⬝
        (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r)))) ⬝
        (K ⬝ (K ⬝ cont)) ⬝ e) hp
      (S ⬝ (Code.B ⬝ (Code.B ⬝ S) ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝
        (Code.B ⬝ (Code.B ⬝ seq) ⬝ r)) ⬝ e) ⬝
        (K ⬝ (K ⬝ cont) ⬝ e)) := by
    apply Evaluates.headS
    have hge : Evaluates hp (Code.B ⬝ S ⬝ (Code.B ⬝ (Code.B ⬝ S) ⬝
        (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r))) ⬝ e) hp
        (S ⬝ (Code.B ⬝ (Code.B ⬝ S) ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝
          (Code.B ⬝ (Code.B ⬝ seq) ⬝ r)) ⬝ e)) :=
      Evaluates.Bsim Evaluates.S1
    exact Evaluates.mk_app hge ⟨1, by simp only [applyV]⟩
  have hea : Evaluates hp
      (S ⬝ (Code.B ⬝ (Code.B ⬝ S) ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝
        (Code.B ⬝ (Code.B ⬝ seq) ⬝ r)) ⬝ e) ⬝
        (K ⬝ (K ⬝ cont) ⬝ e) ⬝ a) hp
      (S ⬝ (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r) ⬝ e ⬝ a) ⬝
        (K ⬝ (K ⬝ cont) ⬝ e ⬝ a)) := by
    apply Evaluates.headS
    exact Evaluates.mk_app (transVA1 hp) ⟨1, by simp only [applyV]⟩
  exact Evaluates.appHeadSwap he Evaluates.S2 hea

/-- Transport: a full run of `seq · (r · e · a) · (K (K cont) e a b₁)` lifts to
`transV r cont · e · a · b₁`. The continuation reduces to `cont · b₁`. -/
theorem transV_apply {r cont e a b₁ : Code} {hp hh : CHeap} {w : Code}
    (hev : Evaluates hp (seq ⬝ (r ⬝ e ⬝ a) ⬝
      (K ⬝ (K ⬝ cont) ⬝ e ⬝ a ⬝ b₁)) hh w) :
    Evaluates hp (transV r cont ⬝ e ⬝ a ⬝ b₁) hh w := by
  refine Evaluates.appHeadSwap (transV_ea hp) Evaluates.S2 ?_
  apply Evaluates.headS
  -- va2 e a b₁ ↠ K (va3 e a) b₁ ↠ va3 e a ↠ seq (r e a)
  have hP : Evaluates hp (Code.B ⬝ (Code.B ⬝ K) ⬝ (Code.B ⬝ (Code.B ⬝ seq) ⬝ r) ⬝ e ⬝ a ⬝ b₁)
      hp (seq ⬝ (r ⬝ e ⬝ a)) :=
    Evaluates.appHeadSwap (transVA2 hp) Evaluates.K1 (Evaluates.headK (transVA3 hp))
  exact Evaluates.appHeadSwap hP Evaluates.seqVal hev

/-- **The exponential's equality is transitive.** Given a pair `⟨c₁, c₂⟩` realising
`expnRel f g ⊓ expnRel g k`, the realizer runs, on input `a : ρ_A x x'`, the pipeline
`b₁ ← c₁·a`, `a' ← eAr·a` (right extent), `b₂ ← c₂·a'`, then `eBt·⟨b₁,b₂⟩` (`B`-transitivity),
producing a realizer of `ρ_B (f x) (k x')`. -/
theorem expn_trans {A B : Obj} :
    (fun p : (A.carrier → B.carrier) × (A.carrier → B.carrier) × (A.carrier → B.carrier) =>
        expnRel p.1 p.2.1 ⊓ₑ expnRel p.2.1 p.2.2) ⊢ₚ (fun p => expnRel p.1 p.2.2) := by
  obtain ⟨eAr, hAr⟩ := A.rel_ext_right
  obtain ⟨eBt, hBt⟩ := B.trans
  refine ⟨S ⬝ (Code.B ⬝ S ⬝ transU) ⬝ (transV (transDofAbs eAr) (transCont eBt)), ?_⟩
  rintro ⟨f, g, k⟩ h₀ e ⟨c₁, c₂, rfl, ⟨hc1v, hc1⟩, ⟨hc2v, hc2⟩⟩
  refine ⟨h₀, S ⬝ (transU ⬝ (pr ⬝ c₁ ⬝ c₂)) ⬝ (transV (transDofAbs eAr) (transCont eBt) ⬝ (pr ⬝ c₁ ⬝ c₂)), ?_,
    fun _ => Evaluates.S2, ?_⟩
  · -- the realizer evaluates to the `S U V` value
    apply Evaluates.headS
    exact Evaluates.mk_app (fv := S ⬝ (transU ⬝ (pr ⬝ c₁ ⬝ c₂)))
      (Evaluates.Bsim Evaluates.S1) ⟨1, by simp only [applyV]⟩
  · -- application: produce ρ_B (f x) (k x') from a : ρ_A x x'
    rintro h' x x' a hle ha
    suffices hsuf : (B.rel (f x) (k x')).Produces h'
        (seq ⬝ (fst ⬝ (pr ⬝ c₁ ⬝ c₂) ⬝ a) ⬝ (transV (transDofAbs eAr) (transCont eBt) ⬝ (pr ⬝ c₁ ⬝ c₂) ⬝ a)) by
      obtain ⟨hh, w, ev, hw⟩ := hsuf
      refine ⟨hh, w, ?_, hw⟩
      apply Evaluates.headS
      exact Evaluates.appHeadSwap (transU_apply h') Evaluates.seqVal ev
    -- stage 1 : b₁ ← c₁ · a
    refine EProp.Produces.bindH (Q := B.rel (f x) (g x')) ?_ ?_
    · refine EProp.Produces.headEq (g' := c₁) (k := a) (fun hh v hev => ?_)
        (hc1 h' x x' a hle ha)
      obtain ⟨rfl, rfl⟩ := Evaluates.deterministic hev (hc1v h')
      exact Evaluates.fstβ
    · intro h'' b₁ hle'' hb1
      -- continuation: transV · e · a · b₁, via its transport to the inner seq pipeline
      have key : (B.rel (f x) (k x')).Produces h''
          (seq ⬝ (transDofAbs eAr ⬝ (pr ⬝ c₁ ⬝ c₂) ⬝ a) ⬝
            (K ⬝ (K ⬝ (transCont eBt)) ⬝ (pr ⬝ c₁ ⬝ c₂) ⬝ a ⬝ b₁)) := by
        -- stage 2 : b₂ ← transDofAbs (= eAr then c₂)
        refine EProp.Produces.bindH (Q := B.rel (g x') (k x')) ?_ ?_
        · -- transDofAbs produces ρ_B (g x') (k x') via its transport to seq (eAr a) (snd e)
          have key3 : (B.rel (g x') (k x')).Produces h''
              (seq ⬝ (eAr ⬝ a) ⬝ (Code.B ⬝ K ⬝ snd ⬝ (pr ⬝ c₁ ⬝ c₂) ⬝ a)) := by
            -- stage 2a : a' ← eAr · a  (right extent ρ_A x' x')
            refine EProp.Produces.bindH (hAr (x, x') h'' a ((A.rel x x').mono hle'' ha)) ?_
            intro h₃ a' hle3 ha'
            -- stage 2b : c₂ · a' → ρ_B (g x') (k x')
            refine EProp.Produces.headEq (g' := c₂) (k := a') (fun hh v hev => ?_)
              (hc2 h₃ x' x' a' (HLe.trans hle (HLe.trans hle'' hle3)) ha')
            obtain ⟨rfl, rfl⟩ := Evaluates.deterministic hev (hc2v h₃)
            exact Evaluates.appHeadSwap (Evaluates.Bsim Evaluates.K1) Evaluates.K1
              (Evaluates.headK Evaluates.sndβ)
          obtain ⟨hh3, w3, ev3, hw3⟩ := key3
          exact ⟨hh3, w3, transDofAbs_apply ev3, hw3⟩
        · -- stage 3 : eBt · ⟨b₁, b₂⟩
          intro h₄ b₂ hle4 hb2
          obtain ⟨hh4, w4, ev4, hw4⟩ : (B.rel (f x) (k x')).Produces h₄ (transCont eBt ⬝ b₁ ⬝ b₂) :=
            transCont_produces (Q := B.rel (f x) (g x') ⊓ₑ B.rel (g x') (k x')) h₄
              ⟨b₁, b₂, rfl, (B.rel (f x) (g x')).mono hle4 hb1, hb2⟩
              (fun hh v _ hv => hBt (f x, g x', k x') hh v hv)
          refine ⟨hh4, w4, ?_, hw4⟩
          have hKKt : Evaluates h₄ (K ⬝ (K ⬝ (transCont eBt)) ⬝ (pr ⬝ c₁ ⬝ c₂) ⬝ a) h₄ (transCont eBt) :=
            Evaluates.appHeadSwap (Evaluates.headK Evaluates.K1) Evaluates.K1
              (Evaluates.headK Evaluates.S2)
          obtain ⟨h2, fv, hfv, m, happ⟩ := Evaluates.app_inv ev4
          exact Evaluates.mk_app (Evaluates.appHeadSwap hKKt Evaluates.S2 hfv) ⟨m, happ⟩
      obtain ⟨hh, w, ev2, hw2⟩ := key
      exact ⟨hh, w, transV_apply ev2, hw2⟩

/-- **The exponential object `B ^ A`.** Its carrier is the function type `A.carrier → B.carrier`
and its partial equivalence relation is `expnRel` (the Kripke function-space equality), shown
symmetric (`expn_symm`) and transitive (`expn_trans`). -/
def expn (A B : Obj) : Obj where
  carrier := A.carrier → B.carrier
  rel := expnRel
  symm := expn_symm
  trans := expn_trans

/-! ### Decidable equality (the `AC_dec` premise) -/

/-- **Decidable equality** of an object `A`, internally: a uniform realizer that, for every
pair `(x, y)`, decides `ρ_A x y` — i.e. realizes the coproduct `(x = y) + ¬(x = y)`. This is the
realizability reading of the `AC_dec` premise `Π x y. (x = y) + ¬(x = y)`; the realizer is what
keys the memo cache. -/
def HasDecEq (A : Obj) : Prop :=
  (fun _ : A.carrier × A.carrier => EProp.top) ⊢ₚ
    (fun p => A.rel p.1 p.2 ⊔ₑ (A.rel p.1 p.2 ⇨ₑ EProp.bot))

/-- The terminal object has decidable equality (everything is equal — decide `inl`). -/
theorem hasDecEq_one : HasDecEq one :=
  PLe.inl (fun _ : Unit × Unit => EProp.top) (fun p => one.rel p.1 p.2 ⇨ₑ EProp.bot)

/-! ### Dependent product (object of sections) -/

/-- The "`f` is a section of the display map `p`" predicate: a *value* `c` that, at any future
heap, sends a realizer of `ρ_A x x` to a producer of `ρ_E (f x) x` over `p` — i.e. witnesses
`p (f x) = x`. Same Kripke+value shape as `expnRel`/`EProp.imp`. -/
def secP {A : Obj} (B : Family A) (f : A.carrier → B.total.carrier) : EProp where
  rel h c := IsVal c ∧
    ∀ h' (x : A.carrier) a, HLe h h' → (A.rel x x).rel h' a →
      (B.proj.rel (f x) x).Produces h' (c ⬝ a)
  ev := by rintro h c ⟨hv, hcond⟩; exact ⟨h, c, hv h, hv, hcond⟩
  mono := by
    rintro h h' c hle ⟨hv, hcond⟩
    exact ⟨hv, fun h'' x a hle'' ha => hcond h'' x a (HLe.trans hle hle'') ha⟩

/-- **The dependent product `Π (x:A). B x`** of a display map `B = (E, p)`: the object of
**sections**, the subobject of the exponential `E ^ A` cut out by "`f` is a section" (`secP`).
The respect proof reuses the transitivity pipeline (`transU`/`transV`/`transCont`): on input
`a : ρ_A x x` it pairs `c_e·a : ρ_E (f x)(g x)` with `c_s·a : p (f x) = x` and composes via the
display map's left-congruence realizer `clg`, yielding `p (g x) = x`. -/
def Family.pi {A : Obj} (B : Family A) : Obj :=
  Obj.sub (expn A B.total) (secP B) (by
    obtain ⟨clg, hclg⟩ := Obj.Hom.congr_left B.proj
    refine ⟨S ⬝ (Code.B ⬝ S ⬝ transU) ⬝ (transV snd (transCont clg)), ?_⟩
    rintro ⟨f, g⟩ h₀ e ⟨c_e, c_s, rfl, ⟨hcev, hce⟩, ⟨hcsv, hcs⟩⟩
    refine ⟨h₀, S ⬝ (transU ⬝ (pr ⬝ c_e ⬝ c_s)) ⬝ (transV snd (transCont clg) ⬝ (pr ⬝ c_e ⬝ c_s)),
      ?_, fun _ => Evaluates.S2, ?_⟩
    · apply Evaluates.headS
      exact Evaluates.mk_app (fv := S ⬝ (transU ⬝ (pr ⬝ c_e ⬝ c_s)))
        (Evaluates.Bsim Evaluates.S1) ⟨1, by simp only [applyV]⟩
    · rintro h' x a hle ha
      suffices hsuf : (B.proj.rel (g x) x).Produces h'
          (seq ⬝ (fst ⬝ (pr ⬝ c_e ⬝ c_s) ⬝ a) ⬝ (transV snd (transCont clg) ⬝ (pr ⬝ c_e ⬝ c_s) ⬝ a)) by
        obtain ⟨hh, w, ev, hw⟩ := hsuf
        refine ⟨hh, w, ?_, hw⟩
        apply Evaluates.headS
        exact Evaluates.appHeadSwap (transU_apply h') Evaluates.seqVal ev
      -- stage 1 : b₁ ← c_e · a  (expnRel f g at (x,x) → ρ_E (f x) (g x))
      refine EProp.Produces.bindH (Q := B.total.rel (f x) (g x)) ?_ ?_
      · refine EProp.Produces.headEq (g' := c_e) (k := a) (fun hh v hev => ?_)
          (hce h' x x a hle ha)
        obtain ⟨rfl, rfl⟩ := Evaluates.deterministic hev (hcev h')
        exact Evaluates.fstβ
      · intro h'' b₁ hle'' hb1
        have key : (B.proj.rel (g x) x).Produces h''
            (seq ⬝ (snd ⬝ (pr ⬝ c_e ⬝ c_s) ⬝ a) ⬝
              (K ⬝ (K ⬝ (transCont clg)) ⬝ (pr ⬝ c_e ⬝ c_s) ⬝ a ⬝ b₁)) := by
          -- stage 2 : b₂ ← c_s · a  (secP f at x → p (f x) = x)
          refine EProp.Produces.bindH (Q := B.proj.rel (f x) x) ?_ ?_
          · refine EProp.Produces.headEq (g' := c_s) (k := a) (fun hh v hev => ?_)
              (hcs h'' x a (HLe.trans hle hle'') ((A.rel x x).mono hle'' ha))
            obtain ⟨rfl, rfl⟩ := Evaluates.deterministic hev (hcsv h'')
            exact Evaluates.sndβ
          · -- stage 3 : clg · ⟨b₁, b₂⟩
            intro h₄ b₂ hle4 hb2
            obtain ⟨hh4, w4, ev4, hw4⟩ : (B.proj.rel (g x) x).Produces h₄ (transCont clg ⬝ b₁ ⬝ b₂) :=
              transCont_produces (Q := B.total.rel (f x) (g x) ⊓ₑ B.proj.rel (f x) x) h₄
                ⟨b₁, b₂, rfl, (B.total.rel (f x) (g x)).mono hle4 hb1, hb2⟩
                (fun hh v _ hv => hclg (f x, g x, x) hh v hv)
            refine ⟨hh4, w4, ?_, hw4⟩
            have hKKt : Evaluates h₄ (K ⬝ (K ⬝ (transCont clg)) ⬝ (pr ⬝ c_e ⬝ c_s) ⬝ a) h₄
                (transCont clg) :=
              Evaluates.appHeadSwap (Evaluates.headK Evaluates.K1) Evaluates.K1
                (Evaluates.headK Evaluates.S2)
            obtain ⟨h2, fv, hfv, m, happ⟩ := Evaluates.app_inv ev4
            exact Evaluates.mk_app (Evaluates.appHeadSwap hKKt Evaluates.S2 hfv) ⟨m, happ⟩
        obtain ⟨hh, w, ev2, hw2⟩ := key
        exact ⟨hh, w, transV_apply ev2, hw2⟩)

end Eval

end LeanStatefulAoc
