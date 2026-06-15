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

end Eval

end LeanStatefulAoc
