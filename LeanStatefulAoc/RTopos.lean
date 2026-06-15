import LeanStatefulAoc.Combinators
import LeanStatefulAoc.Tripos

-- The tripos-to-topos morphism axioms are predicates over product carriers, whose
-- type annotations are unavoidably long; the line-length style linter is off here.
set_option linter.style.longLine false

/-!
# The realizability topos (Layer 3) — objects and morphisms via tripos-to-topos

The type formers we need — propositional truncation, the dependent product — are
fixed by **universal properties**, which live in the **equality** of objects, and
that equality must see the **world-state**. Two facts pin the construction down:

* Modest sets (PERs directly on codes) form a regular category but **not a topos**.
  The actual realizability topos is the **tripos-to-topos** completion: an object
  is an *arbitrary carrier type* with a partial equality **valued in the tripos**,
  which is what makes it closed under quotients.
* The tripos here is `RProp`, whose truth values are **heap-indexed**. Valuing the
  equality in `RProp` threads the world-state through every object and morphism.

A subtlety the construction forces: the object/morphism axioms must hold
**uniformly over the carrier** — a single realizer for the whole fiber `P(X)`, not
one realizer per index. (Composition of functional relations needs this; it fails
with merely pointwise realizers.) So the basic relation is `⊢ₚ`: indexed
entailment of carrier-indexed predicates, one code uniform over the carrier and the
heap. The pointwise Heyting structure on the fibers lifts the Layer-2 Heyting
realizers, which are carrier-independent codes, hence automatically uniform.

This file: the fiber entailment API (`⊢ₚ`), the object and morphism structures, and
the identity morphism. Composition, products, truncation (as image) and `Π` build
on top.
-/

namespace LeanStatefulAoc

open Code

/-! ### Fibers of the tripos and their uniform entailment

`Pred X = X → RProp` is the fiber `P(X)`. `PLe φ ψ` ("`φ ⊢ₚ ψ`") is entailment in
that fiber: one realizer code, uniform over the carrier `X` and the heap. -/

/-- A predicate over a carrier: the fiber `P(X)` of the realizability tripos. -/
abbrev Pred (X : Type) := X → RProp

/-- Uniform entailment in the fiber `P(X)`: one realizer, uniform over `X` and the
heap. This is the order that makes `P` a tripos. -/
def PLe {X : Type} (φ ψ : Pred X) : Prop :=
  ∃ r : Code, ∀ x h a, (φ x).rel h a → (ψ x).rel h (r ⬝ a)

@[inherit_doc] scoped infix:50 " ⊢ₚ " => PLe

theorem PLe.refl {X : Type} (φ : Pred X) : φ ⊢ₚ φ :=
  ⟨Code.I, fun x _ _ ha => (φ x).expReds Code.Reds.i ha⟩

theorem PLe.trans {X : Type} {φ ψ χ : Pred X} (h₁ : φ ⊢ₚ ψ) (h₂ : ψ ⊢ₚ χ) : φ ⊢ₚ χ := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨Code.B ⬝ r₂ ⬝ r₁, fun x h a ha =>
    (χ x).expReds (Code.B_app r₂ r₁ a) (hr₂ x h _ (hr₁ x h a ha))⟩

/-- Reindexing along `f : Y → X` (the tripos's substitution functor `P(f)`): the
same realizer works. -/
theorem PLe.reindex {X Y : Type} {φ ψ : Pred X} (f : Y → X) (h : φ ⊢ₚ ψ) :
    (fun y => φ (f y)) ⊢ₚ (fun y => ψ (f y)) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun y => hr (f y)⟩

/-- Pointwise first projection (uniform realizer `fst`). -/
theorem PLe.and_left {X : Type} (φ ψ : Pred X) : (fun x => φ x ⊓ᵣ ψ x) ⊢ₚ φ :=
  ⟨Code.fst, fun x _ _ ⟨_, _, hred, hp, _⟩ =>
    (φ x).expReds (.trans (Code.Reds.appR Code.fst hred) (.single Code.Red.prL)) hp⟩

/-- Pointwise second projection (uniform realizer `snd`). -/
theorem PLe.and_right {X : Type} (φ ψ : Pred X) : (fun x => φ x ⊓ᵣ ψ x) ⊢ₚ ψ :=
  ⟨Code.snd, fun x _ _ ⟨_, _, hred, _, hq⟩ =>
    (ψ x).expReds (.trans (Code.Reds.appR Code.snd hred) (.single Code.Red.prR)) hq⟩

/-- Pointwise pairing (uniform realizer `S ⬝ (B ⬝ pr ⬝ r₁) ⬝ r₂`). -/
theorem PLe.and_intro {X : Type} {ρ φ ψ : Pred X} (h₁ : ρ ⊢ₚ φ) (h₂ : ρ ⊢ₚ ψ) :
    ρ ⊢ₚ (fun x => φ x ⊓ᵣ ψ x) := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  refine ⟨Code.S ⬝ (Code.B ⬝ Code.pr ⬝ r₁) ⬝ r₂, fun x h a ha => ?_⟩
  refine ⟨r₁ ⬝ a, r₂ ⬝ a, ?_, hr₁ x h a ha, hr₂ x h a ha⟩
  exact .trans (.single Code.Red.s) (Code.Reds.appL (Code.B_app Code.pr r₁ a) (r₂ ⬝ a))

/-- Existential introduction at a chosen witness `w x` (uniform realizer `I`). -/
theorem PLe.ex_intro {X I : Type} (φ : X → I → RProp) (w : X → I) :
    (fun x => φ x (w x)) ⊢ₚ (fun x => RProp.ex I (fun i => φ x i)) :=
  ⟨Code.I, fun x _ _a ha => ⟨w x, (φ x (w x)).expReds Code.Reds.i ha⟩⟩

/-- Existential elimination: to map out of `∃ i, φ x i` into something independent
of `i`, map out of `φ x i` uniformly. Same realizer (`∃` keeps the realizer). -/
theorem PLe.ex_elim {X I : Type} {φ : X → I → RProp} {ψ : Pred X}
    (h : (fun p : X × I => φ p.1 p.2) ⊢ₚ (fun p => ψ p.1)) :
    (fun x => RProp.ex I (fun i => φ x i)) ⊢ₚ ψ := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun x hh a ⟨i, hi⟩ => hr (x, i) hh a hi⟩

/-- Existential monotonicity: a uniform map on the bodies lifts to the `∃`s. -/
theorem PLe.ex_mono {X I : Type} {φ ψ : X → I → RProp}
    (h : (fun p : X × I => φ p.1 p.2) ⊢ₚ (fun p => ψ p.1 p.2)) :
    (fun x => RProp.ex I (fun i => φ x i)) ⊢ₚ (fun x => RProp.ex I (fun i => ψ x i)) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun x hh a ⟨i, hi⟩ => ⟨i, hr (x, i) hh a hi⟩⟩

/-- Frobenius reciprocity: `ρ ⊓ ∃ i. φ i ⊢ ∃ i. (ρ ⊓ φ i)` (the realizer is just
the pair, untouched — `I`). The key fact letting `⊓` pass through the tripos `∃`. -/
theorem PLe.frobenius {X I : Type} (ρ : Pred X) (φ : X → I → RProp) :
    (fun x => ρ x ⊓ᵣ RProp.ex I (fun i => φ x i)) ⊢ₚ
      (fun x => RProp.ex I (fun i => ρ x ⊓ᵣ φ x i)) := by
  refine ⟨Code.I, fun x _ a ha => ?_⟩
  obtain ⟨p, e, hred, hp, i, hi⟩ := ha
  exact ⟨i, p, e, Code.Reds.trans Code.Reds.i hred, hp, hi⟩

/-- A conjunction of two existentials pulls out to a double existential (the pair
of realizers is reused — `I`). Used to expose both witnesses before eliminating. -/
theorem PLe.ex_and_ex {X I J : Type} (φ : X → I → RProp) (ψ : X → J → RProp) :
    (fun x => RProp.ex I (fun i => φ x i) ⊓ᵣ RProp.ex J (fun j => ψ x j)) ⊢ₚ
      (fun x => RProp.ex I (fun i => RProp.ex J (fun j => φ x i ⊓ᵣ ψ x j))) := by
  refine ⟨Code.I, fun x _ a ha => ?_⟩
  obtain ⟨p, q, hred, ⟨i, hp⟩, j, hq⟩ := ha
  exact ⟨i, j, p, q, Code.Reds.trans Code.Reds.i hred, hp, hq⟩

/-- Swap two existential quantifiers (the realizer is untouched — `I`). -/
theorem PLe.ex_swap {X I J : Type} (φ : X → I → J → RProp) :
    (fun x => RProp.ex I (fun i => RProp.ex J (fun j => φ x i j))) ⊢ₚ
      (fun x => RProp.ex J (fun j => RProp.ex I (fun i => φ x i j))) := by
  refine ⟨Code.I, fun x _ a ha => ?_⟩
  obtain ⟨i, j, hij⟩ := ha
  exact ⟨j, i, (φ x i j).expReds Code.Reds.i hij⟩

/-- Left injection into a fiberwise coproduct (uniform realizer `inl`). -/
theorem PLe.inl {X : Type} (φ ψ : Pred X) : φ ⊢ₚ (fun x => φ x ⊔ᵣ ψ x) :=
  ⟨Code.inl, fun _ _ a ha => Or.inl ⟨a, Code.Reds.refl, ha⟩⟩

/-- Right injection into a fiberwise coproduct (uniform realizer `inr`). -/
theorem PLe.inr {X : Type} (φ ψ : Pred X) : ψ ⊢ₚ (fun x => φ x ⊔ᵣ ψ x) :=
  ⟨Code.inr, fun _ _ a ha => Or.inr ⟨a, Code.Reds.refl, ha⟩⟩

/-- Uncurry a double existential into one over the product index (realizer `I`). -/
theorem PLe.ex_pair {X I J : Type} (φ : X → I → J → RProp) :
    (fun x => RProp.ex I (fun i => RProp.ex J (fun j => φ x i j))) ⊢ₚ
      (fun x => RProp.ex (I × J) (fun p => φ x p.1 p.2)) := by
  refine ⟨Code.I, fun x _ a ha => ?_⟩
  obtain ⟨i, j, hij⟩ := ha
  exact ⟨(i, j), (φ x i j).expReds Code.Reds.i hij⟩

/-! ### Objects -/

/-- An object of the realizability topos (tripos-to-topos over the heap-indexed
tripos `RProp`): a carrier with a tripos-valued partial equality `rel x y` (`ρ`),
symmetric and transitive **uniformly** (in `⊢ₚ`). World-state is threaded because
`RProp` is heap-indexed; `rel x x` is the existence/extent predicate. -/
structure Obj where
  /-- the underlying carrier type -/
  carrier : Type
  /-- `rel x y` (`ρ`): the heap-indexed truth value "`x` equals `y`" -/
  rel : carrier → carrier → RProp
  /-- `ρ` is symmetric (uniformly) -/
  symm : (fun p : carrier × carrier => rel p.1 p.2) ⊢ₚ (fun p => rel p.2 p.1)
  /-- `ρ` is transitive (uniformly) -/
  trans : (fun p : carrier × carrier × carrier => rel p.1 p.2.1 ⊓ᵣ rel p.2.1 p.2.2)
            ⊢ₚ (fun p => rel p.1 p.2.2)

namespace Obj

/-- Existence / extent predicate `E x = ρ x x`. -/
def ext (A : Obj) (x : A.carrier) : RProp := A.rel x x

/-- Left extent, uniformly: `ρ x y ⊢ E x`. -/
theorem rel_ext_left (A : Obj) :
    (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ (fun p => A.rel p.1 p.1) := by
  have hand : (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ
      (fun p => A.rel p.1 p.2 ⊓ᵣ A.rel p.2 p.1) := PLe.and_intro (PLe.refl _) A.symm
  have htr := PLe.reindex (fun p : A.carrier × A.carrier => (p.1, p.2, p.1)) A.trans
  exact PLe.trans hand htr

/-- Right extent, uniformly: `ρ x y ⊢ E y`. -/
theorem rel_ext_right (A : Obj) :
    (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ (fun p => A.rel p.2 p.2) := by
  have hand : (fun p : A.carrier × A.carrier => A.rel p.1 p.2) ⊢ₚ
      (fun p => A.rel p.2 p.1 ⊓ᵣ A.rel p.1 p.2) := PLe.and_intro A.symm (PLe.refl _)
  have htr := PLe.reindex (fun p : A.carrier × A.carrier => (p.2, p.1, p.2)) A.trans
  exact PLe.trans hand htr

/-! ### Morphisms (tripos-valued functional relations) -/

/-- A morphism `A ⟶ B`: a tripos-valued relation `rel x y` ("`x` is sent to `y`")
that is strict, congruent, single-valued, and total — all **uniformly** over the
carriers. These are the maps of the topos of a tripos. -/
structure Hom (A B : Obj) where
  /-- the graph of the function, as a heap-indexed truth value -/
  rel : A.carrier → B.carrier → RProp
  /-- strict in the domain -/
  strict_dom : (fun p : A.carrier × B.carrier => rel p.1 p.2) ⊢ₚ (fun p => A.rel p.1 p.1)
  /-- strict in the codomain -/
  strict_cod : (fun p : A.carrier × B.carrier => rel p.1 p.2) ⊢ₚ (fun p => B.rel p.2 p.2)
  /-- congruent: respects both equalities -/
  congr : (fun p : A.carrier × A.carrier × B.carrier × B.carrier =>
            A.rel p.1 p.2.1 ⊓ᵣ B.rel p.2.2.1 p.2.2.2 ⊓ᵣ rel p.1 p.2.2.1)
            ⊢ₚ (fun p => rel p.2.1 p.2.2.2)
  /-- single-valued -/
  sv : (fun p : A.carrier × B.carrier × B.carrier => rel p.1 p.2.1 ⊓ᵣ rel p.1 p.2.2)
        ⊢ₚ (fun p => B.rel p.2.1 p.2.2)
  /-- total -/
  total : (fun x : A.carrier => A.rel x x) ⊢ₚ (fun x => RProp.ex B.carrier (fun y => rel x y))

/-- The identity morphism: its graph is the equality `ρ` itself. -/
def Hom.id (A : Obj) : Hom A A where
  rel := A.rel
  strict_dom := A.rel_ext_left
  strict_cod := A.rel_ext_right
  total := PLe.ex_intro (fun x y => A.rel x y) (fun x => x)
  congr := by
    -- (ρ x x' ⊓ ρ y y' ⊓ ρ x y) ⊢ ρ x' y'   at p = (x, x', y, y')
    have h_xx' := PLe.trans
      (PLe.and_left (X := A.carrier × A.carrier × A.carrier × A.carrier)
        (fun p => A.rel p.1 p.2.1 ⊓ᵣ A.rel p.2.2.1 p.2.2.2) (fun p => A.rel p.1 p.2.2.1))
      (PLe.and_left (fun p : A.carrier × A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1)
        (fun p => A.rel p.2.2.1 p.2.2.2))
    have h_yy' := PLe.trans
      (PLe.and_left (X := A.carrier × A.carrier × A.carrier × A.carrier)
        (fun p => A.rel p.1 p.2.1 ⊓ᵣ A.rel p.2.2.1 p.2.2.2) (fun p => A.rel p.1 p.2.2.1))
      (PLe.and_right (fun p : A.carrier × A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1)
        (fun p => A.rel p.2.2.1 p.2.2.2))
    have h_xy := PLe.and_right
      (fun p : A.carrier × A.carrier × A.carrier × A.carrier =>
        A.rel p.1 p.2.1 ⊓ᵣ A.rel p.2.2.1 p.2.2.2)
      (fun p => A.rel p.1 p.2.2.1)
    -- ρ x' x  from  ρ x x'
    have h_x'x := PLe.trans h_xx'
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier × A.carrier => (p.1, p.2.1)) A.symm)
    -- ρ x' y  from  ρ x' x ⊓ ρ x y
    have h_x'y := PLe.trans (PLe.and_intro h_x'x h_xy)
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier × A.carrier =>
        (p.2.1, p.1, p.2.2.1)) A.trans)
    -- ρ x' y'  from  ρ x' y ⊓ ρ y y'
    exact PLe.trans (PLe.and_intro h_x'y h_yy')
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier × A.carrier =>
        (p.2.1, p.2.2.1, p.2.2.2)) A.trans)
  sv := by
    -- (ρ x y ⊓ ρ x y') ⊢ ρ y y'   at p = (x, y, y')
    have h_xy := PLe.and_left
      (fun p : A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1) (fun p => A.rel p.1 p.2.2)
    have h_xy' := PLe.and_right
      (fun p : A.carrier × A.carrier × A.carrier => A.rel p.1 p.2.1) (fun p => A.rel p.1 p.2.2)
    have h_yx := PLe.trans h_xy
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier => (p.1, p.2.1)) A.symm)
    exact PLe.trans (PLe.and_intro h_yx h_xy')
      (PLe.reindex (fun p : A.carrier × A.carrier × A.carrier => (p.2.1, p.1, p.2.2)) A.trans)

/-- Composition of morphisms: the relational composite `(G ∘ F) x z = ∃ y, F x y ∧
G y z`. The five functional-relation axioms are the coherence check for the whole
tripos-to-topos setup. -/
def Hom.comp {A B C : Obj} (F : Hom A B) (G : Hom B C) : Hom A C where
  rel x z := RProp.ex B.carrier (fun y => F.rel x y ⊓ᵣ G.rel y z)
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
        (fun p => RProp.ex C.carrier (fun z => G.rel p.2 z)) :=
      PLe.trans F.strict_cod (PLe.reindex (fun p : A.carrier × B.carrier => p.2) G.total)
    have hinner : (fun q : (A.carrier × B.carrier) × C.carrier =>
          F.rel q.1.1 q.1.2 ⊓ᵣ G.rel q.1.2 q.2) ⊢ₚ
        (fun q => RProp.ex B.carrier (fun y => F.rel q.1.1 y ⊓ᵣ G.rel y q.2)) :=
      PLe.ex_intro
        (fun q : (A.carrier × B.carrier) × C.carrier =>
          fun y => F.rel q.1.1 y ⊓ᵣ G.rel y q.2)
        (fun q => q.1.2)
    have hyp : (fun p : A.carrier × B.carrier => F.rel p.1 p.2) ⊢ₚ
        (fun p => RProp.ex C.carrier (fun z =>
          RProp.ex B.carrier (fun y => F.rel p.1 y ⊓ᵣ G.rel y z))) :=
      PLe.trans (PLe.and_intro (PLe.refl _) hGtot)
        (PLe.trans (PLe.frobenius (fun p : A.carrier × B.carrier => F.rel p.1 p.2)
          (fun p z => G.rel p.2 z)) (PLe.ex_mono hinner))
    exact PLe.trans F.total (PLe.ex_elim hyp)
  sv := by
    refine PLe.trans (PLe.ex_and_ex
      (fun p : A.carrier × C.carrier × C.carrier => fun y => F.rel p.1 y ⊓ᵣ G.rel y p.2.1)
      (fun p : A.carrier × C.carrier × C.carrier => fun y => F.rel p.1 y ⊓ᵣ G.rel y p.2.2)) ?_
    apply PLe.ex_elim
    apply PLe.ex_elim
    -- q : ((A×C×C)×B)×B ;  x=q.1.1.1 z₁=q.1.1.2.1 z₂=q.1.1.2.2 y=q.1.2 y'=q.2
    have hFxy : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ᵣ G.rel q.1.2 q.1.1.2.1) ⊓ᵣ
          (F.rel q.1.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => F.rel q.1.1.1 q.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hGyz1 : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ᵣ G.rel q.1.2 q.1.1.2.1) ⊓ᵣ
          (F.rel q.1.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => G.rel q.1.2 q.1.1.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hFxy' : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ᵣ G.rel q.1.2 q.1.1.2.1) ⊓ᵣ
          (F.rel q.1.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => F.rel q.1.1.1 q.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hGy'z2 : (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (F.rel q.1.1.1 q.1.2 ⊓ᵣ G.rel q.1.2 q.1.1.2.1) ⊓ᵣ
          (F.rel q.1.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.1.2.2)) ⊢ₚ (fun q => G.rel q.2 q.1.1.2.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_right _ _)
    -- y ≈ y' from F single-valued
    have hyy' := PLe.trans (PLe.and_intro hFxy hFxy')
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.1.1.1, q.1.2, q.2)) F.sv)
    -- E z₂  from G strict in codomain
    have hCz2 := PLe.trans hGy'z2
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.2, q.1.1.2.2)) G.strict_cod)
    -- y' ≈ y
    have hy'y := PLe.trans hyy'
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.1.2, q.2)) B.symm)
    -- G y z₂  by congruence from G y' z₂
    have hGyz2 := PLe.trans (PLe.and_intro (PLe.and_intro hy'y hCz2) hGy'z2)
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.2, q.1.2, q.1.1.2.2, q.1.1.2.2)) G.congr)
    -- z₁ ≈ z₂  from G single-valued
    exact PLe.trans (PLe.and_intro hGyz1 hGyz2)
      (PLe.reindex (fun q : ((A.carrier × C.carrier × C.carrier) × B.carrier) × B.carrier =>
        (q.1.2, q.1.1.2.1, q.1.1.2.2)) G.sv)
  congr := by
    refine PLe.trans (PLe.frobenius
      (fun p : A.carrier × A.carrier × C.carrier × C.carrier =>
        A.rel p.1 p.2.1 ⊓ᵣ C.rel p.2.2.1 p.2.2.2)
      (fun p => fun y => F.rel p.1 y ⊓ᵣ G.rel y p.2.2.1)) ?_
    apply PLe.ex_elim
    -- q : (A×A×C×C)×B ;  x=q.1.1 x'=q.1.2.1 z=q.1.2.2.1 z'=q.1.2.2.2 y=q.2
    have hAxx' : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ᵣ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ᵣ
          (F.rel q.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => A.rel q.1.1 q.1.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hCzz' : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ᵣ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ᵣ
          (F.rel q.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => C.rel q.1.2.2.1 q.1.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hFxy : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ᵣ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ᵣ
          (F.rel q.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => F.rel q.1.1 q.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hGyz : (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (A.rel q.1.1 q.1.2.1 ⊓ᵣ C.rel q.1.2.2.1 q.1.2.2.2) ⊓ᵣ
          (F.rel q.1.1 q.2 ⊓ᵣ G.rel q.2 q.1.2.2.1)) ⊢ₚ (fun q => G.rel q.2 q.1.2.2.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_right _ _)
    -- E y from F strict in codomain
    have hByy := PLe.trans hFxy
      (PLe.reindex (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (q.1.1, q.2)) F.strict_cod)
    -- F x' y by congruence from F x y
    have hFx'y := PLe.trans (PLe.and_intro (PLe.and_intro hAxx' hByy) hFxy)
      (PLe.reindex (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (q.1.1, q.1.2.1, q.2, q.2)) F.congr)
    -- G y z' by congruence from G y z
    have hGyz' := PLe.trans (PLe.and_intro (PLe.and_intro hByy hCzz') hGyz)
      (PLe.reindex (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
        (q.2, q.2, q.1.2.2.1, q.1.2.2.2)) G.congr)
    -- assemble F x' y ⊓ G y z'  and inject at witness y' := y
    exact PLe.trans (PLe.and_intro hFx'y hGyz')
      (PLe.ex_intro
        (fun q : (A.carrier × A.carrier × C.carrier × C.carrier) × B.carrier =>
          fun y' => F.rel q.1.2.1 y' ⊓ᵣ G.rel y' q.1.2.2.2)
        (fun q => q.2))

/-- Equality of parallel morphisms: their graphs are equivalent in the tripos
(mutually entailing). This is the equality of `Hom`-sets in the topos. -/
def HomEq {A B : Obj} (F G : Hom A B) : Prop :=
  ((fun p : A.carrier × B.carrier => F.rel p.1 p.2) ⊢ₚ (fun p => G.rel p.1 p.2)) ∧
    ((fun p : A.carrier × B.carrier => G.rel p.1 p.2) ⊢ₚ (fun p => F.rel p.1 p.2))

/-- Left identity law: `id ∘ F = F`. -/
theorem Hom.id_comp {A B : Obj} (F : Hom A B) : HomEq (Hom.comp (Hom.id A) F) F := by
  constructor
  · -- ∃ y, ρ_A x y ⊓ F y z  ⊢  F x z
    apply PLe.ex_elim
    have hAxy : (fun q : (A.carrier × B.carrier) × A.carrier =>
        A.rel q.1.1 q.2 ⊓ᵣ F.rel q.2 q.1.2) ⊢ₚ (fun q => A.rel q.1.1 q.2) := PLe.and_left _ _
    have hFyz : (fun q : (A.carrier × B.carrier) × A.carrier =>
        A.rel q.1.1 q.2 ⊓ᵣ F.rel q.2 q.1.2) ⊢ₚ (fun q => F.rel q.2 q.1.2) := PLe.and_right _ _
    have hAyx := PLe.trans hAxy
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier => (q.1.1, q.2)) A.symm)
    have hBzz := PLe.trans hFyz
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier => (q.2, q.1.2)) F.strict_cod)
    exact PLe.trans (PLe.and_intro (PLe.and_intro hAyx hBzz) hFyz)
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier =>
        (q.2, q.1.1, q.1.2, q.1.2)) F.congr)
  · -- F x z  ⊢  ∃ y, ρ_A x y ⊓ F y z   (witness y := x)
    exact PLe.trans (PLe.and_intro F.strict_dom (PLe.refl _))
      (PLe.ex_intro (fun p : A.carrier × B.carrier => fun y => A.rel p.1 y ⊓ᵣ F.rel y p.2)
        (fun p => p.1))

/-- Right identity law: `F ∘ id = F`. -/
theorem Hom.comp_id {A B : Obj} (F : Hom A B) : HomEq (Hom.comp F (Hom.id B)) F := by
  constructor
  · -- ∃ y, F x y ⊓ ρ_B y z  ⊢  F x z
    apply PLe.ex_elim
    have hFxy : (fun q : (A.carrier × B.carrier) × B.carrier =>
        F.rel q.1.1 q.2 ⊓ᵣ B.rel q.2 q.1.2) ⊢ₚ (fun q => F.rel q.1.1 q.2) := PLe.and_left _ _
    have hByz : (fun q : (A.carrier × B.carrier) × B.carrier =>
        F.rel q.1.1 q.2 ⊓ᵣ B.rel q.2 q.1.2) ⊢ₚ (fun q => B.rel q.2 q.1.2) := PLe.and_right _ _
    have hAxx := PLe.trans hFxy
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier => (q.1.1, q.2)) F.strict_dom)
    exact PLe.trans (PLe.and_intro (PLe.and_intro hAxx hByz) hFxy)
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier =>
        (q.1.1, q.1.1, q.2, q.1.2)) F.congr)
  · -- F x z  ⊢  ∃ y, F x y ⊓ ρ_B y z   (witness y := z)
    exact PLe.trans (PLe.and_intro (PLe.refl _) F.strict_cod)
      (PLe.ex_intro (fun p : A.carrier × B.carrier => fun y => F.rel p.1 y ⊓ᵣ B.rel y p.2)
        (fun p => p.2))

/-! ### Binary products -/

/-- The binary product `A × B`: pairs, with componentwise equality. -/
def prod (A B : Obj) : Obj where
  carrier := A.carrier × B.carrier
  rel p q := A.rel p.1 q.1 ⊓ᵣ B.rel p.2 q.2
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
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ᵣ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ᵣ B.rel p.2.1.2 p.2.2.2))
      (PLe.and_left (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.1.1 p.2.1.1) (fun p => B.rel p.1.2 p.2.1.2))
    have hA2 := PLe.trans
      (PLe.and_right (X := (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier)
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ᵣ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ᵣ B.rel p.2.1.2 p.2.2.2))
      (PLe.and_left (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.2.1.1 p.2.2.1) (fun p => B.rel p.2.1.2 p.2.2.2))
    have hB1 := PLe.trans
      (PLe.and_left (X := (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier)
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ᵣ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ᵣ B.rel p.2.1.2 p.2.2.2))
      (PLe.and_right (fun p : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        A.rel p.1.1 p.2.1.1) (fun p => B.rel p.1.2 p.2.1.2))
    have hB2 := PLe.trans
      (PLe.and_right (X := (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × B.carrier)
        (fun p => A.rel p.1.1 p.2.1.1 ⊓ᵣ B.rel p.1.2 p.2.1.2)
        (fun p => A.rel p.2.1.1 p.2.2.1 ⊓ᵣ B.rel p.2.1.2 p.2.2.2))
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
  rel p a' := A.rel p.1 a' ⊓ᵣ B.rel p.2 p.2
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
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ A.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (A.rel q.1.1 q.2.2.1 ⊓ᵣ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.1.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_left _ _))
    have hBpp' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ A.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (A.rel q.1.1 q.2.2.1 ⊓ᵣ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => B.rel q.1.2 q.2.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_right _ _))
    have ha'a'' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ A.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (A.rel q.1.1 q.2.2.1 ⊓ᵣ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.2.2.1 q.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hpa' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ A.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (A.rel q.1.1 q.2.2.1 ⊓ᵣ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.2.1) :=
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
        (A.rel q.1.1 q.2.1 ⊓ᵣ B.rel q.1.2 q.1.2) ⊓ᵣ
          (A.rel q.1.1 q.2.2 ⊓ᵣ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hpa'' : (fun q : (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (A.rel q.1.1 q.2.1 ⊓ᵣ B.rel q.1.2 q.1.2) ⊓ᵣ
          (A.rel q.1.1 q.2.2 ⊓ᵣ B.rel q.1.2 q.1.2)) ⊢ₚ (fun q => A.rel q.1.1 q.2.2) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have ha'p := PLe.trans hpa'
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.1.1, q.2.1)) A.symm)
    exact PLe.trans (PLe.and_intro ha'p hpa'')
      (PLe.reindex (fun q : (A.carrier × B.carrier) × A.carrier × A.carrier =>
        (q.2.1, q.1.1, q.2.2)) A.trans)
  total := PLe.ex_intro
    (fun (p : A.carrier × B.carrier) => fun a' => A.rel p.1 a' ⊓ᵣ B.rel p.2 p.2) (fun p => p.1)

/-- Second projection `π₂ : A × B ⟶ B`. -/
def Hom.snd (A B : Obj) : Hom (prod A B) B where
  rel p b' := B.rel p.2 b' ⊓ᵣ A.rel p.1 p.1
  strict_dom := by
    have hB := PLe.trans
      (PLe.and_left (fun q : (A.carrier × B.carrier) × B.carrier => B.rel q.1.2 q.2)
        (fun q => A.rel q.1.1 q.1.1))
      (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier => (q.1.2, q.2)) B.rel_ext_left)
    have hA := PLe.and_right
      (fun q : (A.carrier × B.carrier) × B.carrier => B.rel q.1.2 q.2) (fun q => A.rel q.1.1 q.1.1)
    -- need (prod A B).rel p p = A.rel p.1 p.1 ⊓ᵣ B.rel p.2 p.2
    exact PLe.and_intro hA hB
  strict_cod := PLe.trans
    (PLe.and_left (fun q : (A.carrier × B.carrier) × B.carrier => B.rel q.1.2 q.2)
      (fun q => A.rel q.1.1 q.1.1))
    (PLe.reindex (fun q : (A.carrier × B.carrier) × B.carrier => (q.1.2, q.2)) B.rel_ext_right)
  congr := by
    have hpp'B : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ B.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (B.rel q.1.2 q.2.2.1 ⊓ᵣ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_right _ _))
    have hApp' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ B.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (B.rel q.1.2 q.2.2.1 ⊓ᵣ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => A.rel q.1.1 q.2.1.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_left _ _) (PLe.and_left _ _))
    have hb'b'' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ B.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (B.rel q.1.2 q.2.2.1 ⊓ᵣ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.2.2.1 q.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hpb' : (fun q : (A.carrier × B.carrier) × (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (A.rel q.1.1 q.2.1.1 ⊓ᵣ B.rel q.1.2 q.2.1.2 ⊓ᵣ B.rel q.2.2.1 q.2.2.2) ⊓ᵣ
          (B.rel q.1.2 q.2.2.1 ⊓ᵣ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.2.1) :=
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
        (B.rel q.1.2 q.2.1 ⊓ᵣ A.rel q.1.1 q.1.1) ⊓ᵣ
          (B.rel q.1.2 q.2.2 ⊓ᵣ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hpb'' : (fun q : (A.carrier × B.carrier) × B.carrier × B.carrier =>
        (B.rel q.1.2 q.2.1 ⊓ᵣ A.rel q.1.1 q.1.1) ⊓ᵣ
          (B.rel q.1.2 q.2.2 ⊓ᵣ A.rel q.1.1 q.1.1)) ⊢ₚ (fun q => B.rel q.1.2 q.2.2) :=
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
      (fun (p : A.carrier × B.carrier) => fun b' => B.rel p.2 b' ⊓ᵣ A.rel p.1 p.1) (fun p => p.2))

/-- Pairing `⟨f, g⟩ : C ⟶ A × B`, the universal map into the product. -/
def Hom.pair {C A B : Obj} (f : Hom C A) (g : Hom C B) : Hom C (prod A B) where
  rel c p := f.rel c p.1 ⊓ᵣ g.rel c p.2
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
        (C.rel q.1 q.2.1 ⊓ᵣ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ᵣ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ᵣ
          (f.rel q.1 q.2.2.1.1 ⊓ᵣ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => C.rel q.1 q.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hAaa' : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ᵣ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ᵣ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ᵣ
          (f.rel q.1 q.2.2.1.1 ⊓ᵣ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => A.rel q.2.2.1.1 q.2.2.2.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_right _ _) (PLe.and_left _ _))
    have hBbb' : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ᵣ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ᵣ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ᵣ
          (f.rel q.1 q.2.2.1.1 ⊓ᵣ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => B.rel q.2.2.1.2 q.2.2.2.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.trans (PLe.and_right _ _) (PLe.and_right _ _))
    have hfca : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ᵣ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ᵣ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ᵣ
          (f.rel q.1 q.2.2.1.1 ⊓ᵣ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => f.rel q.1 q.2.2.1.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hgcb : (fun q : C.carrier × C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (C.rel q.1 q.2.1 ⊓ᵣ (A.rel q.2.2.1.1 q.2.2.2.1 ⊓ᵣ B.rel q.2.2.1.2 q.2.2.2.2)) ⊓ᵣ
          (f.rel q.1 q.2.2.1.1 ⊓ᵣ g.rel q.1 q.2.2.1.2)) ⊢ₚ (fun q => g.rel q.1 q.2.2.1.2) :=
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
        (f.rel q.1 q.2.1.1 ⊓ᵣ g.rel q.1 q.2.1.2) ⊓ᵣ
          (f.rel q.1 q.2.2.1 ⊓ᵣ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => f.rel q.1 q.2.1.1) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    have hfa' : (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (f.rel q.1 q.2.1.1 ⊓ᵣ g.rel q.1 q.2.1.2) ⊓ᵣ
          (f.rel q.1 q.2.2.1 ⊓ᵣ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => f.rel q.1 q.2.2.1) :=
      PLe.trans (PLe.and_right _ _) (PLe.and_left _ _)
    have hgb : (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (f.rel q.1 q.2.1.1 ⊓ᵣ g.rel q.1 q.2.1.2) ⊓ᵣ
          (f.rel q.1 q.2.2.1 ⊓ᵣ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => g.rel q.1 q.2.1.2) :=
      PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hgb' : (fun q : C.carrier × (A.carrier × B.carrier) × A.carrier × B.carrier =>
        (f.rel q.1 q.2.1.1 ⊓ᵣ g.rel q.1 q.2.1.2) ⊓ᵣ
          (f.rel q.1 q.2.2.1 ⊓ᵣ g.rel q.1 q.2.2.2)) ⊢ₚ (fun q => g.rel q.1 q.2.2.2) :=
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
      (PLe.ex_pair (fun (c : C.carrier) => fun a b => f.rel c a ⊓ᵣ g.rel c b)))

/-! ### Terminal object, propositions, and truncation -/

/-- The terminal object `1`: a single element, always-true equality. -/
def one : Obj where
  carrier := Unit
  rel _ _ := RProp.top
  symm := ⟨Code.I, fun _ _ _ _ => trivial⟩
  trans := ⟨Code.I, fun _ _ _ _ => trivial⟩

/-- A proposition (subobject of `1`) presented by a truth value `P`: one formal
element whose self-equality is `P`. -/
def prop (P : RProp) : Obj where
  carrier := Unit
  rel _ _ := P
  symm := PLe.refl _
  trans := PLe.and_left _ _

/-- An object is a **proposition** (subsingleton) when any two realized elements
are equal: `E x ⊓ E y ⊢ ρ x y`. -/
def ObjIsProp (Q : Obj) : Prop :=
  (fun p : Q.carrier × Q.carrier => Q.rel p.1 p.1 ⊓ᵣ Q.rel p.2 p.2) ⊢ₚ (fun p => Q.rel p.1 p.2)

theorem prop_isProp (P : RProp) : ObjIsProp (prop P) := PLe.and_left _ _

/-- Propositional truncation `‖A‖` = the **support** of `A`: the proposition
"`A` is inhabited", `∃ x, E_A x`. A realizer is a realizer of `∃ x, E_A x` — i.e. a
realizer of *some* element of `A`, with the index `x` hidden but the realizer kept.
Hence witness-preserving, yet a subsingleton via its (trivial) equality. -/
def trunc (A : Obj) : Obj := prop (RProp.ex A.carrier (fun x => A.rel x x))

theorem trunc_isProp (A : Obj) : ObjIsProp (trunc A) := prop_isProp _

/-- **Decidable equality** of an object `A`, internally: a uniform realizer that,
for every pair `(x, y)`, decides `ρ_A x y` — i.e. realizes the coproduct
`(x = y) + ¬(x = y)`. This is the realizability reading of the `AC_dec` premise
`Π x y. (x = y) + ¬(x = y)`; the realizer is what keys the memo cache. -/
def HasDecEq (A : Obj) : Prop :=
  (fun _ : A.carrier × A.carrier => RProp.top) ⊢ₚ
    (fun p => A.rel p.1 p.2 ⊔ᵣ (A.rel p.1 p.2 ⇨ᵣ RProp.bot))

/-- The terminal object has decidable equality (everything is equal — decide `inl`). -/
theorem hasDecEq_one : HasDecEq one :=
  PLe.inl (fun _ : Unit × Unit => RProp.top) (fun p => one.rel p.1 p.2 ⇨ᵣ RProp.bot)

/-- The truncation unit `η : A ⟶ ‖A‖`. -/
def Hom.toTrunc (A : Obj) : Hom A (trunc A) where
  rel x _ := A.rel x x
  strict_dom := PLe.refl _
  strict_cod :=
    PLe.ex_intro (fun (p : A.carrier × Unit) => fun x => A.rel x x) (fun p => p.1)
  congr := by
    have hxx' : (fun p : A.carrier × A.carrier × Unit × Unit =>
        A.rel p.1 p.2.1 ⊓ᵣ (trunc A).rel p.2.2.1 p.2.2.2 ⊓ᵣ A.rel p.1 p.1) ⊢ₚ
        (fun p => A.rel p.1 p.2.1) := PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
    exact PLe.trans hxx'
      (PLe.reindex (fun p : A.carrier × A.carrier × Unit × Unit => (p.1, p.2.1)) A.rel_ext_right)
  sv := by
    have hxx : (fun p : A.carrier × Unit × Unit => A.rel p.1 p.1 ⊓ᵣ A.rel p.1 p.1) ⊢ₚ
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
  rel _ y := RProp.ex A.carrier (fun x => f.rel x y)
  strict_dom :=
    PLe.ex_mono (PLe.reindex (fun q : (Unit × Q.carrier) × A.carrier => (q.2, q.1.2)) f.strict_dom)
  strict_cod :=
    PLe.ex_elim (PLe.reindex (fun q : (Unit × Q.carrier) × A.carrier => (q.2, q.1.2)) f.strict_cod)
  total := by
    have h1 : (fun u : Unit => RProp.ex A.carrier (fun x => A.rel x x)) ⊢ₚ
        (fun u => RProp.ex A.carrier (fun x => RProp.ex Q.carrier (fun y => f.rel x y))) :=
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
        (trunc A).rel p.1 p.2.1 ⊓ᵣ Q.rel p.2.2.1 p.2.2.2 ⊓ᵣ
          RProp.ex A.carrier (fun x => f.rel x p.2.2.1)) ⊢ₚ
        (fun p => Q.rel p.2.2.1 p.2.2.2) := PLe.trans (PLe.and_left _ _) (PLe.and_right _ _)
    have hex : (fun p : Unit × Unit × Q.carrier × Q.carrier =>
        (trunc A).rel p.1 p.2.1 ⊓ᵣ Q.rel p.2.2.1 p.2.2.2 ⊓ᵣ
          RProp.ex A.carrier (fun x => f.rel x p.2.2.1)) ⊢ₚ
        (fun p => RProp.ex A.carrier (fun x => f.rel x p.2.2.1)) := PLe.and_right _ _
    refine PLe.trans (PLe.and_intro hQyy' hex)
      (PLe.trans (PLe.frobenius
        (fun p : Unit × Unit × Q.carrier × Q.carrier => Q.rel p.2.2.1 p.2.2.2)
        (fun p => fun x => f.rel x p.2.2.1)) ?_)
    apply PLe.ex_mono
    -- q : (Unit×Unit×Q×Q)×A ; y=q.1.2.2.1 y'=q.1.2.2.2 x=q.2
    have hQ' : (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        Q.rel q.1.2.2.1 q.1.2.2.2 ⊓ᵣ f.rel q.2 q.1.2.2.1) ⊢ₚ
        (fun q => Q.rel q.1.2.2.1 q.1.2.2.2) := PLe.and_left _ _
    have hfxy : (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        Q.rel q.1.2.2.1 q.1.2.2.2 ⊓ᵣ f.rel q.2 q.1.2.2.1) ⊢ₚ
        (fun q => f.rel q.2 q.1.2.2.1) := PLe.and_right _ _
    have hExx := PLe.trans hfxy
      (PLe.reindex (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        (q.2, q.1.2.2.1)) f.strict_dom)
    exact PLe.trans (PLe.and_intro (PLe.and_intro hExx hQ') hfxy)
      (PLe.reindex (fun q : (Unit × Unit × Q.carrier × Q.carrier) × A.carrier =>
        (q.2, q.2, q.1.2.2.1, q.1.2.2.2)) f.congr)

end Obj

end LeanStatefulAoc
