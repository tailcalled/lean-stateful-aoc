import LeanStatefulAoc.RTopos

set_option linter.style.longLine false

/-!
# Dependent families and the dependent product (Layer 3)

For the headline to be a single morphism *inside* the topos —
`AC_dec : prem ⟶ ‖Π x:A. B x‖` — we need the **dependent product** as a genuine
object. A dependent family over `A` is, categorically, an object of the slice
category `T/A`: a **display map** `p : E ⟶ A`. The fibre `B(x)` is the pullback
along `x`, and the dependent product `Π_A` is the right adjoint to pullback along
`A → 1` — concretely the **object of sections** of `p`, a subobject of the
exponential `E^A` (those `f : A ⟶ E` with `p ∘ f = id_A`).

(The earlier `A.carrier → Obj` indexing was only faithful for *discrete* `A`: it
ignores `ρ_A`, so for non-discrete `A` it silently builds the product over the
discrete reflection. The display-map presentation respects `ρ_A` by construction —
`E` is one object with one equality `ρ_E`.)

This file builds the plumbing the construction needs:
* `pairAp` — assemble `pr · (fst e a) · (snd e a)` (for merging proofs);
* `C` — the flip combinator `C f x y ↠ f y x`, needed for the **off-diagonal**
  realizers of the exponential (`f ≈ g` iff `ρ_A`-related inputs go to
  `ρ_B`-related outputs, so `symm`/`trans` must transport the `A`-side realizer);
* `Family` — a display map `p : E ⟶ A`.

The exponential `E^A` and the section object `Π_A p` are built on top of these.
-/

namespace LeanStatefulAoc

open Code Obj

/-! ### Plumbing combinators -/

/-- `pairAp · e · a ↠ pr · (fst e a) · (snd e a)`: a closed combinator assembling a
pair from the two projections of `e`, each applied to `a`. -/
def Code.pairAp : Code :=
  S ⬝ (B ⬝ S ⬝ (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I))) ⬝ (B ⬝ snd ⬝ I)

theorem Code.pairAp_app (e a : Code) :
    Code.Reds (Code.pairAp ⬝ e ⬝ a) (pr ⬝ (fst ⬝ e ⬝ a) ⬝ (snd ⬝ e ⬝ a)) := by
  have hR' : Code.Reds (B ⬝ fst ⬝ I ⬝ e) (fst ⬝ e) :=
    .trans (Code.B_app fst I e) (Code.Reds.appR fst Code.Reds.i)
  have hR : Code.Reds (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I) ⬝ e) (B ⬝ pr ⬝ (fst ⬝ e)) :=
    .trans (Code.B_app (B ⬝ pr) (B ⬝ fst ⬝ I) e) (Code.Reds.appR (B ⬝ pr) hR')
  have hP : Code.Reds (B ⬝ S ⬝ (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I)) ⬝ e)
      (S ⬝ (B ⬝ pr ⬝ (fst ⬝ e))) :=
    .trans (Code.B_app S (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I)) e) (Code.Reds.appR S hR)
  have hQ : Code.Reds (B ⬝ snd ⬝ I ⬝ e) (snd ⬝ e) :=
    .trans (Code.B_app snd I e) (Code.Reds.appR snd Code.Reds.i)
  have hPe : Code.Reds (Code.pairAp ⬝ e) (S ⬝ (B ⬝ pr ⬝ (fst ⬝ e)) ⬝ (snd ⬝ e)) := by
    refine .trans (.single Code.Red.s) ?_
    exact .trans (Code.Reds.appL hP _) (Code.Reds.appR _ hQ)
  refine .trans (Code.Reds.appL hPe a) ?_
  refine .trans (.single Code.Red.s) ?_
  exact .trans (Code.Reds.appL (Code.B_app pr (fst ⬝ e) a) _) Code.Reds.refl

/-- The flip combinator `C = S (B B S) (K K)`, with `C · f · x · y ↠ f · y · x`. -/
def Code.C : Code := S ⬝ (B ⬝ B ⬝ S) ⬝ (K ⬝ K)

theorem Code.C_app (f x y : Code) : Code.Reds (Code.C ⬝ f ⬝ x ⬝ y) (f ⬝ y ⬝ x) := by
  have h1 : Code.Reds (Code.C ⬝ f) (B ⬝ (S ⬝ f) ⬝ K) :=
    .trans (.single Code.Red.s)
      (.trans (Code.Reds.appL (Code.B_app B S f) _) (Code.Reds.appR _ (.single Code.Red.k)))
  have h2 : Code.Reds (Code.C ⬝ f ⬝ x) (S ⬝ f ⬝ (K ⬝ x)) :=
    .trans (Code.Reds.appL h1 x) (Code.B_app (S ⬝ f) K x)
  refine .trans (Code.Reds.appL h2 y) ?_
  exact .trans (.single Code.Red.s) (Code.Reds.appR (f ⬝ y) (.single Code.Red.k))

/-- `pairApR eR · e · a ↠ pr · (fst e a) · (snd e (eR a))`: like `pairAp` but the
second projection is fed `eR · a` (used to insert an extent realizer on one side
of the exponential's transitivity). -/
def Code.pairApR (eR : Code) : Code :=
  S ⬝ (B ⬝ S ⬝ (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I))) ⬝ (Code.C ⬝ (B ⬝ B ⬝ snd) ⬝ eR)

theorem Code.pairApR_app (eR e a : Code) :
    Code.Reds (Code.pairApR eR ⬝ e ⬝ a) (pr ⬝ (fst ⬝ e ⬝ a) ⬝ (snd ⬝ e ⬝ (eR ⬝ a))) := by
  have hR' : Code.Reds (B ⬝ fst ⬝ I ⬝ e) (fst ⬝ e) :=
    .trans (Code.B_app fst I e) (Code.Reds.appR fst Code.Reds.i)
  have hR : Code.Reds (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I) ⬝ e) (B ⬝ pr ⬝ (fst ⬝ e)) :=
    .trans (Code.B_app (B ⬝ pr) (B ⬝ fst ⬝ I) e) (Code.Reds.appR (B ⬝ pr) hR')
  have hP : Code.Reds (B ⬝ S ⬝ (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I)) ⬝ e)
      (S ⬝ (B ⬝ pr ⬝ (fst ⬝ e))) :=
    .trans (Code.B_app S (B ⬝ (B ⬝ pr) ⬝ (B ⬝ fst ⬝ I)) e) (Code.Reds.appR S hR)
  have hQ' : Code.Reds (Code.C ⬝ (B ⬝ B ⬝ snd) ⬝ eR ⬝ e) (B ⬝ (snd ⬝ e) ⬝ eR) :=
    .trans (Code.C_app (B ⬝ B ⬝ snd) eR e) (Code.Reds.appL (Code.B_app B snd e) eR)
  have hPe : Code.Reds (Code.pairApR eR ⬝ e) (S ⬝ (B ⬝ pr ⬝ (fst ⬝ e)) ⬝ (B ⬝ (snd ⬝ e) ⬝ eR)) := by
    refine .trans (.single Code.Red.s) ?_
    exact .trans (Code.Reds.appL hP _) (Code.Reds.appR _ hQ')
  refine .trans (Code.Reds.appL hPe a) ?_
  refine .trans (.single Code.Red.s) ?_
  exact .trans (Code.Reds.appL (Code.B_app pr (fst ⬝ e) a) _)
    (Code.Reds.appR _ (Code.B_app (snd ⬝ e) eR a))

/-! ### The exponential object `B ^ A` -/

/-- The exponential `B ^ A` (function space): functions `A.carrier → B.carrier`,
with `f ≈ g` realized by codes that send `ρ_A`-related inputs to `ρ_B`-related
outputs. The `symm`/`transitivity` realizers are **off-diagonal**: they transport
the `A`-side realizer (`C`/extent) before/while applying the `B`-side structure. -/
def Obj.expn (A B : Obj) : Obj where
  carrier := A.carrier → B.carrier
  rel f g :=
    { rel := fun h c => ∀ (x x' : A.carrier) (a : Code),
        (A.rel x x').rel h a → (B.rel (f x) (g x')).rel h (c ⬝ a)
      exp := fun r hc x x' a ha => (B.rel (f x) (g x')).exp (Code.Red.appL r) (hc x x' a ha) }
  symm := by
    obtain ⟨sA, hsA⟩ := A.symm
    obtain ⟨sB, hsB⟩ := B.symm
    refine ⟨Code.B ⬝ (Code.B ⬝ sB) ⬝ (Code.C ⬝ Code.B ⬝ sA), fun p h c hc x x' a ha => ?_⟩
    have hred : Code.Reds ((Code.B ⬝ (Code.B ⬝ sB) ⬝ (Code.C ⬝ Code.B ⬝ sA) ⬝ c) ⬝ a)
        (sB ⬝ (c ⬝ (sA ⬝ a))) := by
      have h1 : Code.Reds (Code.B ⬝ (Code.B ⬝ sB) ⬝ (Code.C ⬝ Code.B ⬝ sA) ⬝ c)
          (Code.B ⬝ sB ⬝ (Code.B ⬝ c ⬝ sA)) :=
        .trans (Code.B_app (Code.B ⬝ sB) (Code.C ⬝ Code.B ⬝ sA) c)
          (Code.Reds.appR (Code.B ⬝ sB) (Code.C_app Code.B sA c))
      refine .trans (Code.Reds.appL h1 a) ?_
      exact .trans (Code.B_app sB (Code.B ⬝ c ⬝ sA) a)
        (Code.Reds.appR sB (Code.B_app c sA a))
    refine (B.rel (p.2 x) (p.1 x')).expReds hred ?_
    exact hsB (p.1 x', p.2 x) h (c ⬝ (sA ⬝ a))
      (hc x' x (sA ⬝ a) (hsA (x, x') h a ha))
  trans := by
    obtain ⟨eR, heR⟩ := A.rel_ext_right
    obtain ⟨tB, htB⟩ := B.trans
    refine ⟨Code.B ⬝ (Code.B ⬝ tB) ⬝ (Code.pairApR eR), fun p h e he x x' a ha => ?_⟩
    obtain ⟨c1, c2, hpred, hc1, hc2⟩ := he
    have hfst : Code.Reds (fst ⬝ e ⬝ a) (c1 ⬝ a) :=
      Code.Reds.appL (.trans (Code.Reds.appR fst hpred) (.single Code.Red.prL)) a
    have hsnd : Code.Reds (snd ⬝ e ⬝ (eR ⬝ a)) (c2 ⬝ (eR ⬝ a)) :=
      Code.Reds.appL (.trans (Code.Reds.appR snd hpred) (.single Code.Red.prR)) (eR ⬝ a)
    have hred : Code.Reds ((Code.B ⬝ (Code.B ⬝ tB) ⬝ (Code.pairApR eR) ⬝ e) ⬝ a)
        (tB ⬝ (pr ⬝ (c1 ⬝ a) ⬝ (c2 ⬝ (eR ⬝ a)))) := by
      have h1 : Code.Reds (Code.B ⬝ (Code.B ⬝ tB) ⬝ (Code.pairApR eR) ⬝ e)
          (Code.B ⬝ tB ⬝ (Code.pairApR eR ⬝ e)) :=
        Code.B_app (Code.B ⬝ tB) (Code.pairApR eR) e
      refine .trans (Code.Reds.appL h1 a) ?_
      refine .trans (Code.B_app tB (Code.pairApR eR ⬝ e) a) ?_
      refine Code.Reds.appR tB ?_
      exact .trans (Code.pairApR_app eR e a)
        (.trans (Code.Reds.appL (Code.Reds.appR pr hfst) _) (Code.Reds.appR _ hsnd))
    refine (B.rel (p.1 x) (p.2.2 x')).expReds hred ?_
    exact htB (p.1 x, p.2.1 x', p.2.2 x') h (pr ⬝ (c1 ⬝ a) ⬝ (c2 ⬝ (eR ⬝ a)))
      ⟨c1 ⬝ a, c2 ⬝ (eR ⬝ a), Code.Reds.refl,
        hc1 x x' a ha, hc2 x' x' (eR ⬝ a) (heR (x, x') h a ha)⟩

/-! ### Comprehension (subobjects) -/

/-- The subobject `{x : X | φ x}` carved by a predicate `φ` that **respects** the
equality of `X` (`ρ_X x y ⊓ φ x ⊢ φ y`). Its equality is `ρ_X x y ⊓ φ x`. This is
comprehension; the section object `Π_A p` is an instance (`φ = "is a section"`). -/
def Obj.sub (X : Obj) (φ : X.carrier → RProp)
    (hresp : (fun p : X.carrier × X.carrier => X.rel p.1 p.2 ⊓ᵣ φ p.1) ⊢ₚ (fun p => φ p.2)) :
    Obj where
  carrier := X.carrier
  rel x y := X.rel x y ⊓ᵣ φ x
  symm := by
    refine PLe.and_intro (PLe.trans (PLe.and_left _ _) X.symm) hresp
  trans := by
    refine PLe.and_intro ?_ ?_
    · have hxy : (fun p : X.carrier × X.carrier × X.carrier =>
          (X.rel p.1 p.2.1 ⊓ᵣ φ p.1) ⊓ᵣ (X.rel p.2.1 p.2.2 ⊓ᵣ φ p.2.1)) ⊢ₚ
          (fun p => X.rel p.1 p.2.1) := PLe.trans (PLe.and_left _ _) (PLe.and_left _ _)
      have hyz : (fun p : X.carrier × X.carrier × X.carrier =>
          (X.rel p.1 p.2.1 ⊓ᵣ φ p.1) ⊓ᵣ (X.rel p.2.1 p.2.2 ⊓ᵣ φ p.2.1)) ⊢ₚ
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
    (fun q : E.carrier × E.carrier × A.carrier => E.rel q.1 q.2.1 ⊓ᵣ p.rel q.1 q.2.2) ⊢ₚ
      (fun q => p.rel q.2.1 q.2.2) := by
  have hEee' : (fun q : E.carrier × E.carrier × A.carrier => E.rel q.1 q.2.1 ⊓ᵣ p.rel q.1 q.2.2)
      ⊢ₚ (fun q => E.rel q.1 q.2.1) := PLe.and_left _ _
  have hpex : (fun q : E.carrier × E.carrier × A.carrier => E.rel q.1 q.2.1 ⊓ᵣ p.rel q.1 q.2.2)
      ⊢ₚ (fun q => p.rel q.1 q.2.2) := PLe.and_right _ _
  have hAxx := PLe.trans hpex
    (PLe.reindex (fun q : E.carrier × E.carrier × A.carrier => (q.1, q.2.2)) p.strict_cod)
  exact PLe.trans (PLe.and_intro (PLe.and_intro hEee' hAxx) hpex)
    (PLe.reindex (fun q : E.carrier × E.carrier × A.carrier => (q.1, q.2.1, q.2.2, q.2.2)) p.congr)

/-- The **dependent product** `Π (x:A). B x` of a display map `B = (E, p)`: the
object of **sections**, built as the subobject of the exponential `E ^ A` cut out by
"`f` is a section" (`p ∘ f = id_A`, i.e. `p (f x) = x` for every existing `x`). -/
def Family.pi {A : Obj} (B : Family A) : Obj :=
  Obj.sub (Obj.expn A B.total)
    (fun f =>
      { rel := fun h c => ∀ (x : A.carrier) (a : Code),
          (A.rel x x).rel h a → (B.proj.rel (f x) x).rel h (c ⬝ a)
        exp := fun r hc x a ha => (B.proj.rel (f x) x).exp (Code.Red.appL r) (hc x a ha) })
    (by
      obtain ⟨clg, hclg⟩ := B.proj.congr_left
      refine ⟨Code.B ⬝ (Code.B ⬝ clg) ⬝ Code.pairAp, fun fg h input hinput x a ha => ?_⟩
      obtain ⟨d, d', hired, hd, hd'⟩ := hinput
      have hred : Code.Reds ((Code.B ⬝ (Code.B ⬝ clg) ⬝ Code.pairAp ⬝ input) ⬝ a)
          (clg ⬝ (pr ⬝ (d ⬝ a) ⬝ (d' ⬝ a))) := by
        refine .trans (Code.Reds.appL (Code.B_app (Code.B ⬝ clg) Code.pairAp input) a) ?_
        refine .trans (Code.B_app clg (Code.pairAp ⬝ input) a) (Code.Reds.appR clg ?_)
        have hfst : Code.Reds (fst ⬝ input ⬝ a) (d ⬝ a) :=
          Code.Reds.appL (.trans (Code.Reds.appR fst hired) (.single Code.Red.prL)) a
        have hsnd : Code.Reds (snd ⬝ input ⬝ a) (d' ⬝ a) :=
          Code.Reds.appL (.trans (Code.Reds.appR snd hired) (.single Code.Red.prR)) a
        exact .trans (Code.pairAp_app input a)
          (.trans (Code.Reds.appL (Code.Reds.appR pr hfst) _) (Code.Reds.appR _ hsnd))
      refine (B.proj.rel (fg.2 x) x).expReds hred ?_
      exact hclg (fg.1 x, fg.2 x, x) h (pr ⬝ (d ⬝ a) ⬝ (d' ⬝ a))
        ⟨d ⬝ a, d' ⬝ a, Code.Reds.refl, hd x x a ha, hd' x a ha⟩)

end LeanStatefulAoc
