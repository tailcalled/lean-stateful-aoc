import LeanStatefulAoc.Combinators

set_option linter.style.longLine false

/-!
# Confluence (Church–Rosser) of the combinator reduction

The effectful dependent product needs `RProp` to be closed under *forward*
reduction (a realizer that reduces still realizes), so that a pure transport
realizer, applied to a produced value, **evaluates** to a value still realizing the
target. That forward-closure follows from **confluence** of `Code.Red`.

We prove confluence by Takahashi's method:
* a **parallel reduction** `Par` (reduce any set of redexes simultaneously), with
  `Red ⊆ Par ⊆ Reds`, so `Par`'s reflexive-transitive closure is `Reds`;
* the **complete development** `dev a` (reduce *all* current redexes once), with
  `Par a (dev a)`;
* the **triangle** `Par a b → Par b (dev a)`, giving the diamond for `Par`
  (`d := dev a`), hence confluence of `Reds`.

This file: `Par`, the conversions, `dev`, and `Par a (dev a)`. The triangle and
confluence are proved on top.
-/

namespace LeanStatefulAoc

open Code

/-- Parallel reduction: contract any set of redexes at once (Tait–Martin-Löf). -/
inductive Par : Code → Code → Prop
  /-- reflexivity (in particular leaves reduce to themselves) -/
  | refl (c : Code) : Par c c
  /-- congruence on application -/
  | app {f f' x x'} : Par f f' → Par x x' → Par (f ⬝ x) (f' ⬝ x')
  /-- `K x y → x` -/
  | k {x x' y y'} : Par x x' → Par y y' → Par (K ⬝ x ⬝ y) x'
  /-- `S x y z → x z (y z)` -/
  | s {x x' y y' z z'} : Par x x' → Par y y' → Par z z' →
      Par (S ⬝ x ⬝ y ⬝ z) (x' ⬝ z' ⬝ (y' ⬝ z'))
  /-- `fst (pr a b) → a` -/
  | prL {a a' b} : Par a a' → Par (fst ⬝ (pr ⬝ a ⬝ b)) a'
  /-- `snd (pr a b) → b` -/
  | prR {a b b'} : Par b b' → Par (snd ⬝ (pr ⬝ a ⬝ b)) b'
  /-- `case f g (inl a) → f a` -/
  | caseL {f f' g a a'} : Par f f' → Par a a' → Par (case ⬝ f ⬝ g ⬝ (inl ⬝ a)) (f' ⬝ a')
  /-- `case f g (inr b) → g b` -/
  | caseR {f g g' b b'} : Par g g' → Par b b' → Par (case ⬝ f ⬝ g ⬝ (inr ⬝ b)) (g' ⬝ b')

/-- One-step reduction is a parallel reduction. -/
theorem Red.toPar {a b : Code} (h : Code.Red a b) : Par a b := by
  induction h with
  | k => exact Par.k (Par.refl _) (Par.refl _)
  | s => exact Par.s (Par.refl _) (Par.refl _) (Par.refl _)
  | appL _ ih => exact Par.app ih (Par.refl _)
  | appR _ ih => exact Par.app (Par.refl _) ih
  | prL => exact Par.prL (Par.refl _)
  | prR => exact Par.prR (Par.refl _)
  | caseL => exact Par.caseL (Par.refl _) (Par.refl _)
  | caseR => exact Par.caseR (Par.refl _) (Par.refl _)

/-- Parallel reduction is contained in multi-step reduction. -/
theorem Par.toReds {a b : Code} (h : Par a b) : Code.Reds a b := by
  induction h with
  | refl c => exact Code.Reds.refl
  | app _ _ ihf ihx => exact .trans (Code.Reds.appL ihf _) (Code.Reds.appR _ ihx)
  | @k x x' y y' _ _ ihx ihy =>
    exact .trans (Code.Reds.appL (Code.Reds.appR K ihx) y)
      (.trans (Code.Reds.appR (K ⬝ x') ihy) (.single Code.Red.k))
  | @s x x' y y' z z' _ _ _ ihx ihy ihz =>
    refine .trans ?_ (.single Code.Red.s)
    exact .trans (Code.Reds.appL (Code.Reds.appL (Code.Reds.appR S ihx) y) z)
      (.trans (Code.Reds.appL (Code.Reds.appR (S ⬝ x') ihy) z) (Code.Reds.appR (S ⬝ x' ⬝ y') ihz))
  | @prL a a' b _ ih =>
    exact .trans (Code.Reds.appR fst (Code.Reds.appL (Code.Reds.appR pr ih) b)) (.single Code.Red.prL)
  | @prR a b b' _ ih =>
    exact .trans (Code.Reds.appR snd (Code.Reds.appR (pr ⬝ a) ih)) (.single Code.Red.prR)
  | @caseL f f' g a a' _ _ ihf iha =>
    exact .trans (Code.Reds.appL (Code.Reds.appL (Code.Reds.appR case ihf) g) (inl ⬝ a))
      (.trans (Code.Reds.appR (case ⬝ f' ⬝ g) (Code.Reds.appR inl iha)) (.single Code.Red.caseL))
  | @caseR f g g' b b' _ _ ihg ihb =>
    exact .trans (Code.Reds.appL (Code.Reds.appR (case ⬝ f) ihg) (inr ⬝ b))
      (.trans (Code.Reds.appR (case ⬝ f ⬝ g') (Code.Reds.appR inr ihb)) (.single Code.Red.caseR))

/-! ### Complete development -/

/-- The complete development `dev a`: contract every redex currently in `a`, once. -/
def Code.dev : Code → Code
  | app (app K x) _ => Code.dev x
  | app (app (app S x) y) z => app (app (Code.dev x) (Code.dev z)) (app (Code.dev y) (Code.dev z))
  | app fst (app (app pr a) _) => Code.dev a
  | app snd (app (app pr _) b) => Code.dev b
  | app (app (app case f) _) (app inl a) => app (Code.dev f) (Code.dev a)
  | app (app (app case _) g) (app inr b) => app (Code.dev g) (Code.dev b)
  | app f x => app (Code.dev f) (Code.dev x)
  | c => c

/-- Every term parallel-reduces to its complete development. -/
theorem Par.devSelf (a : Code) : Par a (Code.dev a) := by
  induction a using Code.dev.induct with
  | case1 x a ihx => exact Par.k ihx (Par.refl a)
  | case2 x y z ihx ihz ihy => exact Par.s ihx ihy ihz
  | case3 a a1 iha => exact Par.prL iha
  | case4 a b ihb => exact Par.prR ihb
  | case5 f a a1 ihf iha1 => exact Par.caseL ihf iha1
  | case6 a g b ihg ihb => exact Par.caseR ihg ihb
  | case7 f x h1 h2 h3 h4 h5 h6 ihf ihx => simp only [Code.dev]; exact Par.app ihf ihx
  | case8 c h1 h2 h3 h4 h5 h6 h7 => simp only [Code.dev]; exact Par.refl c

/-! ### Inversion lemmas

Constructor-headed (partial) applications only parallel-reduce within their shape;
these power the redex sub-cases of the triangle's `app` case. -/

theorem Par.K_inv {u c : Code} (h : Par (K ⬝ u) c) : ∃ u', c = K ⬝ u' ∧ Par u u' := by
  cases h with
  | refl => exact ⟨u, rfl, Par.refl u⟩
  | app hK hu => cases hK with | refl => exact ⟨_, rfl, hu⟩

theorem Par.S2_inv {u v c : Code} (h : Par (S ⬝ u ⬝ v) c) :
    ∃ u' v', c = S ⬝ u' ⬝ v' ∧ Par u u' ∧ Par v v' := by
  cases h with
  | refl => exact ⟨u, v, rfl, Par.refl u, Par.refl v⟩
  | app h1 hv =>
    cases h1 with
    | refl => exact ⟨u, _, rfl, Par.refl u, hv⟩
    | app hS hu => cases hS with | refl => exact ⟨_, _, rfl, hu, hv⟩

theorem Par.case2_inv {u v c : Code} (h : Par (case ⬝ u ⬝ v) c) :
    ∃ u' v', c = case ⬝ u' ⬝ v' ∧ Par u u' ∧ Par v v' := by
  cases h with
  | refl => exact ⟨u, v, rfl, Par.refl u, Par.refl v⟩
  | app h1 hv =>
    cases h1 with
    | refl => exact ⟨u, _, rfl, Par.refl u, hv⟩
    | app hc hu => cases hc with | refl => exact ⟨_, _, rfl, hu, hv⟩

theorem Par.pr2_inv {a b c : Code} (h : Par (pr ⬝ a ⬝ b) c) :
    ∃ a' b', c = pr ⬝ a' ⬝ b' ∧ Par a a' ∧ Par b b' := by
  cases h with
  | refl => exact ⟨a, b, rfl, Par.refl a, Par.refl b⟩
  | app h1 hb =>
    cases h1 with
    | refl => exact ⟨a, _, rfl, Par.refl a, hb⟩
    | app hp ha => cases hp with | refl => exact ⟨_, _, rfl, ha, hb⟩

theorem Par.inl_inv {a c : Code} (h : Par (inl ⬝ a) c) : ∃ a', c = inl ⬝ a' ∧ Par a a' := by
  cases h with
  | refl => exact ⟨a, rfl, Par.refl a⟩
  | app hi ha => cases hi with | refl => exact ⟨_, rfl, ha⟩

theorem Par.inr_inv {b c : Code} (h : Par (inr ⬝ b) c) : ∃ b', c = inr ⬝ b' ∧ Par b b' := by
  cases h with
  | refl => exact ⟨b, rfl, Par.refl b⟩
  | app hi hb => cases hi with | refl => exact ⟨_, rfl, hb⟩

/-! ### The triangle lemma and confluence -/

/-- **Triangle (Takahashi).** Every parallel reduct of `a` parallel-reduces to the
complete development `dev a`. The redex constructor cases are immediate from the
IHs; the `app` case cases on the shape to detect a redex, inverting `Par`. -/
theorem Par.triangle {a b : Code} (h : Par a b) : Par b (Code.dev a) := by
  induction h with
  | refl c => exact Par.devSelf c
  | @k x x' y y' _ _ ihx _ => simp only [Code.dev]; exact ihx
  | @s x x' y y' z z' _ _ _ ihx ihy ihz =>
    simp only [Code.dev]; exact Par.app (Par.app ihx ihz) (Par.app ihy ihz)
  | @prL a a' b _ iha => simp only [Code.dev]; exact iha
  | @prR a b b' _ ihb => simp only [Code.dev]; exact ihb
  | @caseL f f' g a a' _ _ ihf iha => simp only [Code.dev]; exact Par.app ihf iha
  | @caseR f g g' b b' _ _ ihg ihb => simp only [Code.dev]; exact Par.app ihg ihb
  | @app f f' x x' hf hx ihf ihx =>
    cases f
    case app g w =>
      cases g
      case K =>
        obtain ⟨w', rfl, _⟩ := Par.K_inv hf
        simp only [Code.dev] at ihf ⊢
        obtain ⟨u', heq, hP⟩ := Par.K_inv ihf
        simp only [Code.app.injEq, true_and] at heq; subst heq
        exact Par.k hP (Par.refl x')
      case app h2 c =>
        cases h2
        case S =>
          obtain ⟨c', w', rfl, _, _⟩ := Par.S2_inv hf
          simp only [Code.dev] at ihf ⊢
          obtain ⟨cc, ww, heq, hc, hw⟩ := Par.S2_inv ihf
          simp only [Code.app.injEq, true_and] at heq; obtain ⟨rfl, rfl⟩ := heq
          exact Par.s hc hw ihx
        case case =>
          cases x
          case app i a =>
            cases i
            case inl =>
              obtain ⟨c', w', rfl, _, _⟩ := Par.case2_inv hf
              obtain ⟨a', rfl, _⟩ := Par.inl_inv hx
              simp only [Code.dev] at ihf ihx ⊢
              obtain ⟨cc, ww, heq, hc, _⟩ := Par.case2_inv ihf
              simp only [Code.app.injEq, true_and] at heq; obtain ⟨rfl, rfl⟩ := heq
              obtain ⟨aa, heqa, ha⟩ := Par.inl_inv ihx
              simp only [Code.app.injEq, true_and] at heqa; subst heqa
              exact Par.caseL hc ha
            case inr =>
              obtain ⟨c', w', rfl, _, _⟩ := Par.case2_inv hf
              obtain ⟨b', rfl, _⟩ := Par.inr_inv hx
              simp only [Code.dev] at ihf ihx ⊢
              obtain ⟨cc, ww, heq, _, hw⟩ := Par.case2_inv ihf
              simp only [Code.app.injEq, true_and] at heq; obtain ⟨rfl, rfl⟩ := heq
              obtain ⟨bb, heqb, hb⟩ := Par.inr_inv ihx
              simp only [Code.app.injEq, true_and] at heqb; subst heqb
              exact Par.caseR hw hb
            all_goals exact Par.app ihf ihx
          all_goals exact Par.app ihf ihx
        all_goals exact Par.app ihf ihx
      all_goals exact Par.app ihf ihx
    case fst =>
      cases x
      case app i a =>
        cases i
        case app j b =>
          cases j
          case pr =>
            cases hf with
            | refl =>
              obtain ⟨a', b', rfl, _, _⟩ := Par.pr2_inv hx
              simp only [Code.dev] at ihx ⊢
              obtain ⟨aa, bb, heq, ha, _⟩ := Par.pr2_inv ihx
              simp only [Code.app.injEq, true_and] at heq; obtain ⟨rfl, rfl⟩ := heq
              exact Par.prL ha
          all_goals exact Par.app ihf ihx
        all_goals exact Par.app ihf ihx
      all_goals exact Par.app ihf ihx
    case snd =>
      cases x
      case app i a =>
        cases i
        case app j b =>
          cases j
          case pr =>
            cases hf with
            | refl =>
              obtain ⟨a', b', rfl, _, _⟩ := Par.pr2_inv hx
              simp only [Code.dev] at ihx ⊢
              obtain ⟨aa, bb, heq, _, hb⟩ := Par.pr2_inv ihx
              simp only [Code.app.injEq, true_and] at heq; obtain ⟨rfl, rfl⟩ := heq
              exact Par.prR hb
          all_goals exact Par.app ihf ihx
        all_goals exact Par.app ihf ihx
      all_goals exact Par.app ihf ihx
    all_goals exact Par.app ihf ihx

/-- The diamond property of parallel reduction (`d := dev a`). -/
theorem Par.diamond {a b c : Code} (hb : Par a b) (hc : Par a c) :
    ∃ d, Par b d ∧ Par c d :=
  ⟨Code.dev a, Par.triangle hb, Par.triangle hc⟩

/-- The reflexive-transitive closure of `Par` is contained in `Reds`. -/
theorem rtgPar_toReds {a b : Code} (h : Relation.ReflTransGen Par a b) : Code.Reds a b := by
  induction h with
  | refl => exact Code.Reds.refl
  | tail _ hbc ih => exact Code.Reds.trans ih hbc.toReds

/-- **Confluence (Church–Rosser).** Any two reductions from `a` can be joined. -/
theorem Code.Reds.confluent {a b c : Code} (hb : Code.Reds a b) (hc : Code.Reds a c) :
    ∃ d, Code.Reds b d ∧ Code.Reds c d := by
  have pb : Relation.ReflTransGen Par a b := hb.mono (fun _ _ => Red.toPar)
  have pc : Relation.ReflTransGen Par a c := hc.mono (fun _ _ => Red.toPar)
  obtain ⟨d, hbd, hcd⟩ := Relation.church_rosser
    (fun _ _ _ hab hac => by
      obtain ⟨d, h1, h2⟩ := Par.diamond hab hac
      exact ⟨d, Relation.ReflGen.single h1, Relation.ReflTransGen.single h2⟩) pb pc
  exact ⟨d, rtgPar_toReds hbd, rtgPar_toReds hcd⟩

/-! ### Head-shape preservation

A constructor-headed term (`pr`/`inl`/`inr`-application) reduces only within its
shape — `Red`/`Reds` never destroy the head. With confluence this gives forward
reduction-closure for the `RProp` connectives. -/

theorem Code.Red.pr_head {a b d : Code} (h : Code.Red (pr ⬝ a ⬝ b) d) :
    ∃ a' b', d = pr ⬝ a' ⬝ b' ∧ Code.Reds a a' ∧ Code.Reds b b' := by
  cases h with
  | appL h' => cases h' with
    | appL hp => nomatch hp
    | appR h'' => exact ⟨_, b, rfl, Code.Reds.single h'', Code.Reds.refl⟩
  | appR h'' => exact ⟨a, _, rfl, Code.Reds.refl, Code.Reds.single h''⟩

theorem Code.Reds.pr_head {a b d : Code} (h : Code.Reds (pr ⬝ a ⬝ b) d) :
    ∃ a' b', d = pr ⬝ a' ⬝ b' ∧ Code.Reds a a' ∧ Code.Reds b b' := by
  induction h with
  | refl => exact ⟨a, b, rfl, Code.Reds.refl, Code.Reds.refl⟩
  | @tail e d _ h2 ih =>
    obtain ⟨a', b', rfl, ha, hb⟩ := ih
    obtain ⟨a'', b'', rfl, ha', hb'⟩ := Code.Red.pr_head h2
    exact ⟨a'', b'', rfl, ha.trans ha', hb.trans hb'⟩

theorem Code.Red.inl_head {a d : Code} (h : Code.Red (inl ⬝ a) d) :
    ∃ a', d = inl ⬝ a' ∧ Code.Reds a a' := by
  cases h with
  | appL hp => nomatch hp
  | appR h'' => exact ⟨_, rfl, Code.Reds.single h''⟩

theorem Code.Reds.inl_head {a d : Code} (h : Code.Reds (inl ⬝ a) d) :
    ∃ a', d = inl ⬝ a' ∧ Code.Reds a a' := by
  induction h with
  | refl => exact ⟨a, rfl, Code.Reds.refl⟩
  | @tail e d _ h2 ih =>
    obtain ⟨a', rfl, ha⟩ := ih
    obtain ⟨a'', rfl, ha'⟩ := Code.Red.inl_head h2
    exact ⟨a'', rfl, ha.trans ha'⟩

theorem Code.Red.inr_head {b d : Code} (h : Code.Red (inr ⬝ b) d) :
    ∃ b', d = inr ⬝ b' ∧ Code.Reds b b' := by
  cases h with
  | appL hp => nomatch hp
  | appR h'' => exact ⟨_, rfl, Code.Reds.single h''⟩

theorem Code.Reds.inr_head {b d : Code} (h : Code.Reds (inr ⬝ b) d) :
    ∃ b', d = inr ⬝ b' ∧ Code.Reds b b' := by
  induction h with
  | refl => exact ⟨b, rfl, Code.Reds.refl⟩
  | @tail e d _ h2 ih =>
    obtain ⟨b', rfl, hb⟩ := ih
    obtain ⟨b'', rfl, hb'⟩ := Code.Red.inr_head h2
    exact ⟨b'', rfl, hb.trans hb'⟩

end LeanStatefulAoc
