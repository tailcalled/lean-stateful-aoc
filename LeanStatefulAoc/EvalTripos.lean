import LeanStatefulAoc.Memo
import LeanStatefulAoc.EvalHMono

set_option linter.style.longLine false

/-!
# The realizability tripos over the stateful PCA `(Code, eval)`

The pure term model `(Code, ·)` (syntactic application, `Reds`-equality) is a perfectly
good combinatory algebra, but its realizability **does not validate `AC_dec`**: the
memoizer `memo·(loc ℓ)` never `Reds`-reduces to a witness, so it is not a realizer there.
The PCA whose realizability *does* validate `AC_dec` is the **stateful** one, where
application is the effectful evaluator: `a · b := eval (a ⬝ b)` (partial, heap-threading).

Over this PCA every entailment and morphism uses `Produces` uniformly — there is no
"pure vs effectful" split and no strong-normalisation side condition: the termination of a
transport `r · v` is *part of* "`r` realises the entailment", i.e. a `Produces` statement,
not an external obligation. Composition of these `Produces`-entailments is exactly the
state monad's bind (`seq` + `Produces.bind`).

This file builds the foundation: the `Evaluates`-level **simulation primitives** for the
plumbing combinators (so realizers built from `S`/`K`/`B`/`C` behave under `eval`), then the
proposition type `EProp` (heap-indexed realizers, closed under evaluation) and the
entailment preorder `EEntails`.
-/

namespace LeanStatefulAoc

open Code

/-! ## `applyV` fuel monotonicity (companion to `eval_mono`) -/

theorem applyV_mono {n : Nat} {h : CHeap} {fv x : Code} {r : CHeap × Code}
    (hx : applyV n h fv x = some r) : applyV (n + 1) h fv x = some r :=
  applyV_mono_of_eval_mono n (fun h e r he => eval_mono n h e r he) h fv x r hx

theorem applyV_mono_le {n m : Nat} (hnm : n ≤ m) {h : CHeap} {fv x : Code} {r : CHeap × Code}
    (hx : applyV n h fv x = some r) : applyV m h fv x = some r := by
  induction hnm with
  | refl => exact hx
  | step _ ih => exact applyV_mono ih

/-! ## `Evaluates` introduction / inversion for application

`eval` of an application evaluates the head to a value, then `applyV`s the argument. These
two lemmas package that step in fuel-robust (`∃`-fuel) form, the workhorses for every
combinator simulation below. -/

/-- Build an application evaluation from a head evaluation and an `applyV`. -/
theorem Evaluates.mk_app {h h2 h' : CHeap} {f x fv v : Code}
    (hf : Evaluates h f h2 fv) (happ : ∃ m, applyV m h2 fv x = some (h', v)) :
    Evaluates h (f ⬝ x) h' v := by
  obtain ⟨nf, hnf⟩ := hf
  obtain ⟨ma, hma⟩ := happ
  refine ⟨max nf ma + 1, ?_⟩
  have e1 : eval (max nf ma) h f = some (h2, fv) := eval_mono_le (Nat.le_max_left nf ma) hnf
  have e2 : applyV (max nf ma) h2 fv x = some (h', v) := applyV_mono_le (Nat.le_max_right nf ma) hma
  simp only [eval, e1, e2]

/-- Invert an application evaluation into a head evaluation and an `applyV`. -/
theorem Evaluates.app_inv {h h' : CHeap} {f x v : Code} (he : Evaluates h (f ⬝ x) h' v) :
    ∃ h2 fv, Evaluates h f h2 fv ∧ ∃ m, applyV m h2 fv x = some (h', v) := by
  obtain ⟨n, hn⟩ := he
  cases n with
  | zero => simp [eval] at hn
  | succ n =>
    simp only [eval] at hn
    cases hf : eval n h f with
    | none => rw [hf] at hn; simp at hn
    | some p =>
      obtain ⟨h2, fv⟩ := p
      rw [hf] at hn
      exact ⟨h2, fv, ⟨n, hf⟩, ⟨n, hn⟩⟩

/-! ## Value lemmas: stuck applications evaluate to themselves -/

theorem Evaluates.K1 {h : CHeap} {x : Code} : Evaluates h (K ⬝ x) h (K ⬝ x) :=
  ⟨2, by simp only [eval, applyV]⟩

theorem Evaluates.S1 {h : CHeap} {x : Code} : Evaluates h (S ⬝ x) h (S ⬝ x) :=
  ⟨2, by simp only [eval, applyV]⟩

theorem Evaluates.S2 {h : CHeap} {x y : Code} : Evaluates h (S ⬝ x ⬝ y) h (S ⬝ x ⬝ y) :=
  ⟨3, by simp only [eval, applyV]⟩

/-! ## Head-redex simulations -/

/-- `K · x · y` runs like `x`. -/
theorem Evaluates.headK {h h' : CHeap} {x y v : Code} (hx : Evaluates h x h' v) :
    Evaluates h (K ⬝ x ⬝ y) h' v := by
  obtain ⟨nx, hnx⟩ := hx
  exact Evaluates.mk_app Evaluates.K1 ⟨nx, by simp only [applyV]; exact hnx⟩

/-- `S · a · b · c` runs like `a · c · (b · c)`. -/
theorem Evaluates.headS {h h' : CHeap} {a b c v : Code} (hr : Evaluates h (a ⬝ c ⬝ (b ⬝ c)) h' v) :
    Evaluates h (S ⬝ a ⬝ b ⬝ c) h' v := by
  obtain ⟨n, hn⟩ := hr
  exact Evaluates.mk_app Evaluates.S2 ⟨n, by simp only [applyV]; exact hn⟩

/-- `I · a` runs like `a` (`I = S K K`). -/
theorem Evaluates.I {h h' : CHeap} {a v : Code} (ha : Evaluates h a h' v) :
    Evaluates h (I ⬝ a) h' v := by
  simpa only [Code.I] using Evaluates.headS (Evaluates.headK ha)

theorem Evaluates.Sval {h : CHeap} : Evaluates h S h S := ⟨1, by simp only [eval]⟩

theorem Evaluates.Kval {h : CHeap} : Evaluates h K h K := ⟨1, by simp only [eval]⟩

theorem Evaluates.Bval {h : CHeap} : Evaluates h B h B := ⟨3, by simp only [Code.B, eval, applyV]⟩

theorem Evaluates.prv {h : CHeap} : Evaluates h pr h pr := ⟨1, by simp only [eval]⟩

/-- `B · z` runs like `S · (K · z)` (`B z ↠ S (K z)`, a value). -/
theorem Evaluates.B1 {h : CHeap} {z : Code} : Evaluates h (B ⬝ z) h (S ⬝ (K ⬝ z)) := by
  simp only [Code.B]
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.Sval) ⟨1, by simp only [applyV]⟩)

/-- `B · f · g · x` runs like `f · (g · x)` (`B = S (K S) K`); kept for the Heyting layer. -/
theorem Evaluates.Bsim {h h' : CHeap} {f g x v : Code} (hr : Evaluates h (f ⬝ (g ⬝ x)) h' v) :
    Evaluates h (B ⬝ f ⬝ g ⬝ x) h' v := by
  have hBf : Evaluates h (B ⬝ f) h (S ⬝ (K ⬝ f)) := by
    simp only [Code.B]
    exact Evaluates.headS
      (Evaluates.mk_app (Evaluates.headK Evaluates.Sval) ⟨1, by simp only [applyV]⟩)
  have hBfg : Evaluates h (B ⬝ f ⬝ g) h (S ⬝ (K ⬝ f) ⬝ g) :=
    Evaluates.mk_app hBf ⟨1, by simp only [applyV]⟩
  obtain ⟨h2, fv, hfh2, m, happ⟩ := Evaluates.app_inv hr
  obtain ⟨n, hn⟩ : Evaluates h ((K ⬝ f ⬝ x) ⬝ (g ⬝ x)) h' v :=
    Evaluates.mk_app (Evaluates.headK hfh2) ⟨m, happ⟩
  exact Evaluates.mk_app hBfg ⟨n, by simp only [applyV]; exact hn⟩

/-- `eval` is deterministic: raise both runs to a common fuel via monotonicity. -/
theorem Evaluates.deterministic {h h1 h2 : CHeap} {e v1 v2 : Code}
    (h_1 : Evaluates h e h1 v1) (h_2 : Evaluates h e h2 v2) : h1 = h2 ∧ v1 = v2 := by
  obtain ⟨n1, e1⟩ := h_1
  obtain ⟨n2, e2⟩ := h_2
  have e1' : eval (max n1 n2) h e = some (h1, v1) := eval_mono_le (Nat.le_max_left n1 n2) e1
  have e2' : eval (max n1 n2) h e = some (h2, v2) := eval_mono_le (Nat.le_max_right n1 n2) e2
  rw [e1'] at e2'; simp only [Option.some.injEq, Prod.mk.injEq] at e2'; exact e2'

theorem Evaluates.seqVal {h : CHeap} {e : Code} : Evaluates h (seq ⬝ e) h (seq ⬝ e) :=
  ⟨2, by simp only [eval, applyV]⟩

theorem Evaluates.seqv {h : CHeap} : Evaluates h seq h seq := ⟨1, by simp only [eval]⟩

/-- **Head swap**: if `g` and `g'` evaluate to the same value `V` (same heap), then they are
interchangeable as the function of an application. The workhorse for transporting realizers
whose head is a redex (which `eval` reduces) to/from its value form. -/
theorem Evaluates.appHeadSwap {h hV hh : CHeap} {g g' k V w : Code}
    (hg : Evaluates h g hV V) (hg' : Evaluates h g' hV V) (hgk : Evaluates h (g' ⬝ k) hh w) :
    Evaluates h (g ⬝ k) hh w := by
  obtain ⟨hZ, fvZ, hhead, mZ, hap⟩ := Evaluates.app_inv hgk
  obtain ⟨rfl, rfl⟩ := Evaluates.deterministic hhead hg'
  exact Evaluates.mk_app hg ⟨mZ, hap⟩

/-- Transport for the `trans`/pairing composition realizer: `S (S (K seq) r₁) kc` applied to
`a` runs like `seq · (r₁ · a) · (kc · a)`. -/
theorem Evaluates.headSeqK {h h'' : CHeap} {r₁ kc a w : Code}
    (hseq : Evaluates h (seq ⬝ (r₁ ⬝ a) ⬝ (kc ⬝ a)) h'' w) :
    Evaluates h (S ⬝ (S ⬝ (K ⬝ seq) ⬝ r₁) ⬝ kc ⬝ a) h'' w := by
  obtain ⟨hX, fvX, hseqhead, mX, hap⟩ := Evaluates.app_inv hseq
  obtain ⟨heq, feq⟩ := Evaluates.deterministic hseqhead Evaluates.seqVal
  rw [heq, feq] at hap
  have hHead : Evaluates h (S ⬝ (K ⬝ seq) ⬝ r₁ ⬝ a) h (seq ⬝ (r₁ ⬝ a)) :=
    Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.seqv) ⟨1, by simp only [applyV]⟩)
  exact Evaluates.headS (Evaluates.mk_app hHead ⟨mX, hap⟩)

/-! ## Propositions over the stateful PCA -/

/-- A proposition of the stateful realizability tripos: a heap-indexed set of realizers,
**closed under evaluation** (`ev`: a realizer evaluates to a realizer). The `ev` field is
exactly what makes `(Code, eval)` — not the pure term model — the ambient PCA: applying a
realizer genuinely *produces* a realizer, so transport termination is internal, never an
external normalisation obligation. -/
structure EProp where
  rel : CHeap → Code → Prop
  ev : ∀ {h e}, rel h e → ∃ h' v, Evaluates h e h' v ∧ rel h' v
  /-- Kripke monotonicity: realizers persist as the (monotone) heap grows. This is what
  lets a realizer of `X` survive an earlier sub-computation's effects, e.g. in `and_intro`. -/
  mono : ∀ {h h' e}, HLe h h' → rel h e → rel h' e

/-- `P` is *produced* at `h` by `e` if `e` evaluates to a realizer of `P`. This is
application in the stateful PCA. -/
def EProp.Produces (P : EProp) (h : CHeap) (e : Code) : Prop :=
  ∃ h' v, Evaluates h e h' v ∧ P.rel h' v

/-- **Monadic bind for `Produces`**: `seq` composes producers. -/
theorem EProp.Produces.bind {h : CHeap} {e k : Code} {Q R : EProp}
    (hQ : Q.Produces h e) (hk : ∀ h' v, Q.rel h' v → R.Produces h' (k ⬝ v)) :
    R.Produces h (seq ⬝ e ⬝ k) := by
  obtain ⟨h', v, ⟨n0, hev0⟩, hqv⟩ := hQ
  obtain ⟨h'', w, ⟨m0, hevm⟩, hrw⟩ := hk h' v hqv
  refine ⟨h'', w, ⟨max n0 m0 + 3, ?_⟩, hrw⟩
  rw [eval_seq_some (max n0 m0) h h' e k v
        (eval_mono_le (Nat.le_trans (Nat.le_max_left n0 m0) (by omega)) hev0)]
  exact eval_mono_le (Nat.le_trans (Nat.le_max_right n0 m0) (by omega)) hevm

/-- **Bind with reachability**: the continuation may assume it runs at a heap `h'` that
*extends* `h` (the run of `e` only grows the heap, `Evaluates.hle`). This is what lets a
Kripke-monotone realizer of some `X` survive into the continuation — the crux of effectful
pairing (`and_intro`). -/
theorem EProp.Produces.bindH {h : CHeap} {e k : Code} {Q R : EProp}
    (hQ : Q.Produces h e) (hk : ∀ h' v, HLe h h' → Q.rel h' v → R.Produces h' (k ⬝ v)) :
    R.Produces h (seq ⬝ e ⬝ k) := by
  obtain ⟨h', v, hev0, hqv⟩ := hQ
  obtain ⟨h'', w, hevm, hrw⟩ := hk h' v hev0.hle hqv
  obtain ⟨n0, e0⟩ := hev0
  obtain ⟨m0, em⟩ := hevm
  refine ⟨h'', w, ⟨max n0 m0 + 3, ?_⟩, hrw⟩
  rw [eval_seq_some (max n0 m0) h h' e k v
        (eval_mono_le (Nat.le_trans (Nat.le_max_left n0 m0) (by omega)) e0)]
  exact eval_mono_le (Nat.le_trans (Nat.le_max_right n0 m0) (by omega)) em

/-- Transport a producer along a head whose evaluation is dominated by another: if whenever
`g'` evaluates to a value `g` does too, then `g' ⬝ k` producing gives `g ⬝ k` producing. The
clean way to swap a redex head for the value/term it reduces to inside a `Produces`. -/
theorem EProp.Produces.headEq {h : CHeap} {g g' k : Code} {Q : EProp}
    (hgg' : ∀ hh v, Evaluates h g' hh v → Evaluates h g hh v) (hP : Q.Produces h (g' ⬝ k)) :
    Q.Produces h (g ⬝ k) := by
  obtain ⟨h'', w, hev, hw⟩ := hP
  obtain ⟨hZ, fvZ, hhead, mZ, hap⟩ := Evaluates.app_inv hev
  exact ⟨h'', w, Evaluates.mk_app (hgg' hZ fvZ hhead) ⟨mZ, hap⟩, hw⟩

/-! ## Entailment: the tripos order over `(Code, eval)` -/

/-- `P ⊨ Q`: a single realizer `r`, uniform over heaps and carrier realizers, that — applied
to any `P`-realizer — *produces* a `Q`-realizer. Application is `eval`; composition is the
state monad. -/
def EEntails (P Q : EProp) : Prop := ∃ r, ∀ h a, P.rel h a → Q.Produces h (r ⬝ a)

@[inherit_doc] infix:50 " ⊨ " => EEntails

/-- Reflexivity: `I` realises `P ⊨ P` (it produces `a`'s value, still a realizer by `ev`). -/
theorem EEntails.refl (P : EProp) : P ⊨ P :=
  ⟨I, fun _ _ ha => by
    obtain ⟨h', v, hev, hrel⟩ := P.ev ha
    exact ⟨h', v, Evaluates.I hev, hrel⟩⟩

/-- The realizer of entailment composition: `S (S (K seq) r₁) (K r₂)`. -/
def Code.compR (r₂ r₁ : Code) : Code := S ⬝ (S ⬝ (K ⬝ seq) ⬝ r₁) ⬝ (K ⬝ r₂)

/-- **Composition, realizer-explicit core.** `compR r₂ r₁ · a ↠ seq · (r₁·a) · (K·r₂·a)`,
running `r₁` on `a` then `r₂` on the result — exactly `Produces.bind`. Reused by
`EEntails.trans` and `PLe.trans`. -/
theorem EProp.compProduces {P Q R : EProp} {r₁ r₂ : Code}
    (h₁ : ∀ h a, P.rel h a → Q.Produces h (r₁ ⬝ a))
    (h₂ : ∀ h a, Q.rel h a → R.Produces h (r₂ ⬝ a))
    (h : CHeap) (a : Code) (hPa : P.rel h a) :
    R.Produces h (Code.compR r₂ r₁ ⬝ a) := by
  rw [Code.compR]
  have hbind : R.Produces h (seq ⬝ (r₁ ⬝ a) ⬝ (K ⬝ r₂ ⬝ a)) := by
    refine EProp.Produces.bind (h₁ h a hPa) (fun h' v hqv => ?_)
    -- continuation (K · r₂ · a) · v  ↠  r₂ · v
    obtain ⟨h2, fv, hr2, hRfv⟩ := h₂ h' v hqv
    obtain ⟨hr', rv, hr2head, m, happ⟩ := Evaluates.app_inv hr2
    exact ⟨h2, fv, Evaluates.mk_app (Evaluates.headK hr2head) ⟨m, happ⟩, hRfv⟩
  obtain ⟨h', v, hevseq, hRv⟩ := hbind
  exact ⟨h', v, Evaluates.headSeqK hevseq, hRv⟩

/-- **Kripke composition.** Like `compProduces`, but the second tracker may assume it runs at
a heap extending `h` (carries the `HLe`). -/
theorem EProp.compProducesH {P Q R : EProp} {r₁ r₂ : Code} (h : CHeap) {a : Code}
    (h₁ : P.rel h a → Q.Produces h (r₁ ⬝ a))
    (h₂ : ∀ h' v, HLe h h' → Q.rel h' v → R.Produces h' (r₂ ⬝ v))
    (hPa : P.rel h a) :
    R.Produces h (Code.compR r₂ r₁ ⬝ a) := by
  rw [Code.compR]
  have hbind : R.Produces h (seq ⬝ (r₁ ⬝ a) ⬝ (K ⬝ r₂ ⬝ a)) := by
    refine EProp.Produces.bindH (h₁ hPa) (fun h' v hle hqv => ?_)
    obtain ⟨h2, fv, hr2, hRfv⟩ := h₂ h' v hle hqv
    obtain ⟨hr', rv, hr2head, m, happ⟩ := Evaluates.app_inv hr2
    exact ⟨h2, fv, Evaluates.mk_app (Evaluates.headK hr2head) ⟨m, happ⟩, hRfv⟩
  obtain ⟨h', v, hevseq, hRv⟩ := hbind
  exact ⟨h', v, Evaluates.headSeqK hevseq, hRv⟩

/-- Transitivity of entailment. -/
theorem EEntails.trans {P Q R : EProp} (hPQ : P ⊨ Q) (hQR : Q ⊨ R) : P ⊨ R := by
  obtain ⟨r₁, h₁⟩ := hPQ
  obtain ⟨r₂, h₂⟩ := hQR
  exact ⟨Code.compR r₂ r₁, fun h a ha => EProp.compProduces h₁ h₂ h a ha⟩

/-! ## β-reductions for the data constructors (`pr`/`fst`/`snd`/`inl`/`inr`/`case`) -/

theorem Evaluates.prVal {h : CHeap} {a b : Code} : Evaluates h (pr ⬝ a ⬝ b) h (pr ⬝ a ⬝ b) :=
  ⟨3, by simp only [eval, applyV]⟩

theorem Evaluates.inlVal {h : CHeap} {a : Code} : Evaluates h (inl ⬝ a) h (inl ⬝ a) :=
  ⟨2, by simp only [eval, applyV]⟩

theorem Evaluates.inrVal {h : CHeap} {b : Code} : Evaluates h (inr ⬝ b) h (inr ⬝ b) :=
  ⟨2, by simp only [eval, applyV]⟩

theorem Evaluates.fstβ {h : CHeap} {a b : Code} : Evaluates h (fst ⬝ (pr ⬝ a ⬝ b)) h a :=
  ⟨4, by simp only [eval, applyV]⟩

theorem Evaluates.sndβ {h : CHeap} {a b : Code} : Evaluates h (snd ⬝ (pr ⬝ a ⬝ b)) h b :=
  ⟨4, by simp only [eval, applyV]⟩

/-- `case · f · g · (inl · a)` runs like `f · a`. -/
theorem Evaluates.caseLβ {h h' : CHeap} {f g a v : Code} (hf : Evaluates h (f ⬝ a) h' v) :
    Evaluates h (case ⬝ f ⬝ g ⬝ (inl ⬝ a)) h' v := by
  obtain ⟨n, hn⟩ := hf
  have hinl : eval (max n 2) h (inl ⬝ a) = some (h, inl ⬝ a) :=
    eval_mono_le (Nat.le_max_right n 2) (by simp only [eval, applyV])
  refine Evaluates.mk_app (h2 := h) (fv := case ⬝ f ⬝ g) ⟨3, by simp only [eval, applyV]⟩
    ⟨max n 2, ?_⟩
  simp only [applyV, hinl]
  exact eval_mono_le (Nat.le_max_left n 2) hn

/-- `case · f · g · (inr · b)` runs like `g · b`. -/
theorem Evaluates.caseRβ {h h' : CHeap} {f g b v : Code} (hg : Evaluates h (g ⬝ b) h' v) :
    Evaluates h (case ⬝ f ⬝ g ⬝ (inr ⬝ b)) h' v := by
  obtain ⟨n, hn⟩ := hg
  have hinr : eval (max n 2) h (inr ⬝ b) = some (h, inr ⬝ b) :=
    eval_mono_le (Nat.le_max_right n 2) (by simp only [eval, applyV])
  refine Evaluates.mk_app (h2 := h) (fv := case ⬝ f ⬝ g) ⟨3, by simp only [eval, applyV]⟩
    ⟨max n 2, ?_⟩
  simp only [applyV, hinr]
  exact eval_mono_le (Nat.le_max_left n 2) hn

/-- `case · f · g · x` runs like `f · w` when the scrutinee `x` *evaluates* to `inl · w`. -/
theorem Evaluates.caseLβ' {h h₁ h' : CHeap} {f g x w v : Code}
    (hx : Evaluates h x h₁ (inl ⬝ w)) (hf : Evaluates h₁ (f ⬝ w) h' v) :
    Evaluates h (case ⬝ f ⬝ g ⬝ x) h' v := by
  obtain ⟨nx, hnx⟩ := hx
  obtain ⟨nf, hnf⟩ := hf
  refine Evaluates.mk_app (h2 := h) (fv := case ⬝ f ⬝ g) ⟨3, by simp only [eval, applyV]⟩
    ⟨max nx nf, ?_⟩
  simp only [applyV, eval_mono_le (Nat.le_max_left nx nf) hnx]
  exact eval_mono_le (Nat.le_max_right nx nf) hnf

/-- `case · f · g · x` runs like `g · w` when the scrutinee `x` *evaluates* to `inr · w`. -/
theorem Evaluates.caseRβ' {h h₁ h' : CHeap} {f g x w v : Code}
    (hx : Evaluates h x h₁ (inr ⬝ w)) (hg : Evaluates h₁ (g ⬝ w) h' v) :
    Evaluates h (case ⬝ f ⬝ g ⬝ x) h' v := by
  obtain ⟨nx, hnx⟩ := hx
  obtain ⟨ng, hng⟩ := hg
  refine Evaluates.mk_app (h2 := h) (fv := case ⬝ f ⬝ g) ⟨3, by simp only [eval, applyV]⟩
    ⟨max nx ng, ?_⟩
  simp only [applyV, eval_mono_le (Nat.le_max_left nx ng) hnx]
  exact eval_mono_le (Nat.le_max_right nx ng) hng

/-! ## Heyting connectives at the `Produces` level

Realizers are *values* of the expected shape (`tt`, `pr·a·b`, `inl·a`/`inr·b`), so the
`ev` field is discharged by the value lemmas above; the entailment realizers are the data
combinators `fst`/`snd`/`case`, whose β-rules were just proved. -/

/-- Truth: realized by `tt`. -/
def EProp.top : EProp where
  rel _ e := e = tt
  ev := by rintro h e rfl; exact ⟨h, tt, ⟨1, by simp only [eval]⟩, rfl⟩
  mono := by rintro h h' e _ rfl; rfl

/-- Falsity: no realizers. -/
def EProp.bot : EProp where
  rel _ _ := False
  ev := by rintro h e ⟨⟩
  mono := by rintro h h' e _ ⟨⟩

/-- Conjunction: realized by a pair `pr · a · b` of realizers. -/
def EProp.and (P Q : EProp) : EProp where
  rel h e := ∃ a b, e = pr ⬝ a ⬝ b ∧ P.rel h a ∧ Q.rel h b
  ev := by
    rintro h e ⟨a, b, rfl, ha, hb⟩
    exact ⟨h, pr ⬝ a ⬝ b, Evaluates.prVal, a, b, rfl, ha, hb⟩
  mono := by
    rintro h h' e hle ⟨a, b, rfl, ha, hb⟩
    exact ⟨a, b, rfl, P.mono hle ha, Q.mono hle hb⟩

@[inherit_doc] infixl:70 " ⊓ₑ " => EProp.and

/-- Existential / propositional truncation: realized by a realizer of *some* fiber (the
realizer is preserved — truncation is a quotient, not an erasure). -/
def EProp.ex (I : Type) (φ : I → EProp) : EProp where
  rel h e := ∃ i, (φ i).rel h e
  ev := by
    rintro h e ⟨i, hi⟩
    obtain ⟨h', v, hev, hv⟩ := (φ i).ev hi
    exact ⟨h', v, hev, i, hv⟩
  mono := by rintro h h' e hle ⟨i, hi⟩; exact ⟨i, (φ i).mono hle hi⟩

/-! ### Entailment laws -/

theorem EProp.le_top (P : EProp) : P ⊨ EProp.top :=
  ⟨K ⬝ tt, fun h a _ => ⟨h, tt, Evaluates.headK ⟨1, by simp only [eval]⟩, rfl⟩⟩

theorem EProp.bot_le (P : EProp) : EProp.bot ⊨ P :=
  ⟨I, fun _ _ h => h.elim⟩

theorem EProp.and_left {P Q : EProp} : P ⊓ₑ Q ⊨ P :=
  ⟨fst, by rintro h a ⟨x, y, rfl, hx, _⟩; exact ⟨h, x, Evaluates.fstβ, hx⟩⟩

theorem EProp.and_right {P Q : EProp} : P ⊓ₑ Q ⊨ Q :=
  ⟨snd, by rintro h a ⟨x, y, rfl, _, hy⟩; exact ⟨h, y, Evaluates.sndβ, hy⟩⟩

theorem EProp.ex_intro {Idx : Type} {φ : Idx → EProp} (i : Idx) : φ i ⊨ EProp.ex Idx φ :=
  ⟨Code.I, fun h a ha => by
    obtain ⟨h', v, hev, hv⟩ := (φ i).ev ha
    exact ⟨h', v, Evaluates.I hev, i, hv⟩⟩

/-- The elimination rule: a *uniform* realizer `r` for every fiber lifts to the truncation. -/
theorem EProp.ex_elim {Idx : Type} {φ : Idx → EProp} {ψ : EProp} {r : Code}
    (hr : ∀ i h a, (φ i).rel h a → ψ.Produces h (r ⬝ a)) : EProp.ex Idx φ ⊨ ψ :=
  ⟨r, fun h a ⟨i, hi⟩ => hr i h a hi⟩

theorem EProp.ex_mono {Idx : Type} {φ ψ : Idx → EProp} {r : Code}
    (hr : ∀ i h a, (φ i).rel h a → (ψ i).Produces h (r ⬝ a)) :
    EProp.ex Idx φ ⊨ EProp.ex Idx ψ := by
  refine ⟨r, ?_⟩
  rintro h a ⟨i, hi⟩
  obtain ⟨h', v, hev, hv⟩ := hr i h a hi
  exact ⟨h', v, hev, i, hv⟩

/-- Disjunction / binary coproduct: realized by a tagged value `inl · a` or `inr · b`.
This is the truth-value side of the decidable-equality premise of `AC_dec`. -/
def EProp.or (P Q : EProp) : EProp where
  rel h e := (∃ a, e = inl ⬝ a ∧ P.rel h a) ∨ (∃ b, e = inr ⬝ b ∧ Q.rel h b)
  ev := by
    rintro h e (⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩)
    · exact ⟨h, inl ⬝ a, Evaluates.inlVal, Or.inl ⟨a, rfl, ha⟩⟩
    · exact ⟨h, inr ⬝ b, Evaluates.inrVal, Or.inr ⟨b, rfl, hb⟩⟩
  mono := by
    rintro h h' e hle (⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩)
    · exact Or.inl ⟨a, rfl, P.mono hle ha⟩
    · exact Or.inr ⟨b, rfl, Q.mono hle hb⟩

@[inherit_doc] infixl:65 " ⊔ₑ " => EProp.or

theorem EProp.or_inl {P Q : EProp} : P ⊨ P ⊔ₑ Q :=
  ⟨inl, fun h a ha => ⟨h, inl ⬝ a, Evaluates.inlVal, Or.inl ⟨a, rfl, ha⟩⟩⟩

theorem EProp.or_inr {P Q : EProp} : Q ⊨ P ⊔ₑ Q :=
  ⟨inr, fun h a ha => ⟨h, inr ⬝ a, Evaluates.inrVal, Or.inr ⟨a, rfl, ha⟩⟩⟩

/-- The realizer of effectful pairing: `S (S (K seq) r₁) (S (S (K B) (B seq r₂)) (K pr))`. -/
def Code.pairR (r₁ r₂ : Code) : Code :=
  S ⬝ (S ⬝ (K ⬝ seq) ⬝ r₁) ⬝ (S ⬝ (S ⬝ (K ⬝ B) ⬝ (B ⬝ seq ⬝ r₂)) ⬝ (K ⬝ pr))

/-- **Effectful pairing, realizer-explicit core.** Given trackers `r₁`, `r₂` for `P`, `Q`
over a monotone `X`, `pairR r₁ r₂` produces a `P ⊓ Q`-pair: it runs `r₁` then — on the
*grown* heap, where the Kripke-monotone `X`-realizer `a` still holds — runs `r₂`, and pairs
the two produced values with `pr`. Both `and_intro` and the topos's pairing reuse this. -/
theorem EProp.pairProduces {X P Q : EProp} {r₁ r₂ : Code}
    (h₁ : ∀ h a, X.rel h a → P.Produces h (r₁ ⬝ a))
    (h₂ : ∀ h a, X.rel h a → Q.Produces h (r₂ ⬝ a))
    (h : CHeap) (a : Code) (hXa : X.rel h a) :
    (P ⊓ₑ Q).Produces h (Code.pairR r₁ r₂ ⬝ a) := by
  rw [Code.pairR]
  -- produce P⊓Q from the literal seq form, then transport to the realizer via headSeqK
  have key : (P ⊓ₑ Q).Produces h
      (seq ⬝ (r₁ ⬝ a) ⬝ (S ⬝ (S ⬝ (K ⬝ B) ⬝ (B ⬝ seq ⬝ r₂)) ⬝ (K ⬝ pr) ⬝ a)) := by
    refine EProp.Produces.bindH (h₁ h a hXa) (fun h' vp hle hPvp => ?_)
    have hXa' := X.mono hle hXa
    -- KC ⬝ a  ↠  S (K t1) t2   where t1 = (B seq r₂) a, t2 = K pr a   (a value)
    have hKCa : Evaluates h' (S ⬝ (S ⬝ (K ⬝ B) ⬝ (B ⬝ seq ⬝ r₂)) ⬝ (K ⬝ pr) ⬝ a) h'
        (S ⬝ (K ⬝ (B ⬝ seq ⬝ r₂ ⬝ a)) ⬝ (K ⬝ pr ⬝ a)) := by
      apply Evaluates.headS
      refine Evaluates.mk_app (h2 := h') (fv := S ⬝ (K ⬝ (B ⬝ seq ⬝ r₂ ⬝ a))) ?_ ⟨1, by simp only [applyV]⟩
      apply Evaluates.headS
      exact Evaluates.appHeadSwap (Evaluates.headK Evaluates.Bval) Evaluates.Bval Evaluates.B1
    -- inner: produce P⊓Q from  seq (r₂ a) (K pr a vp)
    have hinner : (P ⊓ₑ Q).Produces h' (seq ⬝ (r₂ ⬝ a) ⬝ (K ⬝ pr ⬝ a ⬝ vp)) := by
      refine EProp.Produces.bindH (h₂ h' a hXa') (fun h'' vq hle2 hQvq => ?_)
      refine ⟨h'', pr ⬝ vp ⬝ vq, ?_, vp, vq, rfl, P.mono hle2 hPvp, hQvq⟩
      -- (K pr a vp) ⬝ vq  ↠  pr vp vq
      have e1 : Evaluates h'' (K ⬝ pr ⬝ a ⬝ vp) h'' (pr ⬝ vp) :=
        Evaluates.appHeadSwap (Evaluates.headK Evaluates.prv) Evaluates.prv
          ⟨2, by simp only [eval, applyV]⟩
      exact Evaluates.mk_app e1 ⟨1, by simp only [applyV]⟩
    -- transport  (KC a) ⬝ vp  ←  seq (r₂ a) (K pr a vp)
    obtain ⟨hh, w, hev, hw⟩ := hinner
    refine ⟨hh, w, ?_, hw⟩
    refine Evaluates.appHeadSwap hKCa Evaluates.S2 ?_
    apply Evaluates.headS
    exact Evaluates.appHeadSwap (Evaluates.headK (Evaluates.Bsim Evaluates.seqVal))
      Evaluates.seqVal hev
  obtain ⟨hh, w, hev, hw⟩ := key
  exact ⟨hh, w, Evaluates.headSeqK hev, hw⟩

/-- **Kripke pairing.** Like `pairProduces`, but the second tracker may assume it runs at a
heap extending `h` (carries the `HLe`) — needed when the trackers are themselves Kripke
(future-heap-quantified), as for the exponential. -/
theorem EProp.pairProducesH {X P Q : EProp} {r₁ r₂ : Code} (h : CHeap) {a : Code}
    (h₁ : X.rel h a → P.Produces h (r₁ ⬝ a))
    (h₂ : ∀ h', HLe h h' → X.rel h' a → Q.Produces h' (r₂ ⬝ a))
    (hXa : X.rel h a) :
    (P ⊓ₑ Q).Produces h (Code.pairR r₁ r₂ ⬝ a) := by
  rw [Code.pairR]
  have key : (P ⊓ₑ Q).Produces h
      (seq ⬝ (r₁ ⬝ a) ⬝ (S ⬝ (S ⬝ (K ⬝ B) ⬝ (B ⬝ seq ⬝ r₂)) ⬝ (K ⬝ pr) ⬝ a)) := by
    refine EProp.Produces.bindH (h₁ hXa) (fun h' vp hle hPvp => ?_)
    have hXa' := X.mono hle hXa
    have hKCa : Evaluates h' (S ⬝ (S ⬝ (K ⬝ B) ⬝ (B ⬝ seq ⬝ r₂)) ⬝ (K ⬝ pr) ⬝ a) h'
        (S ⬝ (K ⬝ (B ⬝ seq ⬝ r₂ ⬝ a)) ⬝ (K ⬝ pr ⬝ a)) := by
      apply Evaluates.headS
      refine Evaluates.mk_app (h2 := h') (fv := S ⬝ (K ⬝ (B ⬝ seq ⬝ r₂ ⬝ a))) ?_ ⟨1, by simp only [applyV]⟩
      apply Evaluates.headS
      exact Evaluates.appHeadSwap (Evaluates.headK Evaluates.Bval) Evaluates.Bval Evaluates.B1
    have hinner : (P ⊓ₑ Q).Produces h' (seq ⬝ (r₂ ⬝ a) ⬝ (K ⬝ pr ⬝ a ⬝ vp)) := by
      refine EProp.Produces.bindH (h₂ h' hle hXa') (fun h'' vq hle2 hQvq => ?_)
      refine ⟨h'', pr ⬝ vp ⬝ vq, ?_, vp, vq, rfl, P.mono hle2 hPvp, hQvq⟩
      have e1 : Evaluates h'' (K ⬝ pr ⬝ a ⬝ vp) h'' (pr ⬝ vp) :=
        Evaluates.appHeadSwap (Evaluates.headK Evaluates.prv) Evaluates.prv ⟨2, by simp only [eval, applyV]⟩
      exact Evaluates.mk_app e1 ⟨1, by simp only [applyV]⟩
    obtain ⟨hh, w, hev, hw⟩ := hinner
    refine ⟨hh, w, ?_, hw⟩
    refine Evaluates.appHeadSwap hKCa Evaluates.S2 ?_
    apply Evaluates.headS
    exact Evaluates.appHeadSwap (Evaluates.headK (Evaluates.Bsim Evaluates.seqVal)) Evaluates.seqVal hev
  obtain ⟨hh, w, hev, hw⟩ := key
  exact ⟨hh, w, Evaluates.headSeqK hev, hw⟩

/-- **Conjunction introduction** (effectful pairing). -/
theorem EProp.and_intro {X P Q : EProp} (hP : X ⊨ P) (hQ : X ⊨ Q) : X ⊨ P ⊓ₑ Q := by
  obtain ⟨r₁, h₁⟩ := hP
  obtain ⟨r₂, h₂⟩ := hQ
  exact ⟨Code.pairR r₁ r₂, fun h a hXa => EProp.pairProduces h₁ h₂ h a hXa⟩

/-- Case analysis: realizer `case · r₁ · r₂`, dispatched by the `case` β-rules. -/
theorem EProp.or_elim {P Q R : EProp} (hP : P ⊨ R) (hQ : Q ⊨ R) : P ⊔ₑ Q ⊨ R := by
  obtain ⟨r₁, h₁⟩ := hP
  obtain ⟨r₂, h₂⟩ := hQ
  refine ⟨case ⬝ r₁ ⬝ r₂, ?_⟩
  rintro h a (⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩)
  · obtain ⟨h', v, hev, hv⟩ := h₁ h x hx
    exact ⟨h', v, Evaluates.caseLβ hev, hv⟩
  · obtain ⟨h', v, hev, hv⟩ := h₂ h y hy
    exact ⟨h', v, Evaluates.caseRβ hev, hv⟩

/-! ## Values and implication

The implication connective `⇨ₑ` and (next) the exponential need realizers that are
*functions*: their `ev` field can't reduce a function to "a realizer of `P`" the way `∧`/`∃`
do, so we require the realizer to be a **value** (`IsVal`, eval-stable) and quantify the
producing condition over **future heaps** (`HLe`) so Kripke-monotonicity (`mono`) is free.
This is the shared pattern for both `⇨ₑ` and `Obj.expn`. -/

/-- A code is a value if it evaluates to itself at every heap (a stuck weak-head form). -/
def IsVal (c : Code) : Prop := ∀ h, Evaluates h c h c

theorem IsVal.pr {a b : Code} : IsVal (pr ⬝ a ⬝ b) := fun _ => Evaluates.prVal
theorem IsVal.inl {a : Code} : IsVal (inl ⬝ a) := fun _ => Evaluates.inlVal
theorem IsVal.inr {a : Code} : IsVal (inr ⬝ a) := fun _ => Evaluates.inrVal

/-- **Implication**: realized by a *value* `c` that, at any future heap, sends a `P`-realizer
to a `Q`-producer. The future-heap (`HLe`) quantification makes it Kripke-monotone. -/
def EProp.imp (P Q : EProp) : EProp where
  rel h c := IsVal c ∧ ∀ h' a, HLe h h' → P.rel h' a → Q.Produces h' (c ⬝ a)
  ev := by rintro h c ⟨hv, himp⟩; exact ⟨h, c, hv h, hv, himp⟩
  mono := by
    rintro h h' c hle ⟨hv, himp⟩
    exact ⟨hv, fun h'' a hle'' ha => himp h'' a (HLe.trans hle hle'') ha⟩

@[inherit_doc] infixr:60 " ⇨ₑ " => EProp.imp

end LeanStatefulAoc
