import LeanStatefulAoc.EvalTopos

set_option linter.style.longLine false

/-!
# The binary coproduct object `A ⊔ B` in the eval-model realizability topos

The coproduct's equality uses **tagged** realizers: `ρ (inl x) (inl x')` is `ρ_A x x'` injected on
the left (`inl`-headed realizers), `ρ (inr y) (inr y')` is `ρ_B y y'` on the right, and mismatched
tags relate by `⊥`. Tagging is what lets the *uniform* symmetry/transitivity realizer dispatch with
`case`: it inspects the tag of its input and routes to `A`'s or `B`'s realizer, re-tagging the
result. This is the standard realizability-topos coproduct, needed for the `AC_dec` premise
`Π x y. (x=y) + ¬(x=y)`.
-/

namespace LeanStatefulAoc

namespace Eval

open Code

/-- `case · Lr · Rr · (inl · a)` produces `R` whenever `Lr · a` does. -/
theorem caseL_produces {h : CHeap} {Lr Rr a : Code} {R : EProp} (hP : R.Produces h (Lr ⬝ a)) :
    R.Produces h (case ⬝ Lr ⬝ Rr ⬝ (inl ⬝ a)) := by
  obtain ⟨h', v, ev, hv⟩ := hP; exact ⟨h', v, Evaluates.caseLβ ev, hv⟩

/-- `case · Lr · Rr · (inr · b)` produces `R` whenever `Rr · b` does. -/
theorem caseR_produces {h : CHeap} {Lr Rr b : Code} {R : EProp} (hP : R.Produces h (Rr ⬝ b)) :
    R.Produces h (case ⬝ Lr ⬝ Rr ⬝ (inr ⬝ b)) := by
  obtain ⟨h', v, ev, hv⟩ := hP; exact ⟨h', v, Evaluates.caseRβ ev, hv⟩

theorem Evaluates.inlv {h : CHeap} : Evaluates h inl h inl := ⟨1, by simp only [eval]⟩
theorem Evaluates.inrv {h : CHeap} : Evaluates h inr h inr := ⟨1, by simp only [eval]⟩

/-- **Left tag-transport.** `S (S (K seq) s) (K inl) · a` runs `s · a` and re-tags the value with
`inl`: if `s · a` produces a `P`-realizer, the whole thing produces a `P ⊔ₑ Q`-realizer
(`inl`-headed). -/
theorem tagL_branch {h : CHeap} {s a : Code} {P Q : EProp} (hs : P.Produces h (s ⬝ a)) :
    (P ⊔ₑ Q).Produces h (S ⬝ (S ⬝ (K ⬝ seq) ⬝ s) ⬝ (K ⬝ inl) ⬝ a) := by
  obtain ⟨h1, v, ev, hv⟩ : (P ⊔ₑ Q).Produces h (seq ⬝ (s ⬝ a) ⬝ (K ⬝ inl ⬝ a)) := by
    refine EProp.Produces.bindH hs (fun h' w _ hw => ?_)
    refine EProp.Produces.headEq (g' := inl) (k := w) (fun hh u hu => Evaluates.headK hu) ?_
    exact ⟨h', inl ⬝ w, Evaluates.inlVal, Or.inl ⟨w, rfl, hw⟩⟩
  exact ⟨h1, v, Evaluates.headSeqK ev, hv⟩

/-- **Right tag-transport.** `S (S (K seq) s) (K inr) · a` runs `s · a` and re-tags with `inr`. -/
theorem tagR_branch {h : CHeap} {s a : Code} {P Q : EProp} (hs : Q.Produces h (s ⬝ a)) :
    (P ⊔ₑ Q).Produces h (S ⬝ (S ⬝ (K ⬝ seq) ⬝ s) ⬝ (K ⬝ inr) ⬝ a) := by
  obtain ⟨h1, v, ev, hv⟩ : (P ⊔ₑ Q).Produces h (seq ⬝ (s ⬝ a) ⬝ (K ⬝ inr ⬝ a)) := by
    refine EProp.Produces.bindH hs (fun h' w _ hw => ?_)
    refine EProp.Produces.headEq (g' := inr) (k := w) (fun hh u hu => Evaluates.headK hu) ?_
    exact ⟨h', inr ⬝ w, Evaluates.inrVal, Or.inr ⟨w, rfl, hw⟩⟩
  exact ⟨h1, v, Evaluates.headSeqK ev, hv⟩

/-- The tagged equality of the coproduct `A ⊔ B`. -/
def coprodRel (A B : Obj) : (A.carrier ⊕ B.carrier) → (A.carrier ⊕ B.carrier) → EProp
  | Sum.inl x, Sum.inl x' => A.rel x x' ⊔ₑ EProp.bot
  | Sum.inr y, Sum.inr y' => EProp.bot ⊔ₑ B.rel y y'
  | _, _ => EProp.bot

/-- Symmetry of the coproduct's equality: dispatch on the tag, transport via `A`/`B` symmetry,
re-tag. Realizer `case (S (S(K seq) sA) (K inl)) (S (S(K seq) sB) (K inr))`. -/
theorem coprod_symm (A B : Obj) :
    (fun p : (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) => coprodRel A B p.1 p.2) ⊢ₚ
      (fun p => coprodRel A B p.2 p.1) := by
  obtain ⟨sA, hsA⟩ := A.symm
  obtain ⟨sB, hsB⟩ := B.symm
  refine ⟨case ⬝ (S ⬝ (S ⬝ (K ⬝ seq) ⬝ sA) ⬝ (K ⬝ inl)) ⬝
    (S ⬝ (S ⬝ (K ⬝ seq) ⬝ sB) ⬝ (K ⬝ inr)), ?_⟩
  rintro ⟨u, v⟩ h a ha
  match u, v with
  | Sum.inl x, Sum.inl x' =>
    simp only [coprodRel] at ha ⊢
    obtain (⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩) := ha
    · exact caseL_produces (tagL_branch (hsA (x, x') h a' ha'))
    · exact hb'.elim
  | Sum.inl x, Sum.inr y' => simp only [coprodRel] at ha; exact ha.elim
  | Sum.inr y, Sum.inl x' => simp only [coprodRel] at ha; exact ha.elim
  | Sum.inr y, Sum.inr y' =>
    simp only [coprodRel] at ha ⊢
    obtain (⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩) := ha
    · exact ha'.elim
    · exact caseR_produces (tagR_branch (hsB (y, y') h b' hb'))

/-- Extract the payload of a tagged value, regardless of tag (`case I I`). -/
def unTag : Code := case ⬝ Code.I ⬝ Code.I

theorem unTag_inl {h h' : CHeap} {a v : Code} (hev : Evaluates h a h' v) :
    Evaluates h (unTag ⬝ (inl ⬝ a)) h' v :=
  Evaluates.caseLβ (Evaluates.I hev)

theorem unTag_inr {h h' : CHeap} {a v : Code} (hev : Evaluates h a h' v) :
    Evaluates h (unTag ⬝ (inr ⬝ a)) h' v :=
  Evaluates.caseRβ (Evaluates.I hev)

/-! ### Transitivity

The realizer dispatches on the first conjunct's tag, runs `A`/`B` transitivity on the pair of
payloads `pr · a' · b'`, and re-tags. Built like `expn_trans`: combinators with transport lemmas
that trace through the unevaluated tails CBV leaves behind. -/

/-- `cInnerL eAt · a' · b' ↠ seq · (eAt · (pr · a' · b')) · inl` — run `A`-transitivity on the
payload pair, then re-tag `inl`. -/
def cInnerL (eAt : Code) : Code :=
  S ⬝ (Code.B ⬝ S ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ seq))) ⬝ (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr))) ⬝ (K ⬝ (K ⬝ inl))

/-- `cInnerL eAt · a'` evaluates to the (tailed) value `S (Z₀·a') (K(K inl)·a')`. -/
theorem cInnerL_eval {eAt a' : Code} (hp : CHeap) :
    Evaluates hp (cInnerL eAt ⬝ a') hp
      (S ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ seq))) ⬝ (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr) ⬝ a') ⬝
        (K ⬝ (K ⬝ inl) ⬝ a')) := by
  simp only [cInnerL]
  apply Evaluates.headS
  refine Evaluates.mk_app
    (fv := S ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ seq))) ⬝ (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr) ⬝ a'))
    (Evaluates.Bsim Evaluates.S1) ⟨1, by simp only [applyV]⟩

/-- Transport: `B (B eAt) pr · a' · b'` runs like `eAt · (pr · a' · b')`. -/
theorem cBBpr_apply {eAt a' b' : Code} {hp hh : CHeap} {v : Code}
    (hev : Evaluates hp (eAt ⬝ (pr ⬝ a' ⬝ b')) hh v) :
    Evaluates hp (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr ⬝ a' ⬝ b') hh v := by
  refine Evaluates.appHeadSwap (g' := S ⬝ (K ⬝ eAt) ⬝ (pr ⬝ a'))
    (Evaluates.Bsim (Evaluates.mk_app Evaluates.B1 ⟨1, by simp only [applyV]⟩)) Evaluates.S2 ?_
  apply Evaluates.headS
  obtain ⟨h2, eAtv, heAt, m, happ⟩ := Evaluates.app_inv hev
  exact Evaluates.mk_app (Evaluates.headK heAt) ⟨m, happ⟩

/-- `S (K (S(K seq))) (B(B eAt) pr) · a' · b' ↠ seq · (B(B eAt) pr · a' · b')`. -/
theorem cZ0_eval {eAt a' b' : Code} (hp : CHeap) :
    Evaluates hp (S ⬝ (K ⬝ (S ⬝ (K ⬝ seq))) ⬝ (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr) ⬝ a' ⬝ b') hp
      (seq ⬝ (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr ⬝ a' ⬝ b')) := by
  refine Evaluates.appHeadSwap (g' := S ⬝ (K ⬝ seq) ⬝ (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr ⬝ a'))
    (Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.S1) ⟨1, by simp only [applyV]⟩))
    Evaluates.S2 ?_
  exact Evaluates.headS (Evaluates.mk_app (Evaluates.headK Evaluates.seqv) ⟨1, by simp only [applyV]⟩)

/-- **Left transitivity branch produces.** If `eAt · (pr · a' · b')` produces a `P`-realizer
(`A`-transitivity applied to the payload pair), then `cInnerL eAt · a' · b'` produces a
`P ⊔ₑ Q`-realizer (`inl`-tagged). -/
theorem cInnerL_produces {eAt a' b' : Code} {P Q : EProp} {hp : CHeap}
    (hP : P.Produces hp (eAt ⬝ (pr ⬝ a' ⬝ b'))) :
    (P ⊔ₑ Q).Produces hp (cInnerL eAt ⬝ a' ⬝ b') := by
  obtain ⟨hh, w, ev, hw⟩ : (P ⊔ₑ Q).Produces hp
      (seq ⬝ (Code.B ⬝ (Code.B ⬝ eAt) ⬝ pr ⬝ a' ⬝ b') ⬝ (K ⬝ (K ⬝ inl) ⬝ a' ⬝ b')) := by
    refine EProp.Produces.bindH (Q := P) ?_ (fun h' v _ hv => ?_)
    · obtain ⟨h', v, ev', hv'⟩ := hP; exact ⟨h', v, cBBpr_apply ev', hv'⟩
    · refine EProp.Produces.headEq (g' := inl) (k := v)
        (fun hhh u hu => Evaluates.appHeadSwap (Evaluates.headK Evaluates.K1) Evaluates.K1
          (Evaluates.headK hu)) ?_
      exact ⟨h', inl ⬝ v, Evaluates.inlVal, Or.inl ⟨v, rfl, hv⟩⟩
  refine ⟨hh, w, ?_, hw⟩
  refine Evaluates.appHeadSwap (cInnerL_eval hp) Evaluates.S2 ?_
  apply Evaluates.headS
  exact Evaluates.appHeadSwap (cZ0_eval hp) Evaluates.seqVal ev

/-- `cInnerR eBt · a' · b' ↠ seq · (eBt · (pr · a' · b')) · inr` — the right (B) branch. -/
def cInnerR (eBt : Code) : Code :=
  S ⬝ (Code.B ⬝ S ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ seq))) ⬝ (Code.B ⬝ (Code.B ⬝ eBt) ⬝ pr))) ⬝ (K ⬝ (K ⬝ inr))

theorem cInnerR_eval {eBt a' : Code} (hp : CHeap) :
    Evaluates hp (cInnerR eBt ⬝ a') hp
      (S ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ seq))) ⬝ (Code.B ⬝ (Code.B ⬝ eBt) ⬝ pr) ⬝ a') ⬝
        (K ⬝ (K ⬝ inr) ⬝ a')) := by
  simp only [cInnerR]
  apply Evaluates.headS
  refine Evaluates.mk_app
    (fv := S ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ seq))) ⬝ (Code.B ⬝ (Code.B ⬝ eBt) ⬝ pr) ⬝ a'))
    (Evaluates.Bsim Evaluates.S1) ⟨1, by simp only [applyV]⟩

/-- **Right transitivity branch produces** (`inr`-tagged). -/
theorem cInnerR_produces {eBt a' b' : Code} {P Q : EProp} {hp : CHeap}
    (hQ : Q.Produces hp (eBt ⬝ (pr ⬝ a' ⬝ b'))) :
    (P ⊔ₑ Q).Produces hp (cInnerR eBt ⬝ a' ⬝ b') := by
  obtain ⟨hh, w, ev, hw⟩ : (P ⊔ₑ Q).Produces hp
      (seq ⬝ (Code.B ⬝ (Code.B ⬝ eBt) ⬝ pr ⬝ a' ⬝ b') ⬝ (K ⬝ (K ⬝ inr) ⬝ a' ⬝ b')) := by
    refine EProp.Produces.bindH (Q := Q) ?_ (fun h' v _ hv => ?_)
    · obtain ⟨h', v, ev', hv'⟩ := hQ; exact ⟨h', v, cBBpr_apply ev', hv'⟩
    · refine EProp.Produces.headEq (g' := inr) (k := v)
        (fun hhh u hu => Evaluates.appHeadSwap (Evaluates.headK Evaluates.K1) Evaluates.K1
          (Evaluates.headK hu)) ?_
      exact ⟨h', inr ⬝ v, Evaluates.inrVal, Or.inr ⟨v, rfl, hv⟩⟩
  refine ⟨hh, w, ?_, hw⟩
  refine Evaluates.appHeadSwap (cInnerR_eval hp) Evaluates.S2 ?_
  apply Evaluates.headS
  exact Evaluates.appHeadSwap (cZ0_eval hp) Evaluates.seqVal ev

/-- Left branch builder: `cBL eAt · b · a' ↠ seq · (unTag · b) · (cInnerL eAt · a')` — force the
second payload out of `b`, then run the left inner branch. -/
def cBL (eAt : Code) : Code :=
  S ⬝ (Code.B ⬝ S ⬝ (Code.B ⬝ K ⬝ (Code.B ⬝ seq ⬝ unTag))) ⬝ (K ⬝ (cInnerL eAt))

/-- Right branch builder (mirror of `cBL`, inner branch `cInnerR`). -/
def cBR (eBt : Code) : Code :=
  S ⬝ (Code.B ⬝ S ⬝ (Code.B ⬝ K ⬝ (Code.B ⬝ seq ⬝ unTag))) ⬝ (K ⬝ (cInnerR eBt))

/-- Transport for `cBL`: a run of `seq · (unTag · b) · (K (cInner) b a')` lifts to `cBL eAt · b · a'`.
(The continuation `K (cInnerL eAt) b a'` reduces to `cInnerL eAt · a'`.) -/
theorem cBL_apply {eAt b a' : Code} {hp hh : CHeap} {w : Code}
    (hev : Evaluates hp (seq ⬝ (unTag ⬝ b) ⬝ (K ⬝ (cInnerL eAt) ⬝ b ⬝ a')) hh w) :
    Evaluates hp (cBL eAt ⬝ b ⬝ a') hh w := by
  have hbl : Evaluates hp (cBL eAt ⬝ b) hp
      (S ⬝ (Code.B ⬝ K ⬝ (Code.B ⬝ seq ⬝ unTag) ⬝ b) ⬝ (K ⬝ (cInnerL eAt) ⬝ b)) := by
    simp only [cBL]
    apply Evaluates.headS
    exact Evaluates.mk_app (fv := S ⬝ (Code.B ⬝ K ⬝ (Code.B ⬝ seq ⬝ unTag) ⬝ b))
      (Evaluates.Bsim Evaluates.S1) ⟨1, by simp only [applyV]⟩
  refine Evaluates.appHeadSwap hbl Evaluates.S2 ?_
  apply Evaluates.headS
  refine Evaluates.appHeadSwap (g' := seq ⬝ (unTag ⬝ b)) ?_ Evaluates.seqVal hev
  -- (B K (B seq unTag) b) · a' ↠ seq (unTag b)
  refine Evaluates.appHeadSwap (Evaluates.Bsim Evaluates.K1) Evaluates.K1 ?_
  exact Evaluates.headK (Evaluates.Bsim Evaluates.seqVal)

/-- Transport for `cBR`. -/
theorem cBR_apply {eBt b a' : Code} {hp hh : CHeap} {w : Code}
    (hev : Evaluates hp (seq ⬝ (unTag ⬝ b) ⬝ (K ⬝ (cInnerR eBt) ⬝ b ⬝ a')) hh w) :
    Evaluates hp (cBR eBt ⬝ b ⬝ a') hh w := by
  have hbr : Evaluates hp (cBR eBt ⬝ b) hp
      (S ⬝ (Code.B ⬝ K ⬝ (Code.B ⬝ seq ⬝ unTag) ⬝ b) ⬝ (K ⬝ (cInnerR eBt) ⬝ b)) := by
    simp only [cBR]
    apply Evaluates.headS
    exact Evaluates.mk_app (fv := S ⬝ (Code.B ⬝ K ⬝ (Code.B ⬝ seq ⬝ unTag) ⬝ b))
      (Evaluates.Bsim Evaluates.S1) ⟨1, by simp only [applyV]⟩
  refine Evaluates.appHeadSwap hbr Evaluates.S2 ?_
  apply Evaluates.headS
  refine Evaluates.appHeadSwap (g' := seq ⬝ (unTag ⬝ b)) ?_ Evaluates.seqVal hev
  refine Evaluates.appHeadSwap (Evaluates.Bsim Evaluates.K1) Evaluates.K1 ?_
  exact Evaluates.headK (Evaluates.Bsim Evaluates.seqVal)

/-- The transitivity realizer: dispatch on the first conjunct's tag (`fst`), feeding the second
conjunct (`snd`) into the matching branch builder. -/
def coprodTransR (eAt eBt : Code) : Code :=
  S ⬝ (S ⬝ (S ⬝ (K ⬝ case) ⬝ (Code.B ⬝ cBL eAt ⬝ snd)) ⬝ (Code.B ⬝ cBR eBt ⬝ snd)) ⬝ fst

theorem case_val {h : CHeap} : Evaluates h case h case := ⟨1, by simp only [eval]⟩

theorem case2_val {f g : Code} {h : CHeap} : Evaluates h (case ⬝ f ⬝ g) h (case ⬝ f ⬝ g) :=
  ⟨3, by simp only [eval, applyV]⟩

/-- The dispatch head: `S (S (K case) (B cBL snd)) (B cBR snd) · input ↠ case · (cBL eAt · snd · input) · (cBR eBt · snd · input)`. -/
theorem coprodTransR_disp {eAt eBt input : Code} (hp : CHeap) :
    Evaluates hp (S ⬝ (S ⬝ (K ⬝ case) ⬝ (Code.B ⬝ cBL eAt ⬝ snd)) ⬝ (Code.B ⬝ cBR eBt ⬝ snd) ⬝ input)
      hp (case ⬝ (Code.B ⬝ cBL eAt ⬝ snd ⬝ input) ⬝ (Code.B ⬝ cBR eBt ⬝ snd ⬝ input)) := by
  have hhd : Evaluates hp (S ⬝ (K ⬝ case) ⬝ (Code.B ⬝ cBL eAt ⬝ snd) ⬝ input) hp
      (case ⬝ (Code.B ⬝ cBL eAt ⬝ snd ⬝ input)) :=
    Evaluates.headS (Evaluates.mk_app (Evaluates.headK case_val) ⟨1, by simp only [applyV]⟩)
  apply Evaluates.headS
  exact Evaluates.mk_app hhd ⟨1, by simp only [applyV]⟩

/-- Left-tag dispatch: if `fst input ↠ inl·a'` and `cBL eAt · (snd input) · a' ↠ w`, then
`coprodTransR eAt eBt · input ↠ w`. -/
theorem coprodTransR_caseL {eAt eBt input a' : Code} {hp hh : CHeap} {w : Code}
    (hfst : Evaluates hp (fst ⬝ input) hp (inl ⬝ a'))
    (hCL : Evaluates hp (cBL eAt ⬝ (snd ⬝ input) ⬝ a') hh w) :
    Evaluates hp (coprodTransR eAt eBt ⬝ input) hh w := by
  simp only [coprodTransR]
  apply Evaluates.headS
  refine Evaluates.appHeadSwap (coprodTransR_disp hp) case2_val ?_
  refine Evaluates.caseLβ' hfst ?_
  obtain ⟨h2, cblval, hcbl, m, happ⟩ := Evaluates.app_inv hCL
  exact Evaluates.mk_app (Evaluates.Bsim hcbl) ⟨m, happ⟩

/-- Right-tag dispatch. -/
theorem coprodTransR_caseR {eAt eBt input a' : Code} {hp hh : CHeap} {w : Code}
    (hfst : Evaluates hp (fst ⬝ input) hp (inr ⬝ a'))
    (hCR : Evaluates hp (cBR eBt ⬝ (snd ⬝ input) ⬝ a') hh w) :
    Evaluates hp (coprodTransR eAt eBt ⬝ input) hh w := by
  simp only [coprodTransR]
  apply Evaluates.headS
  refine Evaluates.appHeadSwap (coprodTransR_disp hp) case2_val ?_
  refine Evaluates.caseRβ' hfst ?_
  obtain ⟨h2, cbrval, hcbr, m, happ⟩ := Evaluates.app_inv hCR
  exact Evaluates.mk_app (Evaluates.Bsim hcbr) ⟨m, happ⟩

theorem cInnerL_val {eAt : Code} {h : CHeap} : Evaluates h (cInnerL eAt) h (cInnerL eAt) := by
  simp only [cInnerL]; exact Evaluates.S2

theorem cInnerR_val {eBt : Code} {h : CHeap} : Evaluates h (cInnerR eBt) h (cInnerR eBt) := by
  simp only [cInnerR]; exact Evaluates.S2

/-- Left branch production: force the right payload out of `s` (`unTag`), then run `A`-transitivity
on the payload pair and tag `inl`. -/
theorem cBL_branch_produces {eAt a' s : Code} {Pmid P Q : EProp} {hp : CHeap}
    (hb : Pmid.Produces hp (unTag ⬝ s))
    (hP : ∀ h' v', HLe hp h' → Pmid.rel h' v' → P.Produces h' (eAt ⬝ (pr ⬝ a' ⬝ v'))) :
    (P ⊔ₑ Q).Produces hp (cBL eAt ⬝ s ⬝ a') := by
  obtain ⟨hh, ww, ev, hww⟩ : (P ⊔ₑ Q).Produces hp
      (seq ⬝ (unTag ⬝ s) ⬝ (K ⬝ (cInnerL eAt) ⬝ s ⬝ a')) := by
    refine EProp.Produces.bindH (Q := Pmid) hb (fun h' v' hle hv' => ?_)
    refine EProp.Produces.headEq (g' := cInnerL eAt ⬝ a') (k := v')
      (fun hhh u hu => Evaluates.appHeadSwap (Evaluates.headK cInnerL_val) cInnerL_val hu) ?_
    exact cInnerL_produces (hP h' v' hle hv')
  exact ⟨hh, ww, cBL_apply ev, hww⟩

/-- Right branch production (mirror, `B`-transitivity, tag `inr`). -/
theorem cBR_branch_produces {eBt a' s : Code} {Pmid P Q : EProp} {hp : CHeap}
    (hb : Pmid.Produces hp (unTag ⬝ s))
    (hQ : ∀ h' v', HLe hp h' → Pmid.rel h' v' → Q.Produces h' (eBt ⬝ (pr ⬝ a' ⬝ v'))) :
    (P ⊔ₑ Q).Produces hp (cBR eBt ⬝ s ⬝ a') := by
  obtain ⟨hh, ww, ev, hww⟩ : (P ⊔ₑ Q).Produces hp
      (seq ⬝ (unTag ⬝ s) ⬝ (K ⬝ (cInnerR eBt) ⬝ s ⬝ a')) := by
    refine EProp.Produces.bindH (Q := Pmid) hb (fun h' v' hle hv' => ?_)
    refine EProp.Produces.headEq (g' := cInnerR eBt ⬝ a') (k := v')
      (fun hhh u hu => Evaluates.appHeadSwap (Evaluates.headK cInnerR_val) cInnerR_val hu) ?_
    exact cInnerR_produces (hQ h' v' hle hv')
  exact ⟨hh, ww, cBR_apply ev, hww⟩

/-- Transitivity of the coproduct's equality. -/
theorem coprod_trans (A B : Obj) :
    (fun p : (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        coprodRel A B p.1 p.2.1 ⊓ₑ coprodRel A B p.2.1 p.2.2) ⊢ₚ
      (fun p => coprodRel A B p.1 p.2.2) := by
  obtain ⟨eAt, hAt⟩ := A.trans
  obtain ⟨eBt, hBt⟩ := B.trans
  refine ⟨coprodTransR eAt eBt, ?_⟩
  rintro ⟨u, v, w⟩ h c ⟨a, b, rfl, ha, hb⟩
  match u, v, w with
  | Sum.inl x, Sum.inl x', Sum.inl x'' =>
    simp only [coprodRel] at ha hb ⊢
    obtain (⟨a', rfl, ha'⟩ | ⟨_, _, hbot⟩) := ha
    · obtain (⟨b', rfl, hb'⟩ | ⟨_, _, hbot⟩) := hb
      · obtain ⟨h2, vb, evb, hvb⟩ := (A.rel x' x'').ev hb'
        obtain ⟨hh, ww, ev, hww⟩ := cBL_branch_produces
          (eAt := eAt) (a' := a') (s := snd ⬝ (pr ⬝ (inl ⬝ a') ⬝ (inl ⬝ b')))
          (Pmid := A.rel x' x'') (P := A.rel x x'') (Q := EProp.bot)
          ⟨h2, vb, Evaluates.caseLβ' Evaluates.sndβ (Evaluates.I evb), hvb⟩
          (fun h' v' hle hv' =>
            hAt (x, x', x'') h' (pr ⬝ a' ⬝ v') ⟨a', v', rfl, (A.rel x x').mono hle ha', hv'⟩)
        exact ⟨hh, ww, coprodTransR_caseL Evaluates.fstβ ev, hww⟩
      · exact hbot.elim
    · exact hbot.elim
  | Sum.inr y, Sum.inr y', Sum.inr y'' =>
    simp only [coprodRel] at ha hb ⊢
    obtain (⟨_, _, hbot⟩ | ⟨a', rfl, ha'⟩) := ha
    · exact hbot.elim
    · obtain (⟨_, _, hbot⟩ | ⟨b', rfl, hb'⟩) := hb
      · exact hbot.elim
      · obtain ⟨h2, vb, evb, hvb⟩ := (B.rel y' y'').ev hb'
        obtain ⟨hh, ww, ev, hww⟩ := cBR_branch_produces
          (eBt := eBt) (a' := a') (s := snd ⬝ (pr ⬝ (inr ⬝ a') ⬝ (inr ⬝ b')))
          (Pmid := B.rel y' y'') (P := EProp.bot) (Q := B.rel y y'')
          ⟨h2, vb, Evaluates.caseRβ' Evaluates.sndβ (Evaluates.I evb), hvb⟩
          (fun h' v' hle hv' =>
            hBt (y, y', y'') h' (pr ⬝ a' ⬝ v') ⟨a', v', rfl, (B.rel y y').mono hle ha', hv'⟩)
        exact ⟨hh, ww, coprodTransR_caseR Evaluates.fstβ ev, hww⟩
  | Sum.inl x, Sum.inl x', Sum.inr y => simp only [coprodRel] at hb; exact hb.elim
  | Sum.inl x, Sum.inr y, Sum.inl x' => simp only [coprodRel] at ha; exact ha.elim
  | Sum.inl x, Sum.inr y, Sum.inr y' => simp only [coprodRel] at ha; exact ha.elim
  | Sum.inr y, Sum.inl x, Sum.inl x' => simp only [coprodRel] at ha; exact ha.elim
  | Sum.inr y, Sum.inl x, Sum.inr y' => simp only [coprodRel] at ha; exact ha.elim
  | Sum.inr y, Sum.inr y', Sum.inl x => simp only [coprodRel] at hb; exact hb.elim

/-- **The binary coproduct object `A ⊔ B`.** -/
def coprod (A B : Obj) : Obj where
  carrier := A.carrier ⊕ B.carrier
  rel := coprodRel A B
  symm := coprod_symm A B
  trans := coprod_trans A B

/-- The left injection `A ⟶ A ⊔ B`; its graph is `x ↦ inl x` (`rel x u := ρ_{A⊔B} (inl x) u`). All
five functional-relation axioms reduce to `coprod`'s own equality structure (reindexed) plus the
`inl` injection / `⊔ₑ ⊥` elimination. -/
def Hom.coprodInl (A B : Obj) : Hom A (coprod A B) where
  rel x u := coprodRel A B (Sum.inl x) u
  strict_dom :=
    PLe.trans (PLe.reindex (fun p : A.carrier × (A.carrier ⊕ B.carrier) => (Sum.inl p.1, p.2))
      (coprod A B).rel_ext_left) (PLe.or_elim (PLe.refl _) ⟨Code.I, fun _ _ _ h => h.elim⟩)
  strict_cod := PLe.reindex (fun p : A.carrier × (A.carrier ⊕ B.carrier) => (Sum.inl p.1, p.2))
    (coprod A B).rel_ext_right
  total := PLe.trans (PLe.inl (fun x => A.rel x x) (fun _ => EProp.bot))
    (PLe.ex_intro (fun x (u : A.carrier ⊕ B.carrier) => coprodRel A B (Sum.inl x) u)
      (fun x => Sum.inl x))
  congr := by
    have hAxx' := PLe.trans
      (PLe.and_left (X := A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier))
        (fun p => A.rel p.1 p.2.1 ⊓ₑ coprodRel A B p.2.2.1 p.2.2.2)
        (fun p => coprodRel A B (Sum.inl p.1) p.2.2.1))
      (PLe.and_left
        (fun p : A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
          A.rel p.1 p.2.1) (fun p => coprodRel A B p.2.2.1 p.2.2.2))
    have h_x'x := PLe.trans (PLe.trans hAxx'
        (PLe.inl (fun p : A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
          A.rel p.1 p.2.1) (fun _ => EProp.bot)))
      (PLe.reindex (fun p : A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        ((Sum.inl p.1 : A.carrier ⊕ B.carrier), Sum.inl p.2.1)) (coprod A B).symm)
    have h_xu := PLe.and_right
      (fun p : A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        A.rel p.1 p.2.1 ⊓ₑ coprodRel A B p.2.2.1 p.2.2.2)
      (fun p => coprodRel A B (Sum.inl p.1) p.2.2.1)
    have h_uu' := PLe.trans
      (PLe.and_left (X := A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier))
        (fun p => A.rel p.1 p.2.1 ⊓ₑ coprodRel A B p.2.2.1 p.2.2.2)
        (fun p => coprodRel A B (Sum.inl p.1) p.2.2.1))
      (PLe.and_right
        (fun p : A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
          A.rel p.1 p.2.1) (fun p => coprodRel A B p.2.2.1 p.2.2.2))
    have h_x'u := PLe.trans (PLe.and_intro h_x'x h_xu)
      (PLe.reindex (fun p : A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        (Sum.inl p.2.1, Sum.inl p.1, p.2.2.1)) (coprod A B).trans)
    exact PLe.trans (PLe.and_intro h_x'u h_uu')
      (PLe.reindex (fun p : A.carrier × A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        (Sum.inl p.2.1, p.2.2.1, p.2.2.2)) (coprod A B).trans)
  sv := by
    have h_xu := PLe.and_left
      (fun p : A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        coprodRel A B (Sum.inl p.1) p.2.1) (fun p => coprodRel A B (Sum.inl p.1) p.2.2)
    have h_ux := PLe.trans h_xu
      (PLe.reindex (fun p : A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        ((Sum.inl p.1 : A.carrier ⊕ B.carrier), p.2.1)) (coprod A B).symm)
    have h_xu' := PLe.and_right
      (fun p : A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        coprodRel A B (Sum.inl p.1) p.2.1) (fun p => coprodRel A B (Sum.inl p.1) p.2.2)
    exact PLe.trans (PLe.and_intro h_ux h_xu')
      (PLe.reindex (fun p : A.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        (p.2.1, Sum.inl p.1, p.2.2)) (coprod A B).trans)

/-- The right injection `B ⟶ A ⊔ B`; its graph is `y ↦ inr y`. -/
def Hom.coprodInr (A B : Obj) : Hom B (coprod A B) where
  rel y u := coprodRel A B (Sum.inr y) u
  strict_dom :=
    PLe.trans (PLe.reindex (fun p : B.carrier × (A.carrier ⊕ B.carrier) => (Sum.inr p.1, p.2))
      (coprod A B).rel_ext_left) (PLe.or_elim ⟨Code.I, fun _ _ _ h => h.elim⟩ (PLe.refl _))
  strict_cod := PLe.reindex (fun p : B.carrier × (A.carrier ⊕ B.carrier) => (Sum.inr p.1, p.2))
    (coprod A B).rel_ext_right
  total := PLe.trans (PLe.inr (fun _ => EProp.bot) (fun y => B.rel y y))
    (PLe.ex_intro (fun y (u : A.carrier ⊕ B.carrier) => coprodRel A B (Sum.inr y) u)
      (fun y => Sum.inr y))
  congr := by
    have hByy' := PLe.trans
      (PLe.and_left (X := B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier))
        (fun p => B.rel p.1 p.2.1 ⊓ₑ coprodRel A B p.2.2.1 p.2.2.2)
        (fun p => coprodRel A B (Sum.inr p.1) p.2.2.1))
      (PLe.and_left
        (fun p : B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
          B.rel p.1 p.2.1) (fun p => coprodRel A B p.2.2.1 p.2.2.2))
    have h_y'y := PLe.trans (PLe.trans hByy'
        (PLe.inr (fun _ => EProp.bot)
          (fun p : B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
            B.rel p.1 p.2.1)))
      (PLe.reindex (fun p : B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        ((Sum.inr p.1 : A.carrier ⊕ B.carrier), Sum.inr p.2.1)) (coprod A B).symm)
    have h_yu := PLe.and_right
      (fun p : B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        B.rel p.1 p.2.1 ⊓ₑ coprodRel A B p.2.2.1 p.2.2.2)
      (fun p => coprodRel A B (Sum.inr p.1) p.2.2.1)
    have h_uu' := PLe.trans
      (PLe.and_left (X := B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier))
        (fun p => B.rel p.1 p.2.1 ⊓ₑ coprodRel A B p.2.2.1 p.2.2.2)
        (fun p => coprodRel A B (Sum.inr p.1) p.2.2.1))
      (PLe.and_right
        (fun p : B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
          B.rel p.1 p.2.1) (fun p => coprodRel A B p.2.2.1 p.2.2.2))
    have h_y'u := PLe.trans (PLe.and_intro h_y'y h_yu)
      (PLe.reindex (fun p : B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        (Sum.inr p.2.1, Sum.inr p.1, p.2.2.1)) (coprod A B).trans)
    exact PLe.trans (PLe.and_intro h_y'u h_uu')
      (PLe.reindex (fun p : B.carrier × B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        (Sum.inr p.2.1, p.2.2.1, p.2.2.2)) (coprod A B).trans)
  sv := by
    have h_yu := PLe.and_left
      (fun p : B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        coprodRel A B (Sum.inr p.1) p.2.1) (fun p => coprodRel A B (Sum.inr p.1) p.2.2)
    have h_uy := PLe.trans h_yu
      (PLe.reindex (fun p : B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        ((Sum.inr p.1 : A.carrier ⊕ B.carrier), p.2.1)) (coprod A B).symm)
    have h_yu' := PLe.and_right
      (fun p : B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        coprodRel A B (Sum.inr p.1) p.2.1) (fun p => coprodRel A B (Sum.inr p.1) p.2.2)
    exact PLe.trans (PLe.and_intro h_uy h_yu')
      (PLe.reindex (fun p : B.carrier × (A.carrier ⊕ B.carrier) × (A.carrier ⊕ B.carrier) =>
        (p.2.1, Sum.inr p.1, p.2.2)) (coprod A B).trans)

end Eval

end LeanStatefulAoc
