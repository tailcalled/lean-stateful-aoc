import LeanStatefulAoc.Tripos
import LeanStatefulAoc.Confluence

/-!
# Forward reduction-closure of truth values

`RProp` is closed under *anti*-reduction (`exp`) by construction. The effectful
layer also needs **forward** closure: a realizer that *reduces* still realizes — so
that a pure transport realizer, applied to a produced value, evaluates to a value
that still realizes the target. We capture this as the predicate `FwdClosed` and
prove the connectives preserve it. The non-trivial cases (`⊓`, `⊔`) use
**confluence** (`Confluence.lean`) plus head-shape preservation: if `e` realizes
`P ⊓ Q` (so `e ↠ pr·a·b`) and `e ↠ e'`, confluence joins them and the join is still
`pr`-headed, so `e'` realizes `P ⊓ Q` too.
-/

namespace LeanStatefulAoc

open Code

/-- `P` is closed under forward reduction: reducing a realizer preserves realizing. -/
def RProp.FwdClosed (P : RProp) : Prop := ∀ {h e e'}, Code.Red e e' → P.rel h e → P.rel h e'

/-- Forward closure extends to multi-step reduction. -/
theorem RProp.FwdClosed.reds {P : RProp} (hP : P.FwdClosed) {h e e'} (r : Code.Reds e e') :
    P.rel h e → P.rel h e' := by
  induction r with
  | refl => exact id
  | tail _ r2 ih => exact fun he => hP r2 (ih he)

theorem RProp.top_fwd : RProp.top.FwdClosed := fun _ _ => trivial

theorem RProp.bot_fwd : RProp.bot.FwdClosed := fun _ h => h.elim

theorem RProp.and_fwd {P Q : RProp} (hP : P.FwdClosed) (hQ : Q.FwdClosed) :
    (P ⊓ᵣ Q).FwdClosed := by
  intro h e e' r hand
  obtain ⟨a, b, hred, ha, hb⟩ := hand
  obtain ⟨d, hd1, hd2⟩ := Code.Reds.confluent hred (Code.Reds.single r)
  obtain ⟨a', b', rfl, haa', hbb'⟩ := Code.Reds.pr_head hd1
  exact ⟨a', b', hd2, hP.reds haa' ha, hQ.reds hbb' hb⟩

theorem RProp.or_fwd {P Q : RProp} (hP : P.FwdClosed) (hQ : Q.FwdClosed) :
    (P ⊔ᵣ Q).FwdClosed := by
  intro h e e' r hor
  rcases hor with ⟨a, hred, ha⟩ | ⟨b, hred, hb⟩
  · obtain ⟨d, hd1, hd2⟩ := Code.Reds.confluent hred (Code.Reds.single r)
    obtain ⟨a', rfl, haa'⟩ := Code.Reds.inl_head hd1
    exact Or.inl ⟨a', hd2, hP.reds haa' ha⟩
  · obtain ⟨d, hd1, hd2⟩ := Code.Reds.confluent hred (Code.Reds.single r)
    obtain ⟨b', rfl, hbb'⟩ := Code.Reds.inr_head hd1
    exact Or.inr ⟨b', hd2, hQ.reds hbb' hb⟩

theorem RProp.imp_fwd {P Q : RProp} (hQ : Q.FwdClosed) : (P ⇨ᵣ Q).FwdClosed :=
  fun r hf a ha => hQ (Code.Red.appL r) (hf a ha)

theorem RProp.ex_fwd {I : Type} {φ : I → RProp} (hφ : ∀ i, (φ i).FwdClosed) :
    (RProp.ex I φ).FwdClosed :=
  fun r hex => ⟨hex.choose, hφ hex.choose r hex.choose_spec⟩

end LeanStatefulAoc
