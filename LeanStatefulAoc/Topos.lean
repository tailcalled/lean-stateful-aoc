import LeanStatefulAoc.Combinators
import LeanStatefulAoc.CodeEval
import LeanStatefulAoc.Tripos

/-!
# The evaluation modality (Layer 3 substrate) — stateful application

The objects of the model (modest sets / PERs, see `Modest.lean`) are characterized
by their **equality**, and their morphisms are tracked by codes. For the headline
the tracking codes are **effectful** — the choice map `alloc`s a memo cell — so the
application underlying morphisms is the stateful evaluator `eval` (Layer 1,
checkpoint 2), not pure rewriting.

This file provides that substrate:

* `Evaluates h e h' v` — `e`, run from heap `h`, reaches value `v` leaving `h'`.
* `Produces h e Q` — the **state modality**: `e` run from `h` reaches a value
  realizing `Q` (at the resulting heap), keeping the effects in `h'`.

The eval-application here is what `Modest`'s stateful morphisms (and the AC_dec
choice function) are tracked by; the *equality* discipline that makes truncation
and `Π` correct lives in `Modest.lean`.
-/

namespace LeanStatefulAoc

open Code

/-- `e`, evaluated from heap `h`, reaches value `v` leaving heap `h'` (for some
fuel). Weak-head: `v` is in head-normal form, its sub-codes possibly unreduced. -/
def Evaluates (h : CHeap) (e : Code) (h' : CHeap) (v : Code) : Prop :=
  ∃ fuel, eval fuel h e = some (h', v)

/-- The **state modality**: `e` run from `h` produces a value realizing `Q`
(at the resulting heap). Effects performed along the way are kept in `h'`. -/
def Produces (h : CHeap) (e : Code) (Q : RProp) : Prop :=
  ∃ h' v, Evaluates h e h' v ∧ Q.rel h' v

/-- A leaf constant (non-application) is already a value: it evaluates to itself
in one step, leaving the heap unchanged. -/
theorem Evaluates.const {h : CHeap} {c : Code} (hc : ∀ f x, c ≠ f ⬝ x) :
    Evaluates h c h c := by
  refine ⟨1, ?_⟩
  cases c with
  | app f x => exact absurd rfl (hc f x)
  | _ => simp only [eval]

/-- `Produces` is monotone in the target proposition. -/
theorem Produces.mono {h : CHeap} {e : Code} {Q R : RProp}
    (hQR : ∀ h' v, Q.rel h' v → R.rel h' v) (hQ : Produces h e Q) :
    Produces h e R := by
  obtain ⟨h', v, hev, hq⟩ := hQ
  exact ⟨h', v, hev, hQR h' v hq⟩

/-- A value realizing `Q` `Produces` `Q` immediately (no effects). -/
theorem Produces.of_value {h : CHeap} {v : Code} {Q : RProp}
    (hval : ∀ f x, v ≠ f ⬝ x) (hv : Q.rel h v) : Produces h v Q :=
  ⟨h, v, Evaluates.const hval, hv⟩

end LeanStatefulAoc
