import LeanStatefulAoc.CodeEval

/-!
# Fuel monotonicity of the evaluator

`eval`/`applyV` only consult their fuel through (mutually recursive) `eval` calls,
and a stuck/value result never *needs* more fuel — so giving more fuel never
changes a successful result. This `eval_mono` is the keystone for `Produces.bind`:
sequencing two effectful computations via `seq` runs both at one shared fuel, so we
must be able to raise each sub-computation's fuel to their common maximum.

Proof shape: the `applyV` case analysis (15 arms) is factored into
`applyV_mono_of_eval_mono`, parametric in eval-monotonicity *at the same fuel*;
then `eval_mono` is a one-line induction feeding itself in. Fuel-independent arms
close by `simpa`; eval arms re-use the monotonicity hypothesis on the inner call.
-/

namespace LeanStatefulAoc

open Code

/-- The `applyV` half of fuel monotonicity, assuming the `eval` half at fuel `n`. -/
theorem applyV_mono_of_eval_mono (n : Nat)
    (hev : ∀ h e r, eval n h e = some r → eval (n + 1) h e = some r) :
    ∀ h fv x r, applyV n h fv x = some r → applyV (n + 1) h fv x = some r := by
  intro h fv x r hx
  -- An eval-then-return arm: bump the single inner `eval` via `hev`.
  cases fv <;> try (simpa only [applyV] using hx)
  -- remaining top-level arms: fst, snd, memo, app
  case fst =>
    simp only [applyV] at hx ⊢
    cases hxe : eval n h x with
    | none => simp [hxe] at hx
    | some p => rw [hev h x p hxe]; rwa [hxe] at hx
  case snd =>
    simp only [applyV] at hx ⊢
    cases hxe : eval n h x with
    | none => simp [hxe] at hx
    | some p => rw [hev h x p hxe]; rwa [hxe] at hx
  case memo =>
    simp only [applyV] at hx ⊢
    cases hxe : eval n h x with
    | none => simp [hxe] at hx
    | some p => rw [hev h x p hxe]; rwa [hxe] at hx
  case app f y =>
    cases f <;> try (simpa only [applyV] using hx)
    -- remaining: app K y, app memo y, app seq y, app (app g z) y
    case K =>
      simp only [applyV] at hx ⊢
      cases hy : eval n h y with
      | none => simp [hy] at hx
      | some p => rw [hev h y p hy]; rwa [hy] at hx
    case seq =>
      simp only [applyV] at hx ⊢
      cases hy : eval n h y with
      | none => simp [hy] at hx
      | some p =>
        obtain ⟨h', v⟩ := p
        rw [hev h y (h', v) hy]; rw [hy] at hx
        exact hev h' (Code.app x v) r hx
    case memo =>
      cases y <;> try (simpa only [applyV] using hx)
      case loc ℓ =>
        simp only [applyV] at hx ⊢
        cases hxe : eval n h x with
        | none => simp [hxe] at hx
        | some p =>
          obtain ⟨h1, key⟩ := p
          rw [hev h x (h1, key) hxe]; rw [hxe] at hx
          cases hc : h1[ℓ]? with
          | none => simp only [hc] at hx ⊢; exact hx
          | some cell =>
            simp only [hc] at hx ⊢
            cases hf : cell.cache.find? (fun p => decide (p.1 = key)) with
            | some pr => simp only [hf] at hx ⊢; exact hx
            | none =>
              simp only [hf] at hx ⊢
              cases hfam : eval n h1 (Code.app cell.fam key) with
              | none => simp [hfam] at hx
              | some p2 =>
                obtain ⟨h2, v⟩ := p2
                rw [hev h1 (Code.app cell.fam key) (h2, v) hfam]; rw [hfam] at hx
                cases h2[ℓ]? <;> exact hx
    case app g z =>
      cases g <;> try (simpa only [applyV] using hx)
      case S =>
        simp only [applyV] at hx ⊢
        cases hb : eval n h (Code.app (Code.app z x) (Code.app y x)) with
        | none => simp [hb] at hx
        | some p => rw [hev h _ p hb]; rwa [hb] at hx
      case case =>
        simp only [applyV] at hx ⊢
        cases hxe : eval n h x with
        | none => simp [hxe] at hx
        | some p =>
          obtain ⟨h', val⟩ := p
          rw [hev h x (h', val) hxe]; rw [hxe] at hx
          cases val <;> first
            | exact hx
            | (rename_i a b; cases a <;> first
                | exact hx
                | exact hev h' (Code.app z b) r hx
                | exact hev h' (Code.app y b) r hx)

/-- **Fuel monotonicity of `eval`**: more fuel never invalidates a successful run. -/
theorem eval_mono : ∀ (n : Nat) (h : CHeap) (e : Code) (r : CHeap × Code),
    eval n h e = some r → eval (n + 1) h e = some r := by
  intro n
  induction n with
  | zero => intro h e r he; simp [eval] at he
  | succ n ih =>
    intro h e r he
    cases e with
    | app f x =>
      simp only [eval] at he ⊢
      cases hf : eval n h f with
      | none => simp [hf] at he
      | some p =>
        simp only [hf] at he
        rw [ih h f p hf]
        exact applyV_mono_of_eval_mono n ih p.1 p.2 x r he
    | _ => simpa only [eval] using he

/-- Monotonicity to any larger fuel. -/
theorem eval_mono_le {n m : Nat} (hnm : n ≤ m) {h : CHeap} {e : Code} {r : CHeap × Code}
    (he : eval n h e = some r) : eval m h e = some r := by
  induction hnm with
  | refl => exact he
  | step _ ih => exact eval_mono _ _ _ _ ih

end LeanStatefulAoc
