import LeanStatefulAoc.Topos
import LeanStatefulAoc.Memo

/-!
# Heap monotonicity of the evaluator

The model's whole point is *monotone* mutable state: evaluation only ever grows the heap
(`alloc` appends a fresh cell, `memo` commits prepend to a cache, existing cells keep their
family). This file proves that operationally: every successful `eval`/`applyV` run leaves a
heap `h'` with `HLe h h'`.

This is the operational core that lets a realizer of a Kripke-monotone proposition survive
the side effects of an *earlier* sub-computation — exactly what `EProp.and_intro` (run `r₁`,
then `r₂` on the *same* realizer at the grown heap) and the whole topos layer need.

Proof shape mirrors `EvalMono.applyV_mono_of_eval_mono`: the 15-arm `applyV` case analysis is
factored into `applyV_hmono_of_eval_hmono`, parametric in `eval`-heap-monotonicity at the same
fuel; `eval_hmono` is then a one-line fuel induction feeding itself in. Pure/value arms give
`HLe.refl`; `alloc` gives `HLe.alloc`; `memo` commits give `HLe.commit`; eval arms chain via
`HLe.trans`.
-/

namespace LeanStatefulAoc

open Code

/-- The `applyV` half of heap monotonicity, assuming the `eval` half at fuel `n`. -/
theorem applyV_hmono_of_eval_hmono (n : Nat)
    (hev : ∀ h e h' v, eval n h e = some (h', v) → HLe h h') :
    ∀ h fv x h' v, applyV n h fv x = some (h', v) → HLe h h' := by
  intro h fv x h' v hx
  -- value arms: result heap is the input heap
  cases fv <;>
    try (simp only [applyV, Option.some.injEq, Prod.mk.injEq] at hx;
         obtain ⟨rfl, _⟩ := hx; exact HLe.refl h)
  case fst =>
    simp only [applyV] at hx
    cases hxe : eval n h x with
    | none => simp [hxe] at hx
    | some p =>
      obtain ⟨hh, val⟩ := p
      have hle := hev h x hh val hxe
      simp only [hxe] at hx
      split at hx
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at hx heq
        obtain ⟨rfl, _⟩ := hx; obtain ⟨rfl, _⟩ := heq; exact hle
      · simp at hx
  case snd =>
    simp only [applyV] at hx
    cases hxe : eval n h x with
    | none => simp [hxe] at hx
    | some p =>
      obtain ⟨hh, val⟩ := p
      have hle := hev h x hh val hxe
      simp only [hxe] at hx
      split at hx
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at hx heq
        obtain ⟨rfl, _⟩ := hx; obtain ⟨rfl, _⟩ := heq; exact hle
      · simp at hx
  case memo =>
    simp only [applyV] at hx
    cases hxe : eval n h x with
    | none => simp [hxe] at hx
    | some p =>
      obtain ⟨hh, l⟩ := p
      have hle := hev h x hh l hxe
      simp only [hxe, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, _⟩ := hx; exact hle
  case app f y =>
    cases f <;>
      try (simp only [applyV, Option.some.injEq, Prod.mk.injEq] at hx;
           obtain ⟨rfl, _⟩ := hx; exact HLe.refl h)
    case K =>
      simp only [applyV] at hx
      exact hev h y h' v hx
    case alloc =>
      simp only [applyV] at hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, _⟩ := hx; exact HLe.alloc h _
    case seq =>
      simp only [applyV] at hx
      cases hy : eval n h y with
      | none => rw [hy] at hx; simp at hx
      | some p =>
        obtain ⟨h1, w⟩ := p
        have hle1 := hev h y h1 w hy
        rw [hy] at hx
        exact HLe.trans hle1 (hev h1 (Code.app x w) h' v hx)
    case memo =>
      cases y <;>
        try (simp only [applyV, Option.some.injEq, Prod.mk.injEq] at hx;
             obtain ⟨rfl, _⟩ := hx; exact HLe.refl h)
      case loc ℓ =>
        simp only [applyV] at hx
        cases hxe : eval n h x with
        | none => simp [hxe] at hx
        | some p =>
          obtain ⟨h1, key⟩ := p
          have hle1 := hev h x h1 key hxe
          simp only [hxe] at hx
          cases hc : h1[ℓ]? with
          | none => simp [hc] at hx
          | some cell =>
            simp only [hc] at hx
            cases hf : cell.cache.find? (fun p => decide (p.1 = key)) with
            | some pr =>
              simp only [hf, Option.some.injEq, Prod.mk.injEq] at hx
              obtain ⟨rfl, _⟩ := hx; exact hle1
            | none =>
              simp only [hf] at hx
              cases hfam : eval n h1 (Code.app cell.fam key) with
              | none => simp [hfam] at hx
              | some p2 =>
                obtain ⟨h2, w⟩ := p2
                have hle2 := hev h1 (Code.app cell.fam key) h2 w hfam
                simp only [hfam] at hx
                cases hc2 : h2[ℓ]? with
                | none => simp [hc2] at hx
                | some cell' =>
                  simp only [hc2, Option.some.injEq, Prod.mk.injEq] at hx
                  obtain ⟨rfl, _⟩ := hx
                  exact HLe.trans hle1 (HLe.trans hle2 (HLe.commit h2 ℓ cell' (key, w) hc2))
    case app g z =>
      cases g <;>
        try (simp only [applyV, Option.some.injEq, Prod.mk.injEq] at hx;
             obtain ⟨rfl, _⟩ := hx; exact HLe.refl h)
      case S =>
        simp only [applyV] at hx
        exact hev h _ h' v hx
      case case =>
        simp only [applyV] at hx
        cases hxe : eval n h x with
        | none => simp [hxe] at hx
        | some p =>
          obtain ⟨hh, val⟩ := p
          have hle := hev h x hh val hxe
          simp only [hxe] at hx
          split at hx
          · rename_i heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, _⟩ := heq
            exact HLe.trans hle (hev _ _ h' v hx)
          · rename_i heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, _⟩ := heq
            exact HLe.trans hle (hev _ _ h' v hx)
          · simp at hx

/-- **Heap monotonicity of `eval`**: a successful run only grows the heap. -/
theorem eval_hmono : ∀ (n : Nat) (h : CHeap) (e : Code) (h' : CHeap) (v : Code),
    eval n h e = some (h', v) → HLe h h' := by
  intro n
  induction n with
  | zero => intro h e h' v he; simp [eval] at he
  | succ n ih =>
    intro h e h' v he
    cases e with
    | app f x =>
      simp only [eval] at he
      cases hf : eval n h f with
      | none => rw [hf] at he; simp at he
      | some p =>
        obtain ⟨h1, fv⟩ := p
        rw [hf] at he
        exact HLe.trans (ih h f h1 fv hf) (applyV_hmono_of_eval_hmono n (ih) h1 fv x h' v he)
    | _ =>
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, _⟩ := he; exact HLe.refl h

/-- `Evaluates` form: the heap a computation reaches extends the heap it started from. -/
theorem Evaluates.hle {h h' : CHeap} {e v : Code} (he : Evaluates h e h' v) : HLe h h' := by
  obtain ⟨n, hn⟩ := he
  exact eval_hmono n h e h' v hn

end LeanStatefulAoc
