import LeanStatefulAoc.Combinators

/-!
# Effectful evaluator for the realizer calculus (Layer 1, checkpoint 2)

Combinatory completeness (`Combinators.lean`) gave us *application*. Realizers also
need *state*: the memoizer commits realizers into cells. This file evaluates a
`Code` to weak-head-normal-form while threading a heap of cells, with `alloc`
creating a cell and `memo` doing lookup-or-commit.

`eval fuel h c` reduces `c` (heap `h`), returning the new heap and the
head-normal value, or `none` on fuel exhaustion. Combinator reduction (`K`, `S`)
is pure; `alloc`/`memo` are the effects. For the first (projective-index) target
the cache is keyed by **code identity** — distinct keys are distinct codes — so
the scan is a pure lookup; the general effectful eq-guard is layered on later.

`eval` and `applyV` are mutually recursive, terminating on `(fuel, tag)`
lexicographically (every step strictly decreases it).
-/

namespace LeanStatefulAoc

/-- A cell of the realizer heap: a family code and a cache of committed
`(key, value)` code pairs. -/
structure CCell where
  /-- the cell's family code (run on a miss) -/
  fam : Code
  /-- committed `(key, value)` pairs, newest first -/
  cache : List (Code × Code)

/-- The realizer heap: a grow-only list of cells (`loc` = index). -/
abbrev CHeap := List CCell

mutual

/-- Reduce a code to weak-head-normal-form, threading the heap. -/
def eval : Nat → CHeap → Code → Option (CHeap × Code)
  | 0, _, _ => none
  | fuel + 1, h, Code.app f x =>
    match eval fuel h f with
    | none => none
    | some (h1, fv) => applyV fuel h1 fv x
  | _ + 1, h, c => some (h, c)
termination_by fuel _ _ => (fuel, 0)

/-- Apply a head-normal value `fv` to an argument `x`, performing effects. -/
def applyV : Nat → CHeap → Code → Code → Option (CHeap × Code)
  | fuel, h, fv, x =>
    match fv with
    | Code.K => some (h, Code.app Code.K x)
    | Code.app Code.K a => eval fuel h a
    | Code.S => some (h, Code.app Code.S x)
    | Code.app Code.S a => some (h, Code.app (Code.app Code.S a) x)
    | Code.app (Code.app Code.S a) b =>
      eval fuel h (Code.app (Code.app a x) (Code.app b x))
    | Code.fst =>
      match eval fuel h x with
      | some (h', Code.app (Code.app Code.pr a) _) => some (h', a)
      | _ => none
    | Code.snd =>
      match eval fuel h x with
      | some (h', Code.app (Code.app Code.pr _) b) => some (h', b)
      | _ => none
    | Code.app (Code.app Code.case f) g =>
      match eval fuel h x with
      | some (h', Code.app Code.inl a) => eval fuel h' (Code.app f a)
      | some (h', Code.app Code.inr b) => eval fuel h' (Code.app g b)
      | _ => none
    | Code.alloc => some (h, Code.app Code.alloc x)
    | Code.app Code.alloc _ => some (h ++ [⟨x, []⟩], Code.loc h.length)
    | Code.memo =>
      -- force the location argument to a `loc`
      match eval fuel h x with
      | none => none
      | some (h', l) => some (h', Code.app Code.memo l)
    | Code.app Code.memo (Code.loc ℓ) =>
      -- force the key, then lookup-or-commit at cell ℓ
      match eval fuel h x with
      | none => none
      | some (h1, key) =>
        match h1[ℓ]? with
        | none => none
        | some cell =>
          match cell.cache.find? (fun p => decide (p.1 = key)) with
          | some p => some (h1, p.2)
          | none =>
            match eval fuel h1 (Code.app cell.fam key) with
            | none => none
            | some (h2, v) =>
              match h2[ℓ]? with
              | none => none
              | some cell' => some (h2.set ℓ ⟨cell'.fam, (key, v) :: cell'.cache⟩, v)
    | _ => some (h, Code.app fv x)
termination_by fuel _ _ _ => (fuel, 1)

end

end LeanStatefulAoc
