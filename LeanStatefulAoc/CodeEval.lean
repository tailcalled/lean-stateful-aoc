import LeanStatefulAoc.Combinators

/-!
# Effectful evaluator for the realizer calculus (Layer 1, checkpoint 2)

Combinatory completeness (`Combinators.lean`) gave us *application*. Realizers also
need *state*: the memoizer commits realizers into cells. This file evaluates a
`Code` to weak-head-normal-form while threading a heap of cells, with `alloc`
creating a cell and `memo` doing lookup-or-commit.

`eval fuel h c` reduces `c` (heap `h`), returning the new heap and the
head-normal value, or `none` on fuel exhaustion. Combinator reduction (`K`, `S`)
is pure; `alloc`/`memo` are the effects.

**Equality-guarded cache.** A cell stores an *equality realizer* `eqr`; on a `memo`
lookup the cache is scanned by running `eqr · k · key` for each committed key `k`
and treating an evaluation to `tt` as "equal" (`memoScan`). This is what makes the
memoized choice function respect the object's equality `ρ_A` (two realizers of the
same element are identified by the supplied decidable-equality realizer), rather
than syntactic code identity. The verdict codes `tt`/`ff` carry the eq-guard's answer.

`eval`/`applyV`/`memoScan` are mutually recursive, terminating on `(fuel, tag, len)`
lexicographically (`tag`: eval 0, memoScan 1, applyV 2; `len` = cache length).
-/

namespace LeanStatefulAoc

/-- A cell of the realizer heap: an equality realizer `eqr` (the decidable-equality
guard used to compare keys), a family code, and a cache of committed `(key, value)`
code pairs. -/
structure CCell where
  /-- the cell's equality-guard realizer (`eqr · k₁ · k₂ ↠ tt`/`ff` decides `k₁ = k₂`) -/
  eqr : Code
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
termination_by fuel _ _ => (fuel, 0, 0)

/-- Scan a cache for a key equal to `key` under the equality guard `eqr`: run
`eqr · k · key` for each committed `(k, v)`; an evaluation to `tt` means "equal"
(return `some v`), anything else means "not this entry" (keep scanning). Effects of
the guard thread through. Returns `some (h', some v)` on a hit, `some (h', none)`
when no entry matches, `none` on fuel exhaustion. -/
def memoScan : Nat → CHeap → Code → Code → List (Code × Code) → Option (CHeap × Option Code)
  | _, h, _, _, [] => some (h, none)
  | fuel, h, eqr, key, (k, v) :: rest =>
    match eval fuel h (Code.app (Code.app eqr k) key) with
    | none => none
    | some (h', Code.tt) => some (h', some v)
    | some (h', _) => memoScan fuel h' eqr key rest
termination_by fuel _ _ _ cache => (fuel, 1, cache.length)

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
    | Code.seq => some (h, Code.app Code.seq x)
    | Code.app Code.seq e =>
      -- force `e` to a value (threading effects), then apply `x` (= the
      -- continuation `k`) to that value
      match eval fuel h e with
      | none => none
      | some (h', v) => eval fuel h' (Code.app x v)
    | Code.alloc => some (h, Code.app Code.alloc x)
    | Code.app Code.alloc eqr => some (h ++ [⟨eqr, x, []⟩], Code.loc h.length)
    | Code.memo =>
      -- force the location argument to a `loc`
      match eval fuel h x with
      | none => none
      | some (h', l) => some (h', Code.app Code.memo l)
    | Code.app Code.memo (Code.loc ℓ) =>
      -- force the key, then lookup-or-commit at cell ℓ (eq-guarded scan)
      match eval fuel h x with
      | none => none
      | some (h1, key) =>
        match h1[ℓ]? with
        | none => none
        | some cell =>
          match memoScan fuel h1 cell.eqr key cell.cache with
          | none => none
          | some (h', some v) => some (h', v)
          | some (h', none) =>
            match eval fuel h' (Code.app cell.fam key) with
            | none => none
            | some (h2, v) =>
              match h2[ℓ]? with
              | none => none
              | some cell' =>
                some (h2.set ℓ ⟨cell'.eqr, cell'.fam, (key, v) :: cell'.cache⟩, v)
    | _ => some (h, Code.app fv x)
termination_by fuel _ _ _ => (fuel, 2, 0)

end

end LeanStatefulAoc
