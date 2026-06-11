# lean-stateful-aoc

A realizability model with **mutable state** in which the constructive axiom of
choice

```
AC :  (∏ x : A. ‖B x‖)  →  ‖∏ x : A. B x‖
```

is realized — not as an axiom, but as an honest stateful program. The slogan:
*memoization turns a pointwise, realizer-dependent choice into a coherent
section, and the truncation on the codomain absorbs the order-dependence.*

This repository is a Lean 4 + Mathlib development of that model.

## The idea in one paragraph

In a pure realizability model, `AC` fails for general `A`. A realizer `f` of
`∏ x : A. ‖B x‖` is a program that, on a realizer `r` of an element `a : A`,
returns a realizer of *some* `y : B a` — but *which* `y` may depend on the
particular realizer `r`, not just on the element `a`. So there is no
well-defined section `g : ∏ x : A. B x` to truncate. Mutable state repairs this:
keep a cache indexed by the elements of `A`, and on each query either reuse the
stored answer or compute a fresh one and store it. The first realizer of `a` to
arrive commits the value; every later realizer of the same `a` is routed to that
same value. The extracted assignment is now a function of the *element*, hence a
genuine section.

```python
def axiom_of_choice(family):          # family : ∏ x:A. ‖B x‖
    cache = {}
    def choice_fn(index):             # choice_fn : ∏ x:A. B x
        if index not in cache:
            cache[index] = family(index)
        return cache[index]
    return choice_fn
```

## Why this is sound (and what it costs)

Three observations drive the model:

1. **State manufactures realizer-independence.** The obstruction to `AC` is that
   the chosen `y` depends on the realizer of `a`, not on `a` itself. Memoizing on
   the element forces all realizers of a given `a` to the same committed answer,
   which is exactly the coherence a section requires.

2. **The dictionary is where excluded middle is spent.** Implementing
   `index not in cache` requires deciding, at the realizer level, whether an
   incoming index denotes an already-seen element — i.e. a structure-respecting
   `A → A → Bool`. That is **decidable equality on `A`** (EM on `A`'s equality
   type). This cost is not optional: by Diaconescu, full `AC` *entails* EM, so EM
   is necessary for any realizer of `AC`. Here it is consumed precisely at the
   cache lookup. Decidable equality + monotone state is the matching sufficient
   condition.

3. **Truncation on the codomain makes order-dependence harmless.** `choice_fn` is
   order-sensitive: which `y` is cached for `a` depends on evaluation order and
   on what else has been queried. So it does not define a *canonical* section —
   different runs yield different sections. But the target `‖∏ x:A. B x‖` is a
   mere proposition: we owe only *a* section, never a designated one, and a
   consumer mapping into a proposition cannot distinguish two of them. The
   truncation we exploited to *hide* output values now licenses a
   history-dependent realizer.

### The crucial constraint: monotone, non-backtrackable state

The whole invariant is "a cache entry, once written, is never revised and never
lost." This holds for pure memoization (the table only grows). It **breaks** if
the ambient computation can *rewind* the store — e.g. control operators
(`call/cc`) that backtrack past a cache write, producing two different
commitments for the same `a`. So the model must use *monotone, non-revertible*
state. (This is the same care Krivine's classical realizability takes when
realizing dependent choice via a non-revertible instruction.)

## Model design

The intended construction, in layers:

- **A stateful PCA.** A partial combinatory algebra (or a typed/monadic
  equivalent) whose application threads a global store `S`. State is *monotone*:
  the store carries a partial map and updates only ever extend it; there is no
  primitive that shrinks or rewinds it.
- **Assemblies over it.** Objects are sets `|X|` with realizer sets `E_X(x)`,
  where realizers are stateful programs. Morphisms are tracked by programs that
  respect the store discipline.
- **Propositional truncation.** `‖X‖` collapses the underlying set to a point
  (when inhabited) and pools realizers: `E_‖X‖(∗) = ⋃_x E_X(x)`. Maps out of
  `‖X‖` into a proposition are forced to be constant *as values*, not as
  programs.
- **The choice combinator.** A realizer of `AC` is the memoizing program above:
  it allocates a fresh cache, and the returned `choice_fn` reads/writes it under
  decidable equality on `A`. Soundness is the proof that this program tracks an
  element of `‖∏ x:A. B x‖` whenever its input tracks an element of
  `∏ x:A. ‖B x‖`.

## Formalization plan (Lean)

Rough milestones; each should be a self-contained module under
`LeanStatefulAoc/`.

1. `PCA` — a stateful applicative structure (store + monotone update) and its
   basic combinators.
2. `Assembly` — assemblies and tracked morphisms over the stateful PCA; the
   category structure.
3. `Truncation` — propositional truncation as the realizer-pooling subsingleton,
   with its elimination principle into propositions.
4. `Choice` — the memoizing realizer; the statement of `AC` in the model and the
   soundness theorem, parameterized by `DecidableEq A`.
5. `Diaconescu` — sanity check: `AC` in the model recovers EM, confirming the EM
   cost is real and located at the dictionary.

Open design questions to pin down as we go: the exact store discipline that
rules out backtracking; whether to model state monadically or via an explicit
stateful PCA; and how much of the assembly category we actually need versus a
lighter "realizes" relation sufficient for the soundness theorem.

## Building

```
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` and Mathlib (see
`lakefile.toml`).
