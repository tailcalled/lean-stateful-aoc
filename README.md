# lean-stateful-aoc

A realizability model with **mutable state** in which a constructive,
decidability-conditioned axiom of choice

```
AC_dec :  (Π x y : A. (x = y) + ¬ (x = y))  →  (Π x : A. ‖B x‖)  →  ‖Π x : A. B x‖
```

is realized — not as an axiom, but as an honest stateful program. The slogan,
now a theorem-shaped claim rather than a hope: *memoization is the generic
section, decidable equality is persistence of the key-partition, and the topology
was hiding in the program.*

This repository is a Lean 4 + Mathlib development of that model.

> **Status.** Design resolved; formalization not started. The central viability
> question — *does forcing the generic collapse the logic to classical?* — is
> answered **no**: the coverage is the intuitionistic Beth/open-cover coverage,
> the topos is non-Boolean, and EM *fails outright* (witness below). The
> remaining work is labor, not hazard, and concentrates in the `Soundness`
> module. See [What remains](#what-remains).

## Why the *conditional* statement

The unconditional `(Π x. ‖B x‖) → ‖Π x. B x‖` is too strong: with function
extensionality and truncation it entails excluded middle (Diaconescu). We
condition on decidable equality, which is exactly the right strength:

- **It cannot bootstrap EM.** Diaconescu chooses over `2/~ₚ` (two points glued
  iff a proposition `P` holds). To invoke `AC_dec` there you must supply
  `DecidableEq (2/~ₚ)` — but that *is* `P ∨ ¬P`. So `AC_dec` returns only the EM
  instance it was given.
- **It is genuine content.** Not provable in plain MLTT + truncation (even
  countable choice over `N` is independent).
- **The premise is the mechanism.** Decidable equality gives a *stable, persistent
  partition of keys* — exactly what a memo table needs for single-valuedness, and
  what `2/~ₚ` cannot supply without already deciding `P`.

## The construction

Realizers are **Lean values in the monotone-update monad** over the poset `P` of
forcing conditions (finite partial sections — a heap of caches, each a finite map
from keys `a : A` to realized elements of `B a`, ordered by extension):

```
T X := (c : P) → Σ (c' : P), (c ≤ c') × X        -- from condition c, possibly extend, return an X
```

Monotonicity is in the type, so "the generic filter only grows / no backtracking"
holds by construction. The choice realizer is the memoizer:

```python
def axiom_of_choice(eq, family):       # eq : DecidableEq A,  family : Π x:A. ‖B x‖
    cache = {}                         # a FRESH cell per AC_dec application
    def choice_fn(index):
        if not any(eq(index, k) for k in cache):
            cache[index] = family(index)
        return cache[lookup(eq, cache, index)]
    return choice_fn
```

`choice_fn` does not denote a total set-theoretic function (its cache is always
finite). It realizes a **forcing-name** for the generic section — and the
semantics under which that name is a genuine section is the point of the next two
sections.

## Semantics: realizability over a forcing site

A store-indexed (Kripke) relation `r ⊩_c x`, monotone in `c`, with
`e ⊩ᵀ_c x ⟺ e c = (c', _, r) ∧ c ⊑ c' ∧ r ⊩_{c'} x`, **sheafified** for a
coverage `J` on `P`.

The coverage is *not* a free parameter — it is forced by the computation model:

- **`J` = the Beth / open-cover (decision-bar) coverage.** The generating covers
  are *decision covers*: at condition `c`, cell `ℓ`, key `a` realized at `c`, the
  cover is `{ c ∪ {ℓ : a ↦ b} : b ranges over all realizers of elements of B a }`.
  Closed under pullback and transitivity, a sieve covers `c` iff it contains a
  **decision bar** — a well-founded querying strategy all of whose branches enter
  the sieve. (Verified to be a genuine Grothendieck topology.)
- This is **strictly coarser than double-negation**, hence intuitionistic. The
  `¬¬` coverage would be classical Cohen forcing (Boolean → EM); the decision-bar
  coverage is not. Localically, for `A = ℕ, B = Bool` the site is Cantor space
  `Sh(2^ℕ)`.

**The branching problem dissolves.** The bare Kripke relation failed because the
`Π`-clause demands a section uniform over *all* futures, while incomparable
extensions can commit different values at one key. In `Sh(P, J)` those extensions
are *incompatible conditions* (compatibility = syntactic agreement of stored
realizers, so no equality on `B`-values is ever needed), and the sheaf condition
never asks incompatible branches to agree. The generic is a **sheaf section**,
not a global one:

- **Totality** from density of the decision covers (relativized to conditions
  where `a` is realized — exactly the `Π`-clause's domain, so totality is not
  over-demanded).
- **Single-valuedness** from incompatibility of conflicting commits.

**The eliminator survives sheafification for free.** Local truth for `‖X‖` is "a
cover on each member of which a witness exists." Eliminating into a proposition,
the per-branch values are all the sole element of the subsingleton; propositions
are sheaves of subsingletons, so gluing is well-defined regardless of which
witness each branch produced. `elim k e := e >>= k` transports verbatim.

## Non-Booleanness (the headline theorem)

EM fails outright — stronger than merely blocking Diaconescu.

> Take cells for `A = ℕ`, `B n = Bool`, and `φ := ∃ n, s(n) = true` for the
> generic `s`. Geometrically (`Sh(2^ℕ)`), `φ = 2^ℕ ∖ {all-false}`: open, dense,
> not closed, so not complemented. Hence `cl(φ)` is everything, `¬¬φ = ⊤`
> everywhere, but `φ` misses the all-false point, so `¬¬φ ⊬ φ`. At the sieve
> level: the *always-answer-false* branch evades every decision bar, so `φ`'s
> sieve contains no bar and `φ` is not forced at the empty condition.

This survives the internal `∀A` of `AC_dec` by **value-blindness**: every
generating cover demands that a key be *committed* while admitting *every* value
as outcome — no admissible cover can constrain *which* value is committed.
Operationally this is the same fact as the firewall below.

## The Diaconescu firewall (soundness-critical invariant)

The heap must expose **exactly one** operation: eq-guarded lookup-or-commit. Any
introspection — enumerating keys, observing cache size, comparing cell identities
— lets a program observe whether two realizers routed to the same cell, deciding
element-equality, which on `2/~ₚ` decides `P` and hands EM back through the side
door. The "Lean values in a monad, no quote, no reflection" choice enforces this,
but it must be **promoted to a stated parametricity lemma** (the heap functor is
parametric in cell contents): the non-Booleanness theorem is *false* without it.
Value-blindness and this invariant are the same fact and must be proven together.

## What remains

The viability question is settled favorably; the effort relocates to formalizing
the sheaf-realizability soundness. In rough order of difficulty:

1. **The `∀A` value-blindness / firewall closure.** Argued, not formalized — that
   internal closure under all decidable-equality objects adds no covers beyond
   decision covers. This *is* the heart of the `Soundness` module.
2. **Local-equality cache indexing.** In the sheaf model `eq(a, a')` may be `inl`
   on part of a cover and `inr` on another (a section of `(=) + ¬(=)` is a
   partition of a cover). So the cache is keyed by *local* equality classes,
   coherent only because morphisms respect local equality. `Realizes` must build
   this in from the start (retrofitting is a miserable Lean refactor); expect the
   most friction here.
3. **Full-granularity non-Booleanness proof** — explicit sieve calculus and the
   bar-induction for the transitivity closure of `J`. A subtle error could still
   hide in the bar bookkeeping.

## Provisional Lean layout

1. `Computation` — the monotone-update monad; the heap of caches; allocation;
   the **parametricity (firewall) lemma**.
2. `Forcing` — the poset `P`; decision covers; the coverage `J`; the
   **non-Booleanness witness** as the headline theorem (this subsumes and
   strengthens the old `Diaconescu` plan to "EM fails," not merely "this
   construction doesn't prove EM").
3. `Realizes` — the store-indexed relation, sheafified, with **commit-time
   local-equality-class indexing** built in; clauses for `Π`, `Σ`, `=`, `‖·‖`.
4. `Soundness` — type formers and the truncation eliminator under the sheaf
   relation; the `∀A` closure. (Central effort.)
5. `Choice` — the memoizer; `AC_dec`; the theorem via totality (density) +
   single-valuedness (incompatibility).

## Lineage

The general idea (AoC as memoization) has been discovered independently by tailcalled
through meditating on why the axiom of choice is not trivially true. However, LLMs have
discovered prior literature that seems quite relevant.

The memoizer is the mutable-state form of the **Berardi–Bezem–Coquand functional**
(demand-driven memoization realizing countable choice over `ℕ`). The candidate
contribution is that *only decidable equality* of the index is used, so the
construction extends from `ℕ` to arbitrary decidable-equality objects — which need
not be projective, strictly extending the projective-choice picture of
realizability toposes (Hyland, van Oosten). The condition-threaded monad is the
intuitionistic, control-free cousin of Miquel's forcing-as-program-transformation
and Krivine's clock-realizers for DC; the coverage is Beth/open-cover
(Fourman–Scott); the scaffolding is a realizability tripos indexed over `Sh(L)`.
*(Novelty of the decidable-equality generalization is being checked against the
literature — see the open lineage question.)*

## Building

```
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` and Mathlib.
