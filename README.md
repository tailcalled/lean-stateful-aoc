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

> **Status.** Formalization started. The design was adversarially stress-tested
> and revised (2026-06-12); **`THEORY.md` is the authoritative formalization
> plan** — this README carries the conceptual story. Headlines of the revision:
> the central viability question — *does forcing the generic collapse the logic
> to classical?* — stays answered **no**, now with a direct, bar-free proof; the
> formalization needs **no sheaf machinery** (the Beth coverage is absorbed into
> the realizability clauses); the firewall holds **by construction** rather than
> by a parametricity lemma; and the tractable/research boundary is *data-valued
> vs function-valued `B`*. See [What remains](#what-remains).

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

Realizers are **terms of a free monad over a single heap operation**: eq-guarded
memoizing lookup, whose on-miss value is computed by the *cell's own* family
realizer, fixed at allocation. (Raw "Lean values in a monad" would not do: Lean
has no internal parametricity, and a bare function out of conditions can inspect
them — the firewall would be unprovable. A free-monad term cannot inspect or
write the heap, because no constructor lets it.) Realizer terms are interpreted
into the **monotone-update monad** over the poset `P` of forcing conditions:

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
semantics under which that name is a genuine section is the next section.

## Semantics: the ⊩-kernel

A store-indexed (Kripke) relation `r ⊩_c x`, monotone in `c`, with
`e ⊩ᵀ_c x ⟺ e c = (c', _, r) ∧ c ⊑ c' ∧ r ⊩_{c'} x`. Two design points carry
everything:

- **Conditions are semantic, typed by construction.** A condition is a finite
  partial section: per cell, a finite map from semantic elements `x : A` to
  semantic elements `y : B x`, plus the cell's label (its eq and family
  realizers). Garbage commitments are *unrepresentable*. Programs act on a
  separate **code-heap** `h`, tied to conditions by a simulation relation
  `h ~ c`.
- **Truncation is per-branch existence.** `e ⊩ᵀ_c (y ∈ X)` demands the *same*
  semantic `y` on every run-branch (every `h ~ c`); `e ⊩ᵀ_c ‖X‖` allows a
  different witness per branch (for data `X`; the truncated `Π` gets a dedicated
  *generic-section* clause, `THEORY.md` §4). That quantifier swap is the
  Beth/decision-bar coverage in disguise — **no Grothendieck topology or
  sheafification appears in the formalization**. The localic picture is
  unchanged: for `A = ℕ, B = Bool` the conceptual model is Cantor space
  `Sh(2^ℕ)`; the kernel ↔ decision-bar-site correspondence is a stated
  conjecture, not a dependency.

**The branching problem dissolves.** The bare Kripke relation failed because an
element of `B x` at `c` must be compatible across *all* futures, while
incomparable extensions can commit different values at one key. The per-branch
clauses never ask incomparable branches to agree. The generic is a name whose
value is settled branch-locally:

- **Totality**: a miss extends the condition by a typed entry computed from the
  family realizer.
- **Single-valuedness**: the condition itself fixes the semantic value of each
  entry, and eq-routed keys share their entry.

**The eliminator is not free.** For data `X`, eliminating `‖X‖` into a
proposition is unproblematic: per-branch witnesses are invisible to a
subsingleton. For `‖Π x. B x‖` — whose realizer is a *generic section*, not a
tracker of any fixed function — justifying the standard eliminator is open work
(`THEORY.md` §4, two candidate routes): the kernel theorems state `AC_dec` with
`‖·‖` read as generic-section truncation, and the eliminator belongs to the
research tier.

## Non-Booleanness (the headline theorem)

EM fails outright — stronger than merely blocking Diaconescu.

> Take a cell for `A = ℕ`, `B n = Bool` with the constant-false family, and
> `φ := ∃ n, s(n) = true` for the generic `s`. Geometrically (`Sh(2^ℕ)`),
> `φ = 2^ℕ ∖ {all-false}`: open, dense, not closed — so `¬¬φ = ⊤` everywhere,
> but `φ` misses the all-false point.

In the kernel this is a direct two-horn argument (`THEORY.md` §3) — no bars, no
sieves. A realizer of `φ ∨ ¬φ` cannot answer `inl`: the memo-only operation
never lets a program write `true` into the cache (the firewall). It cannot
answer `inr`: the *typed possibilium* `c + {m ↦ true}` is a legitimate condition
— unreachable by executing this family, but conditions are possibilia, not
execution states — and it realizes `φ` (the genericity). Meanwhile `¬¬φ` is
realized everywhere. The two horns are value-blindness, absorbed structurally:
programs cannot put values in; the semantics can imagine them in.

## The Diaconescu firewall (by construction)

The heap exposes exactly one operation: eq-guarded lookup-or-commit, with the
committed value computed by the cell's own family realizer. Clients cannot write
chosen values, enumerate keys, observe cache size, or compare cell identities —
not because a lemma forbids it, but because the realizer syntax has no
constructor that does it. What an earlier plan called "promote the firewall to a
stated parametricity lemma" is now true by construction of the operational
semantics. What is *not* yet closed is the internal `∀A` version — that no
internal decidable-equality object (e.g. `2/~ₚ`, with equality only locally
decided) smuggles in new observational power. That closure is research-tier; the
kernel theorems do not assume it.

## What remains

In order:

1. **K1 — the ⊩-kernel and non-Booleanness.** Semantic conditions, the
   simulation `h ~ c`, clauses for the needed type-shapes, and the two-horn
   theorem above. First target.
2. **K2 — `AC_dec` for data-valued `B`.** Index `A` with realized,
   condition-stable decidable equality; family and eq realizers arbitrary and
   state-entangled. Main labor: fuel/termination bookkeeping — the interpreter
   cannot be seen total by Lean, so each realizability statement carries its own
   termination witness, BBC-style.
3. **K3 — research tier.** Function-valued `B` (honest higher-order store:
   step-indexing / recursive worlds); the internal `∀A` closure with
   condition-*local* equality classes (a section of `(=) + ¬(=)` is a partition
   of a cover — the `2/~ₚ` firewall and the novelty claim live here); the
   truncation eliminator for the generic-section clause; the kernel ↔
   decision-bar-site correspondence; full soundness, upgrading "EM is not
   realized" to "a model of MLTT in which EM fails."

## Lean layout

1. `Computation` — the monotone-update monad `T` (done, with a verified
   `LawfulMonad` instance); the heap and its extension order (done; being
   reshaped per `THEORY.md` §5); the mono-sorted free monad of realizer terms
   with memo-only operation and allocation; the fuel-indexed interpreter.
2. `Realizes` — the ⊩-kernel.
3. `NonBoolean` — K1.
4. `Choice` — K2: the memoizer; `AC_dec` via totality + single-valuedness.
5. `Soundness` — K3, later.

## Lineage

The general idea (AoC as memoization) has been discovered independently by tailcalled
through meditating on why the axiom of choice is not trivially true. However, LLMs have
discovered prior literature that seems quite relevant.

The memoizer is the mutable-state form of the **Berardi–Bezem–Coquand functional**
(demand-driven memoization realizing countable choice over `ℕ`). The candidate
contribution is that *only decidable equality* of the index is used, so the
construction extends from `ℕ` to arbitrary decidable-equality objects — which need
not be projective, strictly extending the projective-choice picture of
realizability toposes (Hyland, van Oosten); note this substantive form of the
claim lives in the K3 tier, while K2's delta over BBC is chiefly the
decidable-equality-index packaging. The condition-threaded monad is the
intuitionistic, control-free cousin of Miquel's forcing-as-program-transformation
and Krivine's clock-realizers for DC; the coverage is Beth/open-cover
(Fourman–Scott); the conceptual home is a realizability tripos indexed over
`Sh(L)`, though the kernel formalization does not build one.
*(Novelty of the decidable-equality generalization is being checked against the
literature — see the open lineage question.)*

## Building

```
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` and Mathlib.
