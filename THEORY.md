# Kernel design notes (2026-06-12)

Working notes resolving the viability questions raised against the README design.
Outcome: the core claims survive, the formalization architecture changes
substantially, and the tractable/researchy boundary moves. These notes supersede
the README's *formalization plan* (not its conceptual story) until merged back.

## 1. Problems found in the README architecture

**P1 (branching, re-derived — README is right).** In a bare presheaf/Kripke model
an element of `B x` at condition `c'` is a compatible family over the whole future
cone of `c'`. Incomparable futures commit different values at a key, so no
compatible family exists; `Π x. B x` has no elements anywhere and `‖Π x. B x‖` is
empty. Local/per-branch semantics is forced. ✓ (Confirms the README's motivation
for sheafification.)

**P2 (typed-site circularity).** Conditions and decision covers are *typed*
("realizers of elements of `B a`"), but `Realizes` is defined over the site.
Naive cuts all fail:

- *Untyped covers/conditions*: a garbage commit at `(ℓ,a)` is permanent
  (monotonicity is in the type); `choice_fn a` returns it on the whole future
  cone; no alternative `Π`-witness exists at a finite condition (stripping
  `‖B x‖` pointwise is choice); so `‖Π x. B x‖` fails. Typed conditions forced.
- *Fixed point à la Knaster–Tarski*: the dependency is **antitone** — more
  realizers ⇒ wider decision branching ⇒ bars harder ⇒ fewer covers ⇒ less local
  truth. Mixed variance, no monotone fixed point.
- *Induction on condition size / reachability*: the `∀ future` quantifier in the
  `Π`/monadic clauses references larger conditions; never bottoms out.

**P3 (storage at higher type).** Cells storing realizers of function-typed `B a`
are higher-order store (state-entangled closures): condition-indexed realizability
of stored values re-creates P2 at the simulation relation. This is the classic
recursive-worlds wall; the README assumes it away ("Lean values… compatibility =
syntactic agreement" — Lean functions have no syntactic equality).

## 2. The resolution (three moves)

**M1 — semantic conditions.** A condition is a finite map of *semantic* entries
`(x : A) ↦ (y : B x)` (plus per-cell labels: the cell's eq and family realizers).
Semantic conditions are inherently typed — garbage unrepresentable by
construction; no `Realizes` needed to define them. Programs act on a separate
*code-heap* `h`, related to the condition by a simulation `h ~ c` ("each entry
`(x ↦ y)` is implemented by codes `a ⊩ x`, `b ⊩ y`").

**Watershed:** if `B x` is **data-valued** (realizers are normal forms; their
realizability is condition-free), `h ~ c` mentions only condition-free
realizability and the entire definition is well-founded by recursion on type
structure. No fixed point, no step-indexing. Function-valued `B` (storing
closures) is honest higher-order store → research land (step-indexing).
The watershed is data-valued vs function-valued `B` — *not* external vs internal
family: family and eq realizers may be arbitrary and state-entangled, since their
outputs are evaluated to normal forms at commit time.

**M2 — memo-only heap operation.** The single op is `memo ℓ a`: eq-guarded
lookup; on miss, the *cell's own* family code (fixed at allocation) computes the
value to commit. Clients cannot write values. Consequences:

- The Diaconescu firewall (no introspection, no chosen commits) holds **by
  construction** of the operational semantics — not as a parametricity lemma.
- Resolves the oracle-vs-program-commit tension: the program commits (via its
  family); *genericity* lives in the conditions (M3 below), not the run.

**M3 — truncation as per-branch existence.** Monadic realizability clauses:
`e ⊩ᵀ_c (y ∈ X)` requires the *same* semantic `y` on every evaluation branch
(every `h ~ c`); `e ⊩ᵀ_c ‖X‖` allows a different witness per branch. This
quantifier swap is the Beth coverage in disguise: **no Grothendieck topology,
sieves, or sheafification are needed in the formalization.** The topos picture
(`Sh(2^ℕ)`, decision bars) remains the conceptual story; the Lean object is a
direct monadic-Kripke logical relation ("⊩-kernel"). Conjecture (nice-to-have):
the kernel coincides with sheaf semantics over the decision-bar site on this
fragment.

*Scope correction (2026-06-13).* The per-branch-existential clause is adequate
for **data** `X` only. For `X = Π x. B x` it is wrong: "`nf ⊩ y ∈ Π`" with a
fixed total meta-function `y` is satisfied by the memoizer for **no** `y`, even
branchwise — its trace only determines a finite partial record. As literally
written here, §2's clauses would make `AC_dec` *fail*; §4's sketch tacitly used
a different reading. `‖Π x. B x‖` therefore gets a dedicated **generic-section
clause**, defined at the head of §4, and the eliminator caveat there applies.

## 3. Headline theorem, bar-free (EM not realized; ¬¬φ realized)

Cell `ℓ` with constant-false family `f₀ = λn. pure ff` (a legitimate realizer of
`Π n. ‖Bool‖`); condition `c₀` = `ℓ` allocated, empty; `s := choice_fn_ℓ`;
`φ := ∃n. s n = true`. Suppose `e ⊩_{c₀} φ ∨ ¬φ`.

- **inl:** all values `e` can cause to be stored at `ℓ` are `f₀`-outputs = `ff`
  (memo-only: `e` cannot write `tt`). No producible witness. Contradiction.
- **inr:** `w ⊩_{c'} ¬φ` demands no future of `c'` realizes `φ`. But
  `c'' := c' + (ℓ : m ↦ true)`, `m` fresh, is a *typed* condition (`true ∈ Bool`)
  — unreachable by running `f₀`, but conditions are possibilia, not execution
  states. At `c''`, `s m` cache-hits `tt`; `φ` realized. Contradiction.

`¬¬φ` *is* realized at `c₀`: every `c'` has the `(m ↦ true)` extension, so no
`c'` realizes `¬φ`. Hence `¬¬φ ⊬ φ`: non-Boolean.

The two horns use the dual pair — programs **can't write values in** (firewall,
by construction), the semantics **can imagine values in** (genericity, typed
possibilia). That pair *is* value-blindness, absorbed structurally; no separate
parametricity lemma is needed for this theorem.

## 4. AC_dec sketch under the kernel clauses

**The conclusion's clause (generic-section truncation).** K2's theorem is stated
with: `v ⊩_c ‖Π x:A. B x‖` iff for all `c' ≥ c`, all `a ⊩ x ∈ A`, and all
`h ~ c'`, `run (v a) h` terminates as `(h', b)` with `h' ~ c'' ≥ c'` and
`b ⊩ y ∈ B x` for *some* `y` — **behaviorally single-valued**: any subsequent
query at any `a' ⊩ x` (same `x`), from any later heap, yields a value realizing
the *same* `y`. Sanity: genuine Π-realizers satisfy it (intro holds); it cannot
imply untruncated-Π realizability (else Diaconescu → EM, contradicting §3).

Realizer: given eq-realizer `e_A` and family `f`, allocate `ℓ` labeled `(e_A, f)`,
return `choice_fn := λa. memo ℓ a`.

- **Hit:** the entry's semantic `y` is fixed *by the condition*; eq-routed keys
  (`a ~ a'`, both realizing `x`) share the entry, hence the `y` —
  single-valuedness/extensionality. Stored normal forms realize condition-freely,
  so reads need no persistence transport.
- **Miss:** run `f a` ⇝ per-branch witness `y₁` with normal form `b₁ ⊩ y₁ ∈ B x`;
  commit; condition extends by the typed entry `(x ↦ y₁)` — totality.
- **Adversarial entries** (typed but family-inconsistent) are harmless for `Π`:
  any stored value realizes *some* element of `B x`, which is all `Π` asks. They
  bite only `φ`-like statements — where they are the genericity (see §3).
- **Scope of M2-kernel:** index `A` with *realized, condition-stable* deceq
  (data-like `A`, PER-classes as semantic elements via `Quotient`); condition-
  *local* equality partitions (internal `2/~ₚ`-style deceq) are out of kernel
  scope → research tier.

**Eliminator caveat (found 2026-06-13).** `elim k e := e >>= k` does **not**
transport verbatim under the generic-section clause: `k`'s hypothesis quantifies
over codes realizing *untruncated* `Π` (trackers of a fixed semantic function),
and `choice_fn` is not one, so feeding it to `k` is unjustified as-is. Repair
routes, both K3: **(i)** prop-elimination only, via an operational adequacy
argument — `k`'s run sees only a finite trace of answers; any genuine realizer
agreeing on that trace (one exists meta-classically when each queried `B x` is
semantically inhabited) drives `k` to the same result, and a proposition's
realizability is value-irrelevant; **(ii)** give untruncated `Π` Beth-section
elements (condition-indexed, locally-total assignments), re-importing sheaf-like
sections exactly where the conceptual story says they live. Until one is carried
out, K2 is to be advertised as: *the memoizer realizes `AC_dec` with `‖·‖` read
as generic-section truncation*. (Consequence: "no sheaf machinery" holds for
K1 and K2-as-stated; full type-theoretic soundness likely brings sections back.)

## 5. Architecture changes for `Computation.lean`

Supersedes parts of the current file:

- `F V` **mono-sorted** (results are codes `V`): fixes the nested-positivity
  failure for effectful guards; fields `(V → F V)` etc. are strictly positive and
  uniform.
- Ops: `memo : Loc → V → (V → F V) → F V` style (continuation), `alloc` carrying
  shallow eq/family fields `(V → V → F V)`, `(V → F V)`. **No client commit; no
  oracle.** Higher-type realizers are shallow Lean functions (`V → F V`, …),
  never stored; only data normal forms are stored ⇒ **no PCA, no Part**.
- `run` becomes **fuel-indexed**: memo-miss runs arbitrary family code; Lean
  cannot see termination. Each realizer's ⊩-statement carries its own
  termination (∃ fuel), BBC-style. (Loc-allocation order makes memo recursion
  well-founded semantically; fuel is the formal vehicle.)
- `Heap` reshaped: a **grow-only `List (Cell V)`** with `Loc` = stable index
  (improves on the earlier `Finmap Loc CellState` plan: allocation is append,
  freshness is free, and no `DecidableEq V` is needed anywhere — the eq
  realizer does all key routing). `Cell` = label (eq/family fields) × cache
  (newest-first entry list); cell extension = same label + cache suffix order.
  `T` and the extension `PartialOrder` survive; `run` lands in the *partial*
  monotone-update monad `PT` (fuel exhaustion / stuck op return `none`, with
  no condition extension).
- `Realizes` (new module): conditions = semantic typed finite sections; clauses
  per type-shape needed for the two theorems only (Π over `A`, data `B`, `‖·‖`
  with the §4 generic-section clause for `‖Π‖`, `∨`, `=`, `¬`) — a **⊩-kernel**,
  not full MLTT soundness. The Soundness module (every rule realized; internal
  `∀A` closure) comes later and is where the remaining research risk lives.
- A named structural lemma **memo-discipline** (condition-blindness / frame):
  `run` interacts with a cell only through `memo`, at `Loc`s occurring in the
  term or labels reachable from it — by induction on `F`-syntax/fuel. Horn `inl`
  of §3 and the K2 proof both consume it; K1 should state and use it explicitly.

## 6. Revised milestones

- **K1**: the §3 theorems. **DONE 2026-06-13** (`NonBoolean.lean`):
  `em_not_realized`, `notNot_phi_forced`, `dne_not_realized`, via the
  memo-discipline invariant `Protected` + `protected_run`.

  *Correction (same day, prompted by the user asking whether this shows a
  topos is non-Boolean).* The first version forced over **raw heaps**, and
  that relation is **not persistent**: `Cell.Le` admits duplicate-key
  extensions, and the newest-first scan lets them shadow older values, so
  `ForcesPhi h` can fail at an extension of `h`. The realizer-level theorems
  are unaffected, but the forcing reading demands **single-valued conditions**
  (pairwise-distinct keys) — precisely §2's semantic-conditions discipline,
  which the raw-heap shortcut had dropped. With the poset `Cond` of
  single-valued conditions above `h₀`: persistence of `φ` holds
  (`forcesPhi_persists`), density needs a *fresh* key (`kPhi_dense`; the
  earlier shadowing trick was exploiting the broken order), and
  **`kripke_not_boolean`** exhibits the operational `φ` as a monotone
  proposition with `¬φ = ⊥`, `¬¬φ = ⊤`, `φ ≠ ⊤` in the Kripke algebra `KProp`
  of monotone propositions over `Cond`. That algebra is the truth-value
  algebra of the presheaf topos over `Cond`; the formal identification with
  `Psh(Cond)` (and the sheaf topos for the decision coverage) remains K3.
  Scope note: "EM fails in *the* model validating `AC_dec`" still requires
  K2+K3 — K1's topos-facing claim is about the presheaf algebra over this
  condition poset.
- **K2 increments 1 & 2: DONE 2026-06-13** (`Choice.lean`). Increment 1 was
  the `A = ℕ` / code-equality version; it has been *subsumed* by increment 2's
  abstract `AcCell A B` (the `ℕ` case is recovered as `natCell`). The capstone
  is **`AcCell.acDec_realized`** (`#print axioms`: only `propext`,
  `Classical.choice`, `Quot.sound` — no `sorry`): from any heap the `AC_dec`
  program `acDecProg` (allocate the cell, return its `Loc`) succeeds in one
  step and establishes `C.ValidAt`, over which the staged `memoizer ℓ` is a
  `GenericSection` — `AcCell.total` (totality + typing; miss path runs the
  cell's own family, composed at a common fuel via `run_fuel_mono`),
  `AcCell.hit`/`AcCell.stable` (effect-free hits persistent across valid
  extensions = behavioral single-valuedness; with `rel` functional, semantic
  single-valuedness). See §7 for the deceq modeling and its honest caveats.
- **K3 (research)**: function-valued `B` (step-indexing / recursive worlds);
  internal `∀A` with condition-local equality partitions (the `2/~ₚ` firewall
  and the novelty claim live here); the truncation eliminator for the
  generic-section clause (routes (i)/(ii) of §4); kernel ↔ decision-bar-site
  correspondence; full Soundness.

## 7. K2 increment 1: the precise statement (2026-06-13)

Scope: index `A = ℕ`, pure code-equality eq; the deceq-`A` generalization is
increment 2. Design decisions, each load-bearing:

- **Codes**: reuse `V₀`. `B`-realizers are arbitrary `V₀`-codes via an
  abstract `rel : (n : ℕ) → V₀ → B n → Prop` — data-ness (condition-freeness)
  is structural in `rel`'s *type*, and countable data codes into `ℕ` in the
  classical realizability tradition. Require `rel` **functional** (a code
  denotes at most one value); with that, semantic single-valuedness reduces to
  cache determinism.
- **Conditions**: `ValidAt rel f ℓ h` — cell `ℓ` exists with label
  `(eqCode, f)`, pairwise-distinct keys, and every entry `(k, b)` typed:
  `k = nat n` and `rel n b y` for some `n, y`. This is §2's semantic
  conditions specialized to this cell; the heap *is* the condition, the
  semantic content is carried by the typing clause. (K1's persistence lesson:
  distinct keys are non-negotiable.)
- **Family premise** (the `‖B n‖`-clause, per-branch existential over the
  valid cone): for every `ValidAt` heap `h` and every `n`, `run (f (nat n)) h`
  terminates, preserves `ValidAt`, and its value `rel`-realizes some
  `y : B n`.
- **Frame premise**: runs of `f` leave cell `ℓ` untouched
  (`s.next[ℓ]? = h[ℓ]?`). Justified by alloc-order acyclicity (`f` was
  written before `ℓ` existed). Without it, `f` could insert the key between
  the memoizer's scan-miss and its commit, breaking single-valuedness.
  *Formalization note (2026-06-13):* in the shallow embedding this premise
  cannot be discharged generically — `f` is an arbitrary Lean function and
  `ℓ : ℕ` is just a number, so "`f`'s code does not mention `ℓ`" is not
  expressible. It is discharged per-realizer (for concrete `f`, by induction
  on the `F`-terms it produces). A generic discharge would need realizers as
  syntax — a K3/deep-embedding consideration.
- **Premise simplification found in Lean**: the family premise needs *no*
  validity-preservation clause — increment-1 conditions constrain only cell
  `ℓ`, which the frame premise says `f` never touches, so preservation is
  automatic. (Multi-cell conditions in the full `Realizes` module will bring
  the preservation clause back.)
- **Conclusion** (the generic-section clause of §4, instantiated):
  *totality+typing* — from every valid `h`, `memoizer ℓ (nat n)` terminates in
  a valid heap with a value `b` such that `rel n b y` and `(nat n, b)` is in
  the cache; *stability* — if `(nat n, b)` is cached, the memoizer returns `b`
  **without extending the heap** (pure eq ⇒ hits are effect-free);
  *single-valuedness* — across queries, by cache membership + distinctness +
  functionality of `rel`.
- **Staging**: the theorem is stated at a fixed `ℓ` under `ValidAt`; a
  corollary connects the actual `AC_dec` program `F.alloc eqCode f k` — the
  post-alloc state satisfies `ValidAt` with empty cache. No Loc-codes in `V`
  needed.
- **New infrastructure needed**: `run_fuel_mono` (success is preserved by more
  fuel; needed to compose the memoizer's run with `f`'s run at a common fuel).

Increment 2 (DONE): the abstract index. Bundled as `AcCell A B`:
`KeyRel : V₀ → A → Prop` (which codes realize which indices — *many codes per
index*), a pure eq-code `eqb : V₀ → V₀ → Bool`, `rel : (x:A) → V₀ → B x → Prop`,
the family `fam`, and the soundness law
`sound : KeyRel k x → KeyRel k' x' → (eqb k k' = true ↔ x = x')`. This is the
realizability reading of the `AC_dec` premise `Π x y. (x=y)+¬(x=y)`: the
eq-code *decides* index equality on realizing codes. Conditions
(`AcCell.ValidAt`) are single-valued **on indices** (`Pairwise eqb _ _ = false`,
not code-distinctness), and the hit lemma routes any query code `a` with
`KeyRel a x` to the entry stored under any `k` with `KeyRel k x` — distinct
codes for the same index collapse to one cache slot. That collapse *is* "deceq
= persistence of the key-partition". The `ℕ` instance is `natCell`.

Honest caveats on the increment-2 model (do not overstate):
1. `eqb` is **pure and total** — not a state-entangled realizer of
   `(x=y)+¬(x=y)`. A fully internal eq-realizer (effectful, fuel-bearing, only
   *locally* decidable) is the `2/~ₚ` firewall territory of K3; `sound` is a
   meta-level (Lean `Prop`) law, so this models *given* decidable equality, not
   an arbitrary internal one.
2. `KeyRel`, `rel` are abstract `Prop`s assumed condition-free — faithful to
   "data-valued", but it is an assumption on the instance, discharged only when
   a concrete `V₀`-realizability relation is plugged in (the eventual
   `Realizes` module).
3. The **frame premise** is still assumed (see below) and the family premise
   carries no validity-preservation clause (single-cell justification).

Increment 3 / `Realizes` integration: discharge the frame premise via the
general frame lemma; multi-cell conditions reinstate validity-preservation;
internalize `eqb` as an effectful local-equality realizer (K3).

## 8. The Diaconescu firewall (2026-06-13, `Firewall.lean`)

The slogan "`AC_dec` cannot bootstrap EM" made precise in the project's terms.

**Setup.** `Glue P` = `2/~ₚ` = `Quotient` of `Bool` by `a ~ b := a = b ∨ P`.
Its decidable equality *is* the excluded middle: `mk true = mk false ↔ P`
(`mk_true_eq_mk_false_iff`), hence `DecidableEq (Glue P) ↔ Decidable P` (both
directions formalized).

**The firewall** (`acCell_glue_firewall`): for any `AcCell (Glue P) B` and key
codes `k₀, k₁` realizing the two points, `P ∨ ¬P`. The proof decides `P` using
the *actual boolean* `C.eqb k₀ k₁`, tied to index equality by `C.sound`.
Decisive sanity check: `#print axioms` gives `[propext, Quot.sound]` —
**no `Classical.choice`**. A constructive proof of `P ∨ ¬P` means the EM flows
genuinely from the hypothesis; the cell cannot be built without it. So `AC_dec`
over `Glue P` *consumes* the excluded middle it is handed and produces nothing
new. The memoizer adds zero leakage because `F` exposes no introspection (no
key-enumeration / cache-size / cell-identity op) — routing a query is the only
interaction, and routing is an eq-call, which `sound` ties to index equality.

**What this settles, and what it does NOT.** It settles the firewall for the
**global, pure** eq-code `AcCell` currently carries: constructing the cell
forces `eqb` to *globally* decide `P`. The genuinely hard frontier is the
**effectful, only-locally-decidable** eq realizer
`eqr : V₀ → V₀ → F V₀` that refines the condition to decide equality on a
*cover* (a section of `(=) + ¬(=)` = a partition of a cover) without ever
deciding `P` globally. Two open questions there:

1. *Does the memoizer even work with local eq?* Running `eqr` to route now
   extends the condition (commits to a cover branch), so hits are no longer
   effect-free; single-valuedness must survive the condition refinement, and
   the cache must be keyed by *local* equality classes (README item 2). This is
   `Realizes`-module machinery: generalize `AcCell.eqr` to effectful, restate
   `sound` operationally (`run (eqr a k) h` terminates with a Bool, extends `h`
   validity-preservingly, persistently), re-prove `total`/`hit`/`stable` with
   "hit may extend the heap" — `scan` already threads the effects, but the
   pure-eq lemmas `scan_ret_skip`/`scan_ret_hit` must be replaced by their
   effectful analogues.
2. *Does local eq still firewall?* The present proof needs `eqb k₀ k₁` to be a
   *global* boolean. With local eq there is no such global boolean — `eqr` may
   answer `inl` on one cover branch and `inr` on another, precisely *not*
   deciding `P`. The conjecture (firewall still holds) becomes: any boolean a
   program can extract via the memoizer is one the local eq already forces on
   some cover — an observational/`⊩`-level statement, the honest heart of the
   `∀A` value-blindness closure. **Open.**

**Course-correction (2026-06-13), worked out while attempting the effectful
machinery — `effectful_glue_firewall`.** Replacing pure `eqb` by an effectful
`eqr : V₀ → V₀ → F V₀` does *not*, by itself, reach the open frontier. `run` is
**deterministic**: from any fixed heap `h`, `run (eqr k₀ k₁) h` yields at most
one verdict, and if that verdict is *sound* (which the memoizer needs anyway,
for single-valued routing) it is a definite boolean that decides `P`. Formalized
and `Classical.choice`-free. Consequence for the project's plan:

- The escape is **not** "effects". `eqr` reading/extending the heap changes
  nothing — a single run still commits to one answer. The escape is genuine
  **non-determinism across cover branches**: `eqr` answering `true` on the
  branch where `P` and `false` on the branch where `¬P`, deciding `P` on
  *neither*. A single deterministic `run` cannot express this; it follows one
  branch. So **the local-eq firewall is a `⊩`-level (per-branch) statement, not
  an operational one** — building a heavier effectful `AcCell` with
  operationally-sound-from-root `eqr` would still be inside the global case and
  would still satisfy `acCell_glue_firewall`'s hypothesis shape.
- Therefore the productive next step is **not** more effectful eq machinery in
  `Computation`/`Choice`; it is the **`⊩`-semantics layer** (§5's `Realizes`
  module): define `e ⊩ᵀ_c X` quantifying over the cover branches / oracles, lift
  the memoizer's single-run results to it, and *there* state and attack the
  local-eq firewall as value-blindness over branches. The effectful
  generalization of `AcCell.eqr` becomes worthwhile only once eq must answer
  branch-locally, i.e. inside that `⊩` layer — not before.

Caveat on claims: K1/K2 deliver "EM is not realized" and "AC_dec is realized" at
the ⊩-level; the stronger "a topos/model of MLTT where EM fails and AC_dec holds"
needs Soundness (K3). The firewall result (§8) covers the global/pure eq case;
the local/effectful eq firewall — the actual `2/~ₚ` subtlety and the genuine
novelty frontier — is open. The literature/novelty check (BBC, Berger–Oliva, …)
matters chiefly here; K2's delta over BBC is the deceq-index packaging.
