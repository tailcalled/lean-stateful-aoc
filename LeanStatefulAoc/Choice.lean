import LeanStatefulAoc.NonBoolean

/-!
# Choice: the memoizer realizes `AC_dec` (K2)

K2 increment 2 (`THEORY.md` §7): an abstract index type `A` with **realized
decidable equality** — the cell's eq-code decides a PER on key codes (distinct
codes may realize the same index; eq-routing collapses them, which is exactly
"decidable equality is persistence of the key-partition"). Values live in an
abstract data family `B : A → Type` realized by a condition-free
`rel : (x : A) → V₀ → B x → Prop`; data-ness is structural in `rel`'s type.

The data of one `AC_dec` application is bundled as `AcCell`. Over its valid
conditions (`AcCell.ValidAt`) the memoizer satisfies the generic-section
clause: **totality + typing** (`AcCell.total` — the miss path runs the cell's
own family and commits at the queried key code), **stability**
(`AcCell.hit_run`, `AcCell.stable` — hits are effect-free and persist across
valid extensions; with `rel` functional this is semantic single-valuedness),
and **staging** (`AcCell.validAt_alloc`, `AcCell.acDec_realized` — the
`AC_dec` program allocates the cell and returns its location).

The increment-1 instance (`A = ℕ`, code equality) is `natCell` at the end.
-/

namespace LeanStatefulAoc

universe u v

variable {A : Type u} {B : A → Type v}

/-- The data of one `AC_dec` application: how key codes realize indices, the
pure eq-code, how value codes realize family members, and the family realizer.
`sound` says the eq-code *realizes decidable equality of `A`*: on realizing
codes it answers `true` exactly on equal indices. It is a decidable PER on
codes — distinct codes may realize the same index. -/
structure AcCell (A : Type u) (B : A → Type v) : Type (max u v) where
  /-- key codes realizing indices -/
  KeyRel : V₀ → A → Prop
  /-- the pure eq-code -/
  eqb : V₀ → V₀ → Bool
  /-- value codes realizing family members -/
  rel : (x : A) → V₀ → B x → Prop
  /-- the family realizer (of `Π x. ‖B x‖`) -/
  fam : V₀ → F V₀
  /-- the eq-code realizes decidable equality of the index -/
  sound : ∀ {k : V₀} {x : A} {k' : V₀} {x' : A},
    KeyRel k x → KeyRel k' x' → (eqb k k' = true ↔ x = x')

namespace AcCell

variable (C : AcCell A B)

/-- The cell's eq realizer: the eq-code, packaged as a (pure) program. -/
abbrev eqr : V₀ → V₀ → F V₀ := fun a k => F.ret (.bool (C.eqb a k))

/-- The `AC_dec` program: allocate a cell owning the eq and family realizers,
return its location as a numeral code. The staged choice function is
`memoizer ℓ`. -/
def acDecProg : F V₀ := F.alloc C.eqr C.fam fun ℓ => F.ret (V₀.nat ℓ)

/-- Valid conditions for the cell at `ℓ`: it exists, owns the label, its keys
are pairwise eqb-inequivalent (the condition is a finite partial function on
*indices*, not codes), and every entry realizes: key code realizes an index,
value code realizes a member of the family there. -/
def ValidAt (ℓ : Loc) (h : Heap V₀) : Prop :=
  ∃ cell, h[ℓ]? = some cell ∧ cell.eqr = C.eqr ∧ cell.fam = C.fam ∧
    (cell.cache.Pairwise fun p q => C.eqb p.1 q.1 = false) ∧
    ∀ p ∈ cell.cache, ∃ x y, C.KeyRel p.1 x ∧ C.rel x p.2 y

variable {C}

/-- The eq-code is reflexive on realizing codes. -/
theorem eqb_self {k : V₀} {x : A} (hk : C.KeyRel k x) : C.eqb k k = true :=
  (C.sound hk hk).mpr rfl

/-- A code realizes at most one index. -/
theorem keyRel_fn {k : V₀} {x x' : A} (h1 : C.KeyRel k x) (h2 : C.KeyRel k x') :
    x = x' :=
  (C.sound h1 h2).mp (eqb_self h1)

/-- A cache hit, run-level: if some entry's key realizes the queried index,
the memoizer returns that entry's value and leaves the heap unchanged. The
query code `a` need not be the stored code `k` — eq-routing collapses the
PER. -/
theorem hit_run {ℓ : Loc} {h : Heap V₀} {cell : Cell V₀} {a k b : V₀} {x : A}
    (hcell : h[ℓ]? = some cell) (heqr : cell.eqr = C.eqr)
    (hkd : cell.cache.Pairwise fun p q => C.eqb p.1 q.1 = false)
    (htyped : ∀ p ∈ cell.cache, ∃ x y, C.KeyRel p.1 x ∧ C.rel x p.2 y)
    (hKa : C.KeyRel a x) (hKk : C.KeyRel k x) (hmem : (k, b) ∈ cell.cache) :
    run isTrue₀ 2 (memoizer ℓ a) h = some ⟨h, le_refl h, b⟩ := by
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hmem
  have hno : ∀ p ∈ l₁, isTrue₀ (V₀.bool (C.eqb a p.1)) = false := by
    intro p hp
    obtain ⟨x', y', hKp, -⟩ :=
      htyped p (by rw [hsplit]; exact List.mem_append_left _ hp)
    have hpk : C.eqb p.1 k = false := by
      rw [hsplit] at hkd
      exact (List.pairwise_append.mp hkd).2.2 p hp _ (List.mem_cons_self ..)
    have hfalse : C.eqb a p.1 = false := by
      cases heq : C.eqb a p.1
      · rfl
      · exfalso
        have hx : x = x' := (C.sound hKa hKp).mp heq
        have htrue : C.eqb p.1 k = true := (C.sound hKp hKk).mpr hx.symm
        rw [hpk] at htrue
        cases htrue
    rw [hfalse, isTrue₀_bool]
  have hhit : isTrue₀ (V₀.bool (C.eqb a k)) = true := by
    rw [(C.sound hKa hKk).mpr rfl, isTrue₀_bool]
  simp only [memoizer, run_memo, hcell]
  rw [heqr, hsplit, scan_ret_skip hno, scan_ret_hit hhit, PT.pure_bind]
  simp [run_ret]

/-- **Stability + typing on hits** over valid conditions. -/
theorem hit {ℓ : Loc} {h : Heap V₀} {cell : Cell V₀} {a k b : V₀} {x : A}
    (hv : C.ValidAt ℓ h) (hcell : h[ℓ]? = some cell)
    (hKa : C.KeyRel a x) (hKk : C.KeyRel k x) (hmem : (k, b) ∈ cell.cache) :
    run isTrue₀ 2 (memoizer ℓ a) h = some ⟨h, le_refl h, b⟩ ∧
      ∃ y, C.rel x b y := by
  obtain ⟨cell', hcell', heqr, -, hkd, htyped⟩ := hv
  obtain rfl := Option.some.inj (hcell'.symm.trans hcell)
  refine ⟨hit_run hcell heqr hkd htyped hKa hKk hmem, ?_⟩
  obtain ⟨x', y, hK', hrel⟩ := htyped _ hmem
  obtain rfl : x = x' := keyRel_fn hKk hK'
  exact ⟨y, hrel⟩

/-- **Stability across extensions**: a committed entry answers every later
query (at any code realizing its index) from any valid extension,
effect-free. With functionality of `rel`, the section's value at each index
is settled at commit time. -/
theorem stable {ℓ : Loc} {h h' : Heap V₀} {cell : Cell V₀} {a k b : V₀} {x : A}
    (hv' : C.ValidAt ℓ h') (hle : h ≤ h') (hcell : h[ℓ]? = some cell)
    (hKa : C.KeyRel a x) (hKk : C.KeyRel k x) (hmem : (k, b) ∈ cell.cache) :
    run isTrue₀ 2 (memoizer ℓ a) h' = some ⟨h', le_refl h', b⟩ ∧
      ∃ y, C.rel x b y := by
  obtain ⟨cell', hcell', hLe⟩ := hle ℓ cell hcell
  obtain ⟨p, hp⟩ := hLe.2.2
  refine hit hv' hcell' hKa hKk ?_
  rw [hp]
  exact List.mem_append_right p hmem

/-- **Totality + typing**: from any valid condition the memoizer terminates;
on a miss it runs the cell's *own* family — whose termination and typing is
the `Π x. ‖B x‖` premise — and commits the result at the queried key code.
The answer realizes a member of `B x` and is cached under a code realizing
`x`, so all later queries at `x` are stable hits.

The premise needs no validity-preservation clause: conditions constrain only
cell `ℓ`, which the frame premise says the family never touches. -/
theorem total {ℓ : Loc}
    (hf : ∀ h, C.ValidAt ℓ h → ∀ (a : V₀) (x : A), C.KeyRel a x →
      ∃ (fuel : ℕ) (s : Step V₀ h),
        run isTrue₀ fuel (C.fam a) h = some s ∧ ∃ y, C.rel x s.val y)
    (hframe : ∀ (a : V₀) (fuel : ℕ) (h : Heap V₀) (s : Step V₀ h),
      run isTrue₀ fuel (C.fam a) h = some s → s.next[ℓ]? = h[ℓ]?)
    {h : Heap V₀} (hv : C.ValidAt ℓ h) {a : V₀} {x : A} (hKa : C.KeyRel a x) :
    ∃ (fuel : ℕ) (s : Step V₀ h),
      run isTrue₀ fuel (memoizer ℓ a) h = some s ∧
      C.ValidAt ℓ s.next ∧ (∃ y, C.rel x s.val y) ∧
      ∃ cell k', s.next[ℓ]? = some cell ∧ C.KeyRel k' x ∧
        (k', s.val) ∈ cell.cache := by
  obtain ⟨cell, hcell, heqr, hfam, hkd, htyped⟩ := hv
  by_cases hmem : ∃ k b, (k, b) ∈ cell.cache ∧ C.KeyRel k x
  · -- hit: stable, effect-free, typed
    obtain ⟨k, b, hkb, hKk⟩ := hmem
    have hv : C.ValidAt ℓ h := ⟨cell, hcell, heqr, hfam, hkd, htyped⟩
    obtain ⟨hrun, htyp⟩ := hit hv hcell hKa hKk hkb
    exact ⟨2, ⟨h, le_refl h, b⟩, hrun, hv, htyp, cell, k, hcell, hKk, hkb⟩
  · -- miss: run the family, commit at the queried key code, return
    have hno : ∀ p ∈ cell.cache, C.eqb a p.1 = false := by
      intro p hp
      cases heq : C.eqb a p.1
      · rfl
      · exfalso
        obtain ⟨x', y', hKp, -⟩ := htyped p hp
        have hx : x = x' := (C.sound hKa hKp).mp heq
        exact hmem ⟨p.1, p.2, by simpa using hp, hx ▸ hKp⟩
    have hno' : ∀ p ∈ cell.cache, isTrue₀ (V₀.bool (C.eqb a p.1)) = false := by
      intro p hp
      rw [hno p hp, isTrue₀_bool]
    obtain ⟨fuel_f, s_f, hrun_f, y, hrel⟩ :=
      hf h ⟨cell, hcell, heqr, hfam, hkd, htyped⟩ a x hKa
    have hrun_f' : run isTrue₀ (fuel_f + 1) (C.fam a) h = some s_f :=
      run_fuel_mono (by omega) hrun_f
    have hcell_f : s_f.next[ℓ]? = some cell :=
      (hframe _ _ _ _ hrun_f).trans hcell
    have hcell' : (s_f.next.commit ℓ a s_f.val)[ℓ]? =
        some ⟨cell.eqr, cell.fam, (a, s_f.val) :: cell.cache⟩ := by
      rw [Heap.commit, Heap.getElem?_updateCell_self, hcell_f]
      rfl
    have hv' : C.ValidAt ℓ (s_f.next.commit ℓ a s_f.val) := by
      refine ⟨_, hcell', heqr, hfam, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun q hq => hno q hq, hkd⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨x, y, hKa, hrel⟩
        · exact htyped p hp
    have hcommit : commitPT ℓ a s_f.val s_f.next =
        some ⟨s_f.next.commit ℓ a s_f.val,
          Heap.le_commit s_f.next ℓ a s_f.val, s_f.val⟩ := rfl
    have hinner := PT.bind_some (f := commitPT ℓ a) hrun_f' hcommit
    have hret : run isTrue₀ (fuel_f + 1) (F.ret s_f.val)
        (s_f.next.commit ℓ a s_f.val) =
        some ⟨s_f.next.commit ℓ a s_f.val, le_refl _, s_f.val⟩ := by
      rw [run_ret]
      rfl
    have houter := PT.bind_some
      (f := fun b => run isTrue₀ (fuel_f + 1) (F.ret b)) hinner hret
    refine ⟨fuel_f + 1 + 1,
      ⟨s_f.next.commit ℓ a s_f.val,
        le_trans s_f.le (Heap.le_commit s_f.next ℓ a s_f.val), s_f.val⟩,
      ?_, hv', ⟨y, hrel⟩, _, a, hcell', hKa, List.mem_cons_self ..⟩
    simp only [memoizer, run_memo, hcell]
    rw [heqr, hfam, show cell.cache = cell.cache ++ [] from (List.append_nil _).symm,
      scan_ret_skip hno', scan_nil, PT.pure_bind]
    exact houter

/-- **Staging**: allocating the cell yields a valid condition with an empty
cache — the entry point for `total`/`hit`. -/
theorem validAt_alloc (C : AcCell A B) (h : Heap V₀) :
    C.ValidAt h.length (h.alloc C.eqr C.fam) := by
  refine ⟨⟨C.eqr, C.fam, []⟩, ?_, rfl, rfl, List.Pairwise.nil,
    fun p hp => absurd hp (List.not_mem_nil)⟩
  rw [Heap.alloc]
  exact List.getElem?_concat_length ..

/-- The generic-section clause (`THEORY.md` §4) for the memoizer at `ℓ`:
totality + typing + caching at every valid condition, and stability of
committed entries across valid extensions. -/
def GenericSection (C : AcCell A B) (ℓ : Loc) : Prop :=
  (∀ h, C.ValidAt ℓ h → ∀ (a : V₀) (x : A), C.KeyRel a x →
    ∃ (fuel : ℕ) (s : Step V₀ h),
      run isTrue₀ fuel (memoizer ℓ a) h = some s ∧
      C.ValidAt ℓ s.next ∧ (∃ y, C.rel x s.val y) ∧
      ∃ cell k', s.next[ℓ]? = some cell ∧ C.KeyRel k' x ∧
        (k', s.val) ∈ cell.cache) ∧
  (∀ (h h' : Heap V₀) (cell : Cell V₀) (a k b : V₀) (x : A),
    C.ValidAt ℓ h' → h ≤ h' → h[ℓ]? = some cell →
    C.KeyRel a x → C.KeyRel k x → (k, b) ∈ cell.cache →
    run isTrue₀ 2 (memoizer ℓ a) h' = some ⟨h', le_refl h', b⟩)

/-- **`AC_dec` is realized**: from any heap, the `AC_dec` program succeeds in
one step, returns the fresh cell's location, and establishes a valid
condition over which the staged memoizer is a generic section of `B`. The
premises are the family's `Π x. ‖B x‖`-clause and the frame property at the
fresh cell (`THEORY.md` §7). -/
theorem acDec_realized (C : AcCell A B) (h : Heap V₀)
    (hf : ∀ h₁, C.ValidAt h.length h₁ → ∀ (a : V₀) (x : A), C.KeyRel a x →
      ∃ (fuel : ℕ) (s : Step V₀ h₁),
        run isTrue₀ fuel (C.fam a) h₁ = some s ∧ ∃ y, C.rel x s.val y)
    (hframe : ∀ (a : V₀) (fuel : ℕ) (h₁ : Heap V₀) (s : Step V₀ h₁),
      run isTrue₀ fuel (C.fam a) h₁ = some s →
        s.next[h.length]? = h₁[h.length]?) :
    ∃ s : Step V₀ h,
      run isTrue₀ 2 C.acDecProg h = some s ∧
      s.val = V₀.nat h.length ∧
      C.ValidAt h.length s.next ∧
      C.GenericSection h.length := by
  have halloc : allocPT C.eqr C.fam h =
      some ⟨h.alloc C.eqr C.fam, Heap.le_alloc h C.eqr C.fam, h.length⟩ := rfl
  have hret : run isTrue₀ 1 (F.ret (V₀.nat h.length)) (h.alloc C.eqr C.fam) =
      some ⟨h.alloc C.eqr C.fam, le_refl _, V₀.nat h.length⟩ := by
    rw [run_ret]
    rfl
  have hrun := PT.bind_some
    (f := fun ℓ => run isTrue₀ 1 (F.ret (V₀.nat ℓ))) halloc hret
  refine ⟨⟨h.alloc C.eqr C.fam, Heap.le_alloc h C.eqr C.fam, V₀.nat h.length⟩,
    ?_, rfl, validAt_alloc C h,
    fun h₁ hv a x hKa => total hf hframe hv hKa,
    fun h₁ h₂ cell a k b x hv' hle hc hKa hKk hm =>
      (stable hv' hle hc hKa hKk hm).1⟩
  simp only [acDecProg, run_alloc]
  exact hrun

end AcCell

/-! ### The increment-1 instance: `A = ℕ` with code equality -/

/-- The `ℕ`-indexed instance: numeral keys, code equality as the eq-code. -/
def natCell {B' : ℕ → Type v} (rel : (n : ℕ) → V₀ → B' n → Prop) (f : V₀ → F V₀) :
    AcCell ℕ B' where
  KeyRel k n := k = V₀.nat n
  eqb a k := decide (a = k)
  rel := rel
  fam := f
  sound := by
    rintro k x k' x' rfl rfl
    simp

/-! ### Non-vacuity: a concrete instance with all premises discharged

If the premises of `acDec_realized` were not simultaneously satisfiable the
capstone would be vacuous. Here is a concrete `AcCell` — index `ℕ`, family
constantly `Bool`, the constant-`true` choice — for which both premises hold
unconditionally, yielding a **hypothesis-free** realization of `AC_dec`. -/

/-- A concrete cell: numeral keys, `B n = Bool`, value codes are booleans, the
family is constantly `true`. -/
def boolCell : AcCell ℕ (fun _ => Bool) :=
  natCell (fun _ v b => v = V₀.bool b) (fun _ => F.ret (V₀.bool true))

/-- **The capstone is not vacuous**: for the concrete `boolCell`, `AC_dec` is
realized with no remaining hypotheses. -/
theorem boolCell_acDec (h : Heap V₀) :
    ∃ s : Step V₀ h,
      run isTrue₀ 2 boolCell.acDecProg h = some s ∧
      s.val = V₀.nat h.length ∧
      boolCell.ValidAt h.length s.next ∧
      boolCell.GenericSection h.length := by
  apply boolCell.acDec_realized
  · -- family premise: the constant-`true` family terminates and is typed
    intro h₁ _ a n _
    refine ⟨1, ⟨h₁, le_refl h₁, V₀.bool true⟩, ?_, true, rfl⟩
    change run isTrue₀ 1 (F.ret (V₀.bool true)) h₁ = _
    rw [run_ret]
    rfl
  · -- frame premise: a pure family leaves every cell untouched
    intro a fuel h₁ s hs
    have hs' : run isTrue₀ fuel (F.ret (V₀.bool true)) h₁ = some s := hs
    obtain ⟨hnext, -⟩ := run_ret_inv hs'
    rw [hnext]

/-! ### A pair cell: decidable equality coarser than code identity

`natCell` keys each index by a *single* code (`eqb` is code equality), so the
decidable-equality machinery never actually collapses two distinct codes. The
*pair cell* is the first instance where it does: index `n` is realized by **both**
`2n` and `2n+1`, and `eqb` decides "same pair" (`⌊·/2⌋` equal), not code identity.
So `2n` and `2n+1` are distinct codes realizing the *same* index, and the memoizer
routes them together — "decidable equality is persistence of the key-partition",
exercised non-trivially. This is the structural core of the decidable-equality
*index* generalization (the eq is genuinely coarser than `=` on codes).

(This is the *projective* shape — both realizers always present, so a normal form
is computable. The genuinely non-projective version — `tailcalled`'s twisted-`ℕ`,
where which of `{2n, 2n+1}` is a valid realizer is fixed by diagonalizing against
all machines so no normal form exists — needs a computability layer this
development does not have; see the lineage note in the README.) -/

/-- "Same pair": equality of `⌊·/2⌋` on numerals, coarser than code identity. -/
def pairEqb : V₀ → V₀ → Bool
  | .nat i, .nat j => decide (i / 2 = j / 2)
  | _, _ => false

/-- The pair cell: index `n` realized by `2n` and `2n+1`, equality = "same pair". -/
def pairCell {B' : ℕ → Type v} (rel : (n : ℕ) → V₀ → B' n → Prop) (f : V₀ → F V₀) :
    AcCell ℕ B' where
  KeyRel k n := k = V₀.nat (2 * n) ∨ k = V₀.nat (2 * n + 1)
  eqb := pairEqb
  rel := rel
  fam := f
  sound := by
    intro k x k' x' hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;>
      simp only [pairEqb, decide_eq_true_eq] <;> omega

/-- **The two codes for one index route together.** An entry stored under the code
`2n` is returned when the memoizer is queried with the *distinct* code `2n+1` —
the decidable equality collapses the two realizers of index `n`. This is the
behaviour `natCell` (single code per index) cannot exhibit. -/
theorem pairCell_routes_together {B' : ℕ → Type v} (rel : (n : ℕ) → V₀ → B' n → Prop)
    (f : V₀ → F V₀) {ℓ : Loc} {h : Heap V₀} {n : ℕ} {b : V₀} {cell : Cell V₀}
    (hv : (pairCell rel f).ValidAt ℓ h) (hcell : h[ℓ]? = some cell)
    (hmem : (V₀.nat (2 * n), b) ∈ cell.cache) :
    run isTrue₀ 2 (memoizer ℓ (V₀.nat (2 * n + 1))) h = some ⟨h, le_refl h, b⟩ :=
  (AcCell.hit hv hcell (Or.inr rfl) (Or.inl rfl) hmem).1

/-- A concrete pair cell, and `AC_dec` realized for it with no remaining
hypotheses — so the decidable-equality-coarser-than-code-identity case is also
non-vacuous. -/
def pairBoolCell : AcCell ℕ (fun _ => Bool) :=
  pairCell (fun _ v b => v = V₀.bool b) (fun _ => F.ret (V₀.bool true))

theorem pairBoolCell_acDec (h : Heap V₀) :
    ∃ s : Step V₀ h,
      run isTrue₀ 2 pairBoolCell.acDecProg h = some s ∧
      s.val = V₀.nat h.length ∧
      pairBoolCell.ValidAt h.length s.next ∧
      pairBoolCell.GenericSection h.length := by
  apply pairBoolCell.acDec_realized
  · intro h₁ _ a n _
    refine ⟨1, ⟨h₁, le_refl h₁, V₀.bool true⟩, ?_, true, rfl⟩
    change run isTrue₀ 1 (F.ret (V₀.bool true)) h₁ = _
    rw [run_ret]
    rfl
  · intro a fuel h₁ s hs
    have hs' : run isTrue₀ fuel (F.ret (V₀.bool true)) h₁ = some s := hs
    obtain ⟨hnext, -⟩ := run_ret_inv hs'
    rw [hnext]

end LeanStatefulAoc
