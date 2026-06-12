import LeanStatefulAoc.NonBoolean

/-!
# Choice: the memoizer realizes `AC_dec` (K2)

Increment 1 of K2 (`THEORY.md` §7): index `A = ℕ`, pure code-equality eq,
values in an abstract data family `B : ℕ → Type` realized by an abstract
condition-free relation `rel : (n : ℕ) → V₀ → B n → Prop`. Data-ness is
structural in `rel`'s type; functionality of `rel` reduces semantic
single-valuedness to cache determinism.

Contents: the condition predicate `ValidAt` (the semantic conditions of
`THEORY.md` §2, specialized to one `AC_dec` cell) and the generic-section
clause for the memoizer over it — **totality + typing** (`ValidAt.total`: the
miss path runs the cell's own family and commits), **stability**
(`ValidAt.hit`, `ValidAt.stable`: hits are effect-free and persist across all
valid extensions — behavioral single-valuedness; with `rel` functional, also
semantic single-valuedness), and **staging** (`validAt_alloc`: the `AC_dec`
program's allocation step establishes `ValidAt`).
-/

namespace LeanStatefulAoc

universe u

variable {B : ℕ → Type u}

/-- The condition predicate for an `AC_dec` cell at `ℓ` with family `f`:
the cell exists, owns the label `(eqCode, f)`, its keys are pairwise-distinct
numerals, and every entry realizes some value of the family. This is the
semantic-conditions discipline of `THEORY.md` §2 specialized to one cell. -/
def ValidAt (rel : (n : ℕ) → V₀ → B n → Prop) (f : V₀ → F V₀) (ℓ : Loc)
    (h : Heap V₀) : Prop :=
  ∃ cell, h[ℓ]? = some cell ∧ cell.eqr = eqCode ∧ cell.fam = f ∧
    (cell.cache.Pairwise fun p q => p.1 ≠ q.1) ∧
    ∀ p ∈ cell.cache, ∃ n y, p.1 = V₀.nat n ∧ rel n p.2 y

/-- A cache hit, in general form: if `(a, b)` is cached in a distinct-key cell
routed by `eqCode`, the memoizer at key `a` returns `b` and leaves the heap
unchanged (pure eq makes hits effect-free). Fuel `2` always suffices. -/
theorem memoizer_hit {h : Heap V₀} {ℓ : Loc} {cell : Cell V₀} {a b : V₀}
    (hcell : h[ℓ]? = some cell) (heqr : eqCode = cell.eqr)
    (hkd : cell.cache.Pairwise fun p q => p.1 ≠ q.1)
    (hmem : (a, b) ∈ cell.cache) :
    run isTrue₀ 2 (memoizer ℓ a) h = some ⟨h, le_refl h, b⟩ := by
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hmem
  have hno : ∀ p ∈ l₁, p.1 ≠ a := by
    intro p hp
    rw [hsplit] at hkd
    exact (List.pairwise_append.mp hkd).2.2 p hp _ (List.mem_cons_self ..)
  simp only [memoizer, run_memo, hcell]
  rw [← heqr, hsplit, scan_skip hno, scan_hit_head, PT.pure_bind]
  simp [run_ret]

/-- **Stability + typing on hits**: on a valid condition with `(nat n, b)`
cached, the memoizer returns `b` without extending the heap, and `b` realizes
an element of `B n`. Together with key-distinctness this is the behavioral
single-valuedness of the generic-section clause: every later query at `n`
finds the same entry, hence the same code, hence (by functionality of `rel`)
the same value. -/
theorem ValidAt.hit {rel : (n : ℕ) → V₀ → B n → Prop} {f : V₀ → F V₀}
    {ℓ : Loc} {h : Heap V₀} {n : ℕ} {b : V₀} {cell : Cell V₀}
    (hv : ValidAt rel f ℓ h) (hcell : h[ℓ]? = some cell)
    (hmem : (V₀.nat n, b) ∈ cell.cache) :
    run isTrue₀ 2 (memoizer ℓ (V₀.nat n)) h = some ⟨h, le_refl h, b⟩ ∧
      ∃ y, rel n b y := by
  obtain ⟨cell', hcell', heqr, -, hkd, htyped⟩ := hv
  obtain rfl := Option.some.inj (hcell'.symm.trans hcell)
  refine ⟨memoizer_hit hcell heqr.symm hkd hmem, ?_⟩
  obtain ⟨n', y, hkey, hrel⟩ := htyped _ hmem
  obtain rfl : n = n' := by cases hkey; rfl
  exact ⟨y, hrel⟩

/-- **Totality + typing**: from any valid condition the memoizer terminates;
on a miss it runs the cell's *own* family — whose termination and typing is
the `Π n. ‖B n‖` premise — and commits the result at the queried key. The
answer realizes an element of `B n` and is cached in the resulting valid
condition, so all later queries at `n` are stable hits.

The premise needs no validity-preservation clause: increment-1 conditions
constrain only cell `ℓ`, and the frame premise says `f` never touches it. -/
theorem ValidAt.total {rel : (n : ℕ) → V₀ → B n → Prop} {f : V₀ → F V₀} {ℓ : Loc}
    (hf : ∀ (h : Heap V₀), ValidAt rel f ℓ h → ∀ n : ℕ,
      ∃ (fuel : ℕ) (s : Step V₀ h),
        run isTrue₀ fuel (f (V₀.nat n)) h = some s ∧ ∃ y, rel n s.val y)
    (hframe : ∀ (a : V₀) (fuel : ℕ) (h : Heap V₀) (s : Step V₀ h),
      run isTrue₀ fuel (f a) h = some s → s.next[ℓ]? = h[ℓ]?)
    {h : Heap V₀} (hv : ValidAt rel f ℓ h) (n : ℕ) :
    ∃ (fuel : ℕ) (s : Step V₀ h),
      run isTrue₀ fuel (memoizer ℓ (V₀.nat n)) h = some s ∧
      ValidAt rel f ℓ s.next ∧ (∃ y, rel n s.val y) ∧
      ∃ cell, s.next[ℓ]? = some cell ∧ (V₀.nat n, s.val) ∈ cell.cache := by
  obtain ⟨cell, hcell, heqr, hfam, hkd, htyped⟩ := hv
  by_cases hmem : ∃ b, (V₀.nat n, b) ∈ cell.cache
  · -- hit: stable, effect-free, typed
    obtain ⟨b, hb⟩ := hmem
    have htyp : ∃ y, rel n b y := by
      obtain ⟨n', y, hkey, hrel⟩ := htyped _ hb
      obtain rfl : n = n' := by cases hkey; rfl
      exact ⟨y, hrel⟩
    exact ⟨2, ⟨h, le_refl h, b⟩, memoizer_hit hcell heqr.symm hkd hb,
      ⟨cell, hcell, heqr, hfam, hkd, htyped⟩, htyp, cell, hcell, hb⟩
  · -- miss: run the family, commit, return
    have hno : ∀ p ∈ cell.cache, p.1 ≠ V₀.nat n := by
      intro p hp hkey
      refine hmem ⟨p.2, ?_⟩
      rw [← hkey]
      simpa using hp
    obtain ⟨fuel_f, s_f, hrun_f, y, hrel⟩ :=
      hf h ⟨cell, hcell, heqr, hfam, hkd, htyped⟩ n
    have hrun_f' : run isTrue₀ (fuel_f + 1) (f (V₀.nat n)) h = some s_f :=
      run_fuel_mono (by omega) hrun_f
    -- the family never touches cell `ℓ`, so the commit lands on `cell`
    have hcell_f : s_f.next[ℓ]? = some cell :=
      (hframe _ _ _ _ hrun_f).trans hcell
    have hcell' : (s_f.next.commit ℓ (V₀.nat n) s_f.val)[ℓ]? =
        some ⟨cell.eqr, cell.fam, (V₀.nat n, s_f.val) :: cell.cache⟩ := by
      rw [Heap.commit, Heap.getElem?_updateCell_self, hcell_f]
      rfl
    have hv' : ValidAt rel f ℓ (s_f.next.commit ℓ (V₀.nat n) s_f.val) := by
      refine ⟨_, hcell', heqr, hfam, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun q hq => (hno q hq).symm, hkd⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨n, y, rfl, hrel⟩
        · exact htyped p hp
    -- assemble the run at fuel `fuel_f + 1 + 1`
    have hcommit : commitPT ℓ (V₀.nat n) s_f.val s_f.next =
        some ⟨s_f.next.commit ℓ (V₀.nat n) s_f.val,
          Heap.le_commit s_f.next ℓ (V₀.nat n) s_f.val, s_f.val⟩ := rfl
    have hinner := PT.bind_some (f := commitPT ℓ (V₀.nat n)) hrun_f' hcommit
    have hret : run isTrue₀ (fuel_f + 1) (F.ret s_f.val)
        (s_f.next.commit ℓ (V₀.nat n) s_f.val) =
        some ⟨s_f.next.commit ℓ (V₀.nat n) s_f.val,
          le_refl _, s_f.val⟩ := by
      rw [run_ret]
      rfl
    have houter := PT.bind_some
      (f := fun b => run isTrue₀ (fuel_f + 1) (F.ret b)) hinner hret
    refine ⟨fuel_f + 1 + 1,
      ⟨s_f.next.commit ℓ (V₀.nat n) s_f.val,
        le_trans s_f.le (Heap.le_commit s_f.next ℓ (V₀.nat n) s_f.val), s_f.val⟩,
      ?_, hv', ⟨y, hrel⟩, _, hcell', List.mem_cons_self ..⟩
    simp only [memoizer, run_memo, hcell]
    rw [heqr, hfam, show cell.cache = cell.cache ++ [] from (List.append_nil _).symm,
      scan_skip hno, scan_nil, PT.pure_bind]
    exact houter

/-- **Stability across extensions**: once `(nat n ↦ b)` is committed, every
later query at `n` from *any* valid extension returns `b`, effect-free. With
functionality of `rel`, the realized value is also unique: the generic
section's value at `n` is settled at commit time. -/
theorem ValidAt.stable {rel : (n : ℕ) → V₀ → B n → Prop} {f : V₀ → F V₀}
    {ℓ : Loc} {h h' : Heap V₀} {n : ℕ} {b : V₀} {cell : Cell V₀}
    (hv' : ValidAt rel f ℓ h') (hle : h ≤ h')
    (hcell : h[ℓ]? = some cell) (hmem : (V₀.nat n, b) ∈ cell.cache) :
    run isTrue₀ 2 (memoizer ℓ (V₀.nat n)) h' = some ⟨h', le_refl h', b⟩ ∧
      ∃ y, rel n b y := by
  obtain ⟨cell', hcell', hLe⟩ := hle ℓ cell hcell
  obtain ⟨p, hp⟩ := hLe.2.2
  refine hv'.hit hcell' ?_
  rw [hp]
  exact List.mem_append_right p hmem

/-- **Staging**: allocating a fresh `AC_dec` cell yields a valid condition
with an empty cache — the entry point for `ValidAt.total`/`ValidAt.hit`. -/
theorem validAt_alloc (rel : (n : ℕ) → V₀ → B n → Prop) (f : V₀ → F V₀)
    (h : Heap V₀) : ValidAt rel f h.length (h.alloc eqCode f) := by
  refine ⟨⟨eqCode, f, []⟩, ?_, rfl, rfl, List.Pairwise.nil,
    fun p hp => absurd hp (List.not_mem_nil)⟩
  rw [Heap.alloc]
  exact List.getElem?_concat_length ..

end LeanStatefulAoc
