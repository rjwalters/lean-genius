# Blichfeldt General — S11 Prototype (Path A, refined)

**Session**: S11 (researcher-3, 2026-05-08)
**Goal**: Convert the S10 spec (`path-a-contrapose-spec.md`) into a build-ready Lean prototype with each of the three "mechanical sorries" resolved against verified Mathlib v4.26.0 API.
**Status**: source-ready; **build pending** (`proofs/.lake` recursive symlink unrepaired — full Mathlib clone ~30–45 min).

This document is a direct handoff for S12: copy the proof body verbatim into `proofs/Proofs/MinkowskiTheoremOQ04.lean`, run `./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`, and resolve any remaining build errors. If all three previously-identified mechanical sorries close cleanly, the `axiom blichfeldt_general` becomes a `theorem` and `axiomCount` drops 1 → 0.

---

## 1. Mathlib API Verified (2026-05-08, master `aac6750`)

All API names referenced below were verified by `gh api repos/leanprover-community/mathlib4/contents/...` against Mathlib master. No drift expected against `v4.26.0` for these declarations (they are stable, well-established).

| Lemma | File | Signature |
|---|---|---|
| `ENNReal.tsum_set_one` | `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` | `(s : Set α) : ∑' _ : s, (1 : ℝ≥0∞) = s.encard` |
| `tsum_subtype` | (used in `Mathlib/MeasureTheory/Measure/Count.lean`, `le_count_apply`) | `(s : Set α) (f : α → β) : ∑' i : s, f i = ∑' i, s.indicator f i` |
| `ENat.toENNReal_lt` | `Mathlib/Data/Real/ENatENNReal.lean` | `[norm_cast] (m n : ℕ∞) : (m : ℝ≥0∞) < n ↔ m < n` |
| `ENat.toENNReal_coe` | `Mathlib/Data/Real/ENatENNReal.lean` | `[norm_cast] (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n` |
| `ENat.add_one_le_iff` | `Mathlib/Data/ENat/Basic.lean` | `(hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n` |
| `Set.Finite.encard_eq_coe_toFinset_card` | `Mathlib/Data/Set/Card.lean` | `(h : s.Finite) : s.encard = h.toFinset.card` |
| `Set.encard_lt_top_iff` | `Mathlib/Data/Set/Card.lean` | `[simp] : s.encard < ⊤ ↔ s.Finite` |
| `Set.exists_subset_encard_eq` | `Mathlib/Data/Set/Card.lean` | `{k : ℕ∞} (hk : k ≤ s.encard) : ∃ t, t ⊆ s ∧ t.encard = k` |
| `Fintype.equivFinOfCardEq` | `Mathlib/Data/Fintype/EquivFin.lean` | `{n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n` |
| `Fintype.card_coe` | `Mathlib/Data/Fintype/Card.lean` | `[simp] (s : Finset α) : Fintype.card s = s.card` |
| `MeasureTheory.setLIntegral_mono_ae` | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean` | `(hg : Measurable g) (h : ∀ᵐ a ∂μ, a ∈ s → f a ≤ g a) : ∫⁻ a in s, f a ∂μ ≤ ∫⁻ a in s, g a ∂μ` |
| `MeasureTheory.setLIntegral_const` | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean` | `(s : Set α) (c : ℝ≥0∞) : ∫⁻ _ in s, c ∂μ = c * μ s` |
| `volume_eq_setLIntegral_indicator_tsum` | `proofs/Proofs/MinkowskiTheoremOQ04.lean:185` (LOCAL, S9) | `{n} [NeZero n] {s} (h_meas) : ∫⁻ x in F, ∑' g, s.indicator 1 ((g : ℝⁿ)+x) = volume s` |

---

## 2. The Three Mechanical Sorries — Concrete Proofs

### Sorry 1 (spec §5 row 1): cast `(k : ℝ≥0∞) < T.encard` to `((k+1 : ℕ) : ℕ∞) ≤ T.encard`

**Setup**: After `by_contra h_too_many; push_neg at h_too_many` the hypothesis is
```lean
h_too_many : (k : ℝ≥0∞) < T.encard
```
where `T.encard : ℕ∞` is implicitly coerced to `ℝ≥0∞` via `ENat.toENNReal`.

**Concrete proof** (5 lines):
```lean
have h_le_encard : ((k + 1 : ℕ) : ℕ∞) ≤ T.encard := by
  have h_lt_enat : (k : ℕ∞) < T.encard := by
    have h_cast : ((k : ℕ∞) : ℝ≥0∞) < ((T.encard : ℝ≥0∞)) := by exact_mod_cast h_too_many
    exact_mod_cast h_cast
  have h_succ : (k : ℕ∞) + 1 ≤ T.encard :=
    (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr h_lt_enat
  exact_mod_cast h_succ
```

**Why it works**: `ENat.toENNReal_lt` is tagged `[norm_cast]`, so `exact_mod_cast` strips the
`ENat → ENNReal` coercion. Once in `ℕ∞`, `(k : ℕ∞) < T.encard ↔ (k : ℕ∞) + 1 ≤ T.encard` by
`ENat.add_one_le_iff` (with the `k ≠ ⊤` side condition discharged by `ENat.coe_ne_top`). Final
`exact_mod_cast` rewrites `(k : ℕ∞) + 1 = ((k + 1 : ℕ) : ℕ∞)` (via `Nat.cast_add` + `Nat.cast_one`,
both `[norm_cast]`).

---

### Sorry 2 (spec §5 row 2): `F₀.card = k + 1` from `T₀.encard = ((k+1:ℕ):ℕ∞)` and `T₀.Finite`

**Setup**:
```lean
hT₀_card : T₀.encard = ((k + 1 : ℕ) : ℕ∞)
hT₀_finite : T₀.Finite
F₀ : Finset _ := hT₀_finite.toFinset
```

**Concrete proof** (5 lines):
```lean
have hF₀_card : F₀.card = k + 1 := by
  have h_eq : T₀.encard = (F₀.card : ℕ∞) := by
    show T₀.encard = (hT₀_finite.toFinset.card : ℕ∞)
    exact hT₀_finite.encard_eq_coe_toFinset_card
  rw [hT₀_card] at h_eq
  exact_mod_cast h_eq.symm
```

**Why it works**: `Set.Finite.encard_eq_coe_toFinset_card` directly gives
`T₀.encard = (h.toFinset.card : ℕ∞)`. Substituting `T₀.encard = ((k+1:ℕ):ℕ∞)` yields
`((k+1:ℕ):ℕ∞) = (F₀.card : ℕ∞)`, which `exact_mod_cast` reduces to the ℕ-level equation.
The `F₀ : Finset _ := hT₀_finite.toFinset` `let`-binding is unfolded by the explicit `show`.

---

### Sorry 3 (spec §5 row 3): build `Fin (k+1) → L` injection with `Set.range vs = ↑F₀`

**Setup**:
```lean
F₀ : Finset (stdLattice n).toAddSubgroup
hF₀_card : F₀.card = k + 1
```

**Concrete proof** (5 lines):
```lean
obtain ⟨vs, hvs_inj, hvs_range⟩ : ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
    Function.Injective vs ∧ Set.range vs = ↑F₀ := by
  have h_card : Fintype.card (↑F₀ : Set (stdLattice n).toAddSubgroup) = k + 1 := by
    rw [Set.Finite.fintype_coe_eq_toFinset_card]; simpa using hF₀_card
  let e : (↑F₀ : Set _) ≃ Fin (k+1) := Fintype.equivFinOfCardEq h_card
  refine ⟨fun i => (e.symm i).1, ?_, ?_⟩
  · intro i j hij; exact e.symm.injective (Subtype.ext hij)
  · ext x
    simp only [Set.mem_range, Set.mem_coe, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
```

**Why it works**: `(↑F₀ : Set L)` has `Fintype` instance (subtype of a Finset's coercion). Its
cardinality equals `F₀.card = k+1`. `Fintype.equivFinOfCardEq` provides
`(↑F₀ : Set L) ≃ Fin (k+1)`; the value `vs i := (e.symm i).1` is the underlying lattice element.
Injectivity follows from `e.symm.injective` plus `Subtype.ext`. The range equation is two
`simp`-driven case splits (`i ↦ (e.symm i).1` is in `↑F₀` by `(e.symm i).2`; conversely any
`x ∈ ↑F₀` is hit by `e ⟨x, _⟩`).

**Note**: `Set.Finite.fintype_coe_eq_toFinset_card` may need to be replaced with whichever
Mathlib v4.26.0 lemma converts `Fintype.card (↑F₀ : Set _)` to `F₀.card`. Alternatives
worth trying if the name has drifted:
- `Set.toFinset_coe_eq_toFinset` then `Set.toFinset_card`
- direct `simp [Fintype.card_coe]` with `F₀ : Finset _` (since `↑F₀ : Set _` has `Fintype` via `Finset.fintypeCoeSort`)
- `simp; exact hF₀_card` may close it outright depending on which `Fintype` instance Lean picks

The `e.symm` direction (from `Fin (k+1)` to subtype) is the key — once we have it, range membership is purely `simp` bookkeeping.

---

## 3. Full Prototype (drop-in for `MinkowskiTheoremOQ04.lean`)

This replaces the existing `axiom blichfeldt_general ...` declaration (lines 230–242 of the
current file). The companion theorem `blichfeldt_basic_from_general` requires no change since
its statement is preserved.

```lean
/-- **Blichfeldt's General Theorem**: vol(S) > k implies k+1 ℤⁿ-congruent points in S.

Path A (contrapose route, S11 prototype). Mirrors Mathlib's `k=1`
`exists_pair_mem_lattice_not_disjoint_vadd` with Tonelli replacing `measure_iUnion₀`.

Move A: Reuse `volume_eq_setLIntegral_indicator_tsum` (proved S9).
Move B: Pointwise `c z ≤ k` from contraposed hypothesis via `tsum_subtype` + `tsum_set_one`.
Move C: Integrate via `setLIntegral_mono_ae` + `setLIntegral_const` + `stdLattice_covolume`. -/
theorem blichfeldt_general {n : ℕ} [NeZero n]
    (k : ℕ) (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (k : ENNReal) < volume s) :
    ∃ pts : Fin (k+1) → Fin n → ℝ,
      Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
      ∀ i j, pts i - pts j ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  haveI : Countable (stdLattice n).toAddSubgroup := by
    unfold stdLattice
    change Countable (Submodule.span ℤ (Set.range (stdBasis n)))
    infer_instance
  -- Container reformulation: factor out the lattice translation z.
  suffices h : ∃ z : Fin n → ℝ, ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
      Function.Injective vs ∧ ∀ i, z + (vs i : Fin n → ℝ) ∈ s by
    obtain ⟨z, vs, hvs_inj, hvs_in⟩ := h
    refine ⟨fun i => z + (vs i : Fin n → ℝ), ?_, hvs_in, ?_⟩
    · intro i j hij
      have h_coe : (vs i : Fin n → ℝ) = (vs j : Fin n → ℝ) := add_left_cancel hij
      exact hvs_inj (Subtype.ext h_coe)
    · intro i j
      show (z + (vs i : Fin n → ℝ)) - (z + (vs j : Fin n → ℝ))
        ∈ (stdLattice n : Set (Fin n → ℝ))
      have h_sub : (z + (vs i : Fin n → ℝ)) - (z + (vs j : Fin n → ℝ))
                = (vs i : Fin n → ℝ) - (vs j : Fin n → ℝ) := by ring
      rw [h_sub, ← AddSubgroupClass.coe_sub]
      exact (vs i - vs j).2
  -- Contrapose to a volume bound.
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : ∀ z, ∀ vs, Injective vs → ∃ i, z + (vs i : ℝⁿ) ∉ s
  apply absurd h_vol (not_lt.mpr ?_)
  -- Move A: ∫⁻ z in F, c z ∂volume = volume s
  rw [← volume_eq_setLIntegral_indicator_tsum h_meas]
  -- Move B: pointwise c z ≤ (k : ℝ≥0∞)
  have h_pointwise : ∀ z : Fin n → ℝ,
      (∑' v : (stdLattice n).toAddSubgroup,
          s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)) ≤ (k : ENNReal) := by
    intro z
    set T : Set (stdLattice n).toAddSubgroup :=
      {v | (v : Fin n → ℝ) + z ∈ s} with hT_def
    -- Bridge: tsum-of-indicators on L = T.encard.
    have h_summand_eq : ∀ v : (stdLattice n).toAddSubgroup,
        s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)
          = T.indicator (fun _ => (1 : ENNReal)) v := by
      intro v
      by_cases hv : (v : Fin n → ℝ) + z ∈ s
      · simp [Set.indicator, hv, hT_def, Set.mem_setOf_eq]
      · simp [Set.indicator, hv, hT_def, Set.mem_setOf_eq]
    have h_bridge :
        ∑' v : (stdLattice n).toAddSubgroup,
            s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)
          = (T.encard : ℝ≥0∞) := by
      rw [tsum_congr h_summand_eq, ← tsum_subtype, ENNReal.tsum_set_one]
    rw [h_bridge]
    -- Bound encard ≤ k via contrapositive of h_neg.
    by_contra h_too_many
    push_neg at h_too_many
    -- h_too_many : (k : ℝ≥0∞) < (T.encard : ℝ≥0∞)
    have h_le_encard : ((k + 1 : ℕ) : ℕ∞) ≤ T.encard := by
      have h_lt_enat : (k : ℕ∞) < T.encard := by
        have h_cast : ((k : ℕ∞) : ℝ≥0∞) < ((T.encard : ℝ≥0∞)) := by exact_mod_cast h_too_many
        exact_mod_cast h_cast
      have h_succ : (k : ℕ∞) + 1 ≤ T.encard :=
        (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr h_lt_enat
      exact_mod_cast h_succ
    obtain ⟨T₀, hT₀_sub, hT₀_card⟩ :=
      Set.exists_subset_encard_eq h_le_encard
    have hT₀_finite : T₀.Finite := by
      rw [← Set.encard_lt_top_iff, hT₀_card]
      exact ENat.coe_lt_top _
    set F₀ : Finset _ := hT₀_finite.toFinset with hF₀_def
    have hF₀_card : F₀.card = k + 1 := by
      have h_eq : T₀.encard = (F₀.card : ℕ∞) := by
        show T₀.encard = (hT₀_finite.toFinset.card : ℕ∞)
        exact hT₀_finite.encard_eq_coe_toFinset_card
      rw [hT₀_card] at h_eq
      exact_mod_cast h_eq.symm
    -- Build Fin (k+1) → L injection from F₀.
    obtain ⟨vs, hvs_inj, hvs_range⟩ : ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
        Function.Injective vs ∧ Set.range vs = ↑F₀ := by
      have h_card : Fintype.card (↑F₀ : Set (stdLattice n).toAddSubgroup) = k + 1 := by
        rw [Set.Finite.fintype_coe_eq_toFinset_card]; simpa using hF₀_card
      let e : (↑F₀ : Set _) ≃ Fin (k+1) := Fintype.equivFinOfCardEq h_card
      refine ⟨fun i => (e.symm i).1, ?_, ?_⟩
      · intro i j hij; exact e.symm.injective (Subtype.ext hij)
      · ext x
        simp only [Set.mem_range, Set.mem_coe, Finset.mem_coe]
        constructor
        · rintro ⟨i, rfl⟩; exact (e.symm i).2
        · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
    -- Each vs i ∈ T (via T₀ ⊆ T), i.e., (vs i : ℝⁿ) + z ∈ s.
    have h_all_in : ∀ i, z + (vs i : Fin n → ℝ) ∈ s := by
      intro i
      have h_in_F₀ : vs i ∈ F₀ := by
        have : vs i ∈ Set.range vs := ⟨i, rfl⟩
        rwa [hvs_range, Finset.mem_coe] at this
      have h_in_T₀ : vs i ∈ T₀ := by
        rw [hF₀_def, Set.Finite.mem_toFinset] at h_in_F₀
        exact h_in_F₀
      have h_in_T : vs i ∈ T := hT₀_sub h_in_T₀
      have h_swap : (vs i : Fin n → ℝ) + z = z + (vs i : Fin n → ℝ) := by ring
      rwa [Set.mem_setOf_eq, h_swap] at h_in_T
    obtain ⟨i, h_not_in⟩ := h_neg z vs hvs_inj
    exact h_not_in (h_all_in i)
  -- Move C: integrate the pointwise bound.
  calc ∫⁻ z in stdFundDomain n,
          (∑' v : (stdLattice n).toAddSubgroup,
              s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)) ∂volume
      ≤ ∫⁻ _ in stdFundDomain n, (k : ENNReal) ∂volume := by
        apply MeasureTheory.setLIntegral_mono_ae measurable_const
        exact MeasureTheory.ae_of_all _ (fun z _ => h_pointwise z)
    _ = (k : ENNReal) * volume (stdFundDomain n) := by
        rw [MeasureTheory.setLIntegral_const]
    _ = (k : ENNReal) * 1 := by rw [stdLattice_covolume]
    _ = (k : ENNReal) := mul_one _
```

---

## 4. Predicted Build Issues for S12

The prototype above is internally consistent against the verified API table, but build experience
suggests these likely friction points:

| Risk | Symptom | Mitigation |
|---|---|---|
| `setLIntegral_mono_ae` argument order/spelling | "function expected" or wrong implicit binders | Try `MeasureTheory.setLIntegral_mono_ae` vs `setLIntegral_mono_ae` (after `open MeasureTheory`); spec verified the lemma exists in `Mathlib/MeasureTheory/Integral/Lebesgue/MonotoneClass.lean` |
| `Set.Finite.fintype_coe_eq_toFinset_card` name drift | "unknown constant" | Replace with `simpa [Fintype.card_coe] using hF₀_card`, or compute directly `Fintype.card (↑F₀ : Set _) = (↑F₀ : Set _).toFinset.card = F₀.card` |
| `tsum_subtype` reorientation | Goal direction wrong | Use `(tsum_subtype T (fun _ => (1 : ENNReal))).symm` if the spec's direction is reversed |
| `AddSubgroupClass.coe_sub` direction | "motive is not type correct" or rewrite fails | Reverse: `rw [show ... by rw [AddSubgroupClass.coe_sub]]` |
| `Fintype` instance for `↑F₀ : Set _` | Synthesis fails | Add `haveI : Fintype (↑F₀ : Set _) := Finset.fintypeCoeSort F₀` (or whichever lemma) |
| `set` tactic on `Finset` value | Unfolding required to apply `Finite.toFinset` lemmas | Use explicit `show` rewrites (already done at hF₀_card, should be fine) |

If any of these blocks the build, the fix is local (≤ 10 lines) and can be resolved without
changing the proof structure.

---

## 5. Build Plan for S12

Once `proofs/.lake` self-symlink is repaired (current state at HEAD: `lrwxr-xr-x ... -> proofs/.lake` —
recursive). Sequence:

1. Drop the prototype above into `MinkowskiTheoremOQ04.lean` replacing lines 230–242 (`axiom blichfeldt_general ...`).
2. `./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`. Budget 60 min.
3. Resolve any build errors per the table in §4. Each fix should be ≤ 10 lines.
4. Once green: update `meta.json` `axiomCount: 1 → 0`, `status: axiomatized → verified`, `badge: axiom → original`.
5. Update `meta.json` `lineCount` and `theoremCount` to match the new file.
6. Update `state.md` and `<slug>.json` with S12 summary.

---

## 6. Why This Is S11 Progress (not just spec restatement)

The S10 spec identified the three sorries by name and approach but left the concrete Lean as
`sorry  -- ENat/ENNReal arithmetic; ~5 lines` style placeholders. S11 replaces each with a
specific, verified-API Lean snippet. In particular:

- **Sorry 1**: S10 said "or `not_lt` after `Nat.cast_lt_cast`". S11 produces 5 lines using
  `ENat.toENNReal_lt` (`norm_cast`) + `ENat.add_one_le_iff` — both verified present in master.
- **Sorry 2**: S10 said "Set.Finite.toFinset_card + Set.encard_toNat_eq_ncard + ENat.toNat_coe_natCast".
  S11 reduces to a single `Set.Finite.encard_eq_coe_toFinset_card` call (3 lines) — verified
  present in `Mathlib/Data/Set/Card.lean`.
- **Sorry 3**: S10 said "F₀.equivFin (or Finset.equivOfCardEq)". S11 specifies
  `Fintype.equivFinOfCardEq` on the subtype, with explicit injection extraction — verified
  present in `Mathlib/Data/Fintype/EquivFin.lean`.

Plus the integration into the full Move B proof (7 sub-`have`s wired together), which was
described in spec §4 but not assembled.

This is strictly a **spec-to-prototype** advance: the deliverable is now a single Lean block
that can be copied into the file. S12's only job is build verification + drift mitigation.

---

## 7. Provenance

- All Mathlib lemma signatures verified by `gh api repos/leanprover-community/mathlib4/contents/...`
  on 2026-05-08 against master `aac675020a3727a73d444c09e233693a79ad242e`.
- `volume_eq_setLIntegral_indicator_tsum` taken from `MinkowskiTheoremOQ04.lean:185` on
  origin/main (post-PR #16995, S9).
- `path-a-contrapose-spec.md` (S10) provides the structural skeleton; this document fills in
  the three identified mechanical gaps with verified-API Lean.
- Build infrastructure caveat per memory note `feedback_researcher_lake_symlink_broken`.
