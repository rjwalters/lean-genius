# Blichfeldt General — Path A (Contrapose) Specification

**Session**: S10 (researcher-12, 2026-05-08)
**Goal**: Provide a build-ready Path A skeleton that mirrors Mathlib's
`exists_pair_mem_lattice_not_disjoint_vadd` (the `k = 1` Blichfeldt) for the `k+1` case,
with all Mathlib lemma names resolved against `mathlib4` master.
**Status**: spec only — Lean prototype deferred until `proofs/.lake` recursive symlink is repaired.
**Build cost when prototyped**: ~30–45 min Mathlib clone + ~10 min cache fetch (current symlink trap).

This complements `blichfeldt-general-roadmap.md` (S9, Path B = explicit covering count, ~195 lines).
Path A is the recommended route: ~110 lines once filled in, leveraging machinery that already
landed in `MinkowskiTheoremOQ04.lean` during S8/S9.

---

## 1. The Contrapositive

The forward statement is:

```lean
∃ pts : Fin (k+1) → ℝⁿ, Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
    ∀ i j, pts i - pts j ∈ (stdLattice n : Set ℝⁿ)
```

The clean reformulation is to factor out the lattice translation:

```lean
∃ z : ℝⁿ, ∃ vs : Fin (k+1) → L, Function.Injective vs ∧ ∀ i, z + (vs i : ℝⁿ) ∈ s
```

where `L := (stdLattice n).toAddSubgroup`. Setting `pts i := z + (vs i : ℝⁿ)`:

* injective: `z + vs i = z + vs j ⇒ vs i = vs j ⇒ i = j` by `add_left_cancel` + `Subtype.ext`.
* membership: by hypothesis.
* differences: `pts i - pts j = (vs i : ℝⁿ) - (vs j : ℝⁿ) = ((vs i - vs j : L) : ℝⁿ) ∈ stdLattice`
  by `AddSubgroupClass.coe_sub` + `(vs i - vs j).property`.

Negating the reformulation:

```lean
∀ z : ℝⁿ, ∀ vs : Fin (k+1) → L, Function.Injective vs → ∃ i, z + (vs i : ℝⁿ) ∉ s
```

i.e. for every base point `z` and every injection `vs : Fin (k+1) → L`, at least one of the
`k+1` translates `z + vs i` lies outside `s`.

This is **equivalent** (once `Set.encard ≤ k`) to:

```lean
∀ z : ℝⁿ, Set.encard {v : L | z + (v : ℝⁿ) ∈ s} ≤ k
```

i.e. for every `z`, the covering count function `c(z) := encard {v : L | z + v ∈ s}` is `≤ k`.

---

## 2. Three-Move Proof in 1–4 Lines per Move

After the contrapose, the Goal is `volume s ≤ (k : ℝ≥0∞)`. Set:

```lean
let L := (stdLattice n).toAddSubgroup
let F := stdFundDomain n
let c : ℝⁿ → ℝ≥0∞ := fun z => ∑' v : L, s.indicator (fun _ => 1) (z + (v : ℝⁿ))
```

* **Move A** (already done in `MinkowskiTheoremOQ04.lean:185`):

  `volume_eq_setLIntegral_indicator_tsum h_meas : ∫⁻ z in F, c z ∂volume = volume s`.

* **Move B** (the new work — pointwise bound `c z ≤ k`):

  Show `∀ z, c z ≤ (k : ℝ≥0∞)` from the contraposed hypothesis. This is a single-Set
  cardinality argument: bridge `c z` to `Set.encard {v : L | z + v ∈ s}` via
  `tsum_subtype` + `ENNReal.tsum_set_one`, then bound the encard by `k` from the hypothesis
  via `not_lt` of `Set.encard ≤ k`.

* **Move C** (integrate the pointwise bound):

  ```lean
  ∫⁻ z in F, c z ∂volume ≤ ∫⁻ _ in F, (k : ℝ≥0∞) ∂volume
                       = (k : ℝ≥0∞) * volume F = (k : ℝ≥0∞) * 1 = (k : ℝ≥0∞)
  ```

  using `setLIntegral_mono_ae`, `setLIntegral_const`, `stdLattice_covolume`, `mul_one`.

Combine A + C: `volume s = ∫⁻ z in F, c z ≤ k`. ∎

---

## 3. Mathlib API Inventory (verified against `mathlib4` master, 2026-05-08)

| Lemma | Mathlib location | Statement |
|---|---|---|
| `tsum_subtype` | `Mathlib/MeasureTheory/Measure/Count.lean` (used at `le_count_apply`) | `∑' _ : ↥s, f _ = ∑' i, s.indicator f i`. Confirmed via `gh api search/code "tsum_subtype repo:leanprover-community/mathlib4"` — 10 callers across MeasureTheory + NumberTheory. |
| `ENNReal.tsum_set_one` | `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` | `∑' _ : ↥s, (1 : ℝ≥0∞) = s.encard`. ENat → ENNReal coercion via `ENat.toENNReal`. |
| `Set.encard_le_iff_card_le_card_of_finite` (or direct `encard_le`) | `Mathlib/Data/Set/Card.lean` | `s.encard ≤ k ↔ ∀ t ⊆ s, t.Finite → t.toFinset.card ≤ k`. Used in Move B. |
| `Set.exists_subset_encard_eq` | `Mathlib/Data/Set/Card.lean` | `k ≤ s.encard → ∃ t ⊆ s, t.encard = k`. Used in the Move B contradiction direction (extract `k+1` distinct elements when `encard > k`). |
| `Set.Infinite.exists_subset_ncard_eq` | `Mathlib/Data/Set/Card.lean` | `s.Infinite → ∀ k, ∃ t ⊆ s, t.Finite ∧ t.ncard = k`. Used as a sub-step for the infinite case. |
| `MeasureTheory.setLIntegral_mono_ae` | `Mathlib/MeasureTheory/Integral/Lebesgue/MonotoneClass.lean` | `f ≤ g a.e. on s → ∫⁻ in s, f ≤ ∫⁻ in s, g`. Move C. |
| `MeasureTheory.setLIntegral_const` | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean` | `∫⁻ _ in s, c ∂μ = c * μ s`. Move C. |
| `IsAddFundamentalDomain.exists_ne_zero_vadd_eq` | `Mathlib/MeasureTheory/Group/FundamentalDomain.lean:443` | Already used by `blichfeldt_basic`. |
| `MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd` | `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean:46` | The 6-line proof we are mirroring. Source: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean`. |
| `volume_eq_setLIntegral_indicator_tsum` | `proofs/Proofs/MinkowskiTheoremOQ04.lean:185` | **Already proved (S9, PR #16995).** Move A. |

All lemmas verified present in Mathlib `v4.26.0` via `gh api search/code` and direct file fetches.

---

## 4. The Contrapose Proof Skeleton (Lean 4)

```lean
/-- **Blichfeldt's General Theorem** (k+1-version): vol(s) > k ⇒ k+1 ℤⁿ-congruent points in s. -/
theorem blichfeldt_general {n : ℕ} [NeZero n]
    (k : ℕ) (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (k : ENNReal) < volume s) :
    ∃ pts : Fin (k+1) → Fin n → ℝ,
      Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
      ∀ i j, pts i - pts j ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  -- Convert to the cleaner `(z, vs)` reformulation.
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
      rw [h_sub]
      have h_cast : (vs i : Fin n → ℝ) - (vs j : Fin n → ℝ)
                  = ((vs i - vs j : (stdLattice n).toAddSubgroup) : Fin n → ℝ) := by
        rw [AddSubgroupClass.coe_sub]
      rw [h_cast]
      exact (vs i - vs j).2
  -- Contrapose: hypothesis becomes "no z + vs all in s", goal becomes vol s ≤ k.
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : ∀ z, ∀ vs : Fin (k+1) → L, Injective vs → ∃ i, z + (vs i : ℝⁿ) ∉ s
  -- We will derive volume s ≤ (k : ℝ≥0∞), contradicting h_vol.
  apply absurd h_vol (not_lt.mpr ?_)
  -- Move A: ∫⁻ z in F, c z ∂volume = volume s   (already proved!)
  rw [← volume_eq_setLIntegral_indicator_tsum h_meas]
  -- Move B: pointwise bound c z ≤ (k : ℝ≥0∞)
  have h_pointwise : ∀ z : Fin n → ℝ,
      (∑' v : (stdLattice n).toAddSubgroup,
          s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)) ≤ (k : ENNReal) := by
    intro z
    -- Bridge to encard
    set T : Set (stdLattice n).toAddSubgroup :=
      {v | (v : Fin n → ℝ) + z ∈ s} with hT_def
    have h_bridge :
        ∑' v : (stdLattice n).toAddSubgroup,
            s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)
          = T.encard := by
      -- The summand equals T.indicator 1 v: indicator-of-indicator collapse.
      -- s.indicator 1 ((v : ℝⁿ) + z) = if (v + z) ∈ s then 1 else 0
      --                              = T.indicator 1 v.
      have h_summand_eq : ∀ v : (stdLattice n).toAddSubgroup,
          s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)
            = T.indicator (fun _ => (1 : ENNReal)) v := by
        intro v
        simp [Set.indicator, hT_def, Set.mem_setOf_eq]
      rw [tsum_congr h_summand_eq, ← tsum_subtype, ENNReal.tsum_set_one]
    rw [h_bridge]
    -- T.encard ≤ k follows from h_neg: any `k+1` distinct elements of T contradicts h_neg.
    -- Use `Set.encard_le_iff_card_le_card_of_finite`-style: contrapositive via
    -- `Set.exists_subset_encard_eq`.
    by_contra h_too_many
    push_neg at h_too_many   -- (k : ℝ≥0∞) < T.encard
    -- Convert to ((k+1 : ℕ) : ℕ∞) ≤ T.encard
    have h_le_encard : ((k + 1 : ℕ) : ℕ∞) ≤ T.encard := by
      -- ENNReal.coe_natCast comparison + ENat.add_one_le_iff
      sorry  -- ENat/ENNReal arithmetic; ~5 lines
    obtain ⟨T₀, hT₀_sub, hT₀_card⟩ := Set.exists_subset_encard_eq h_le_encard
    -- T₀ ⊆ T, T₀.encard = k+1; extract Finset of size k+1
    have hT₀_finite : T₀.Finite := by
      rw [Set.encard_lt_top_iff.mp]; rw [hT₀_card]; exact ENat.coe_lt_top _
    set F₀ : Finset _ := hT₀_finite.toFinset with hF₀_def
    have hF₀_card : F₀.card = k + 1 := by
      rw [hF₀_def, Set.Finite.toFinset_eq_toFinset, ← Set.ncard_eq_toFinset_card', Set.encard_eq_coe_toFinset_card]
      sorry  -- standard Set.Finite ↔ Finset bookkeeping; ~5 lines
    -- Build Fin (k+1) → L injection from F₀
    obtain ⟨vs, hvs_inj, hvs_range⟩ : ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
        Function.Injective vs ∧ Set.range vs = ↑F₀ := by
      sorry  -- standard: Finset.equivFin or `Set.Finite.exists_injective`; ~5 lines
    -- Each vs i ∈ T (via T₀ ⊆ T), i.e., (vs i : ℝⁿ) + z ∈ s. Apply h_neg with z := -z and adjust.
    -- The form needed by h_neg is `∀ i, z' + (vs i : ℝⁿ) ∈ s`, where z' may be `z` or `-z`
    -- depending on which translate convention we use.
    have h_all_in : ∀ i, z + (vs i : Fin n → ℝ) ∈ s := by
      intro i
      have h_in_T : vs i ∈ T := hT₀_sub (by rw [← hvs_range]; exact ⟨i, rfl⟩)
      -- T = {v | (v : ℝⁿ) + z ∈ s}, and (v : ℝⁿ) + z = z + (v : ℝⁿ) by add_comm
      have : (vs i : Fin n → ℝ) + z = z + (vs i : Fin n → ℝ) := by ring
      rwa [Set.mem_setOf_eq, this] at h_in_T
    -- Contradicts h_neg z vs hvs_inj: ∃ i, z + vs i ∉ s.
    obtain ⟨i, h_not_in⟩ := h_neg z vs hvs_inj
    exact h_not_in (h_all_in i)
  -- Move C: integrate pointwise bound.
  calc ∫⁻ z in stdFundDomain n,
          (∑' v : (stdLattice n).toAddSubgroup,
              s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)) ∂volume
      ≤ ∫⁻ _ in stdFundDomain n, (k : ENNReal) ∂volume :=
        MeasureTheory.setLIntegral_mono_ae (by measurability)
          (MeasureTheory.ae_of_all _ h_pointwise)
    _ = (k : ENNReal) * volume (stdFundDomain n) := MeasureTheory.setLIntegral_const _ _
    _ = (k : ENNReal) * 1 := by rw [stdLattice_covolume]
    _ = (k : ENNReal) := mul_one _
```

**Total cost estimate**: ~110 lines once the 3 `sorry` placeholders are filled in. Two of the three
`sorry`s are pure ENat/ENNReal/Finset arithmetic (5 lines each). The third (`Set.range vs = ↑F₀`) is
standard `Finset.equivFin` machinery (5 lines).

---

## 5. Critical Path: The 3 Remaining `sorry`s

| `sorry` | What it proves | Approach | Estimated lines |
|---|---|---|---|
| 1: `((k+1 : ℕ) : ℕ∞) ≤ T.encard` from `(k : ℝ≥0∞) < T.encard` | ENat/ENNReal cast comparison | `Nat.lt_iff_add_one_le` plus `ENNReal.coe_natCast` ↔ `ENat.toENNReal`; or `not_lt` after `Nat.cast_lt_cast` and the trivial `(k : ℝ≥0∞) = ENat.toENNReal k`. | 5 |
| 2: `F₀.card = k + 1` from `T₀.encard = k + 1` and `T₀.Finite` | `Set.Finite.toFinset.card = T₀.ncard` and `T₀.ncard = T₀.encard.toNat = (k+1).toNat = k+1` | `Set.Finite.toFinset_card`, `Set.encard_toNat_eq_ncard`, `ENat.toNat_coe_natCast`. | 5 |
| 3: `∃ vs : Fin (k+1) → L, Injective vs ∧ Set.range vs = ↑F₀` | Pick a Finset bijection | `F₀.equivFin` (or `Finset.equivOfCardEq`) returns `F₀ ≃ Fin F₀.card`; compose with the inclusion `↑F₀ ↪ L`. | 5 |

Each `sorry` is mechanical Mathlib bookkeeping. None requires deep mathematical content.

---

## 6. Comparison: Path A (Contrapose) vs Path B (Explicit Covering Count)

| Aspect | Path A (this spec) | Path B (S9 roadmap) |
|---|---|---|
| Total lines | ~110 | ~195 |
| Reuses S9 work? | Yes — `volume_eq_setLIntegral_indicator_tsum` directly | Yes — same identity |
| Pigeonhole-on-integral subproof | Inline `setLIntegral_mono_ae` (3 lines) | Stand-alone Step 2 lemma (~20 lines) |
| `tsum → ncard/encard` bridge | Inline via `tsum_subtype + ENNReal.tsum_set_one` (3 lines + 5-line cast lemma) | Stand-alone Step 4 lemma (~35 lines) |
| Combinatorial extraction | After contrapose, run `Set.exists_subset_encard_eq` once | Forward direction, more bookkeeping |
| Mirrors Mathlib k=1 proof | **Yes** (`exists_pair_mem_lattice_not_disjoint_vadd`) | No |
| Mathlib upstream contribution potential | High — natural generalization of an existing Mathlib proof | Lower — bespoke covering-count machinery |

**Recommendation**: prototype Path A in S11 once `proofs/.lake` is repaired. ~110 lines, three
mechanical `sorry`s to fill in, well-aligned with Mathlib idiom.

---

## 7. Why Path A Mirrors the Mathlib Proof

Mathlib's `exists_pair_mem_lattice_not_disjoint_vadd` (`Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean:46`)
proves the `k = 1` case in 6 lines:

```lean
theorem exists_pair_mem_lattice_not_disjoint_vadd
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  contrapose! h
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_right)
```

The 6-line proof structure:
1. `contrapose!`
2. `μ s = ∑' v, μ ((v +ᵥ s) ∩ F)` — `IsAddFundamentalDomain.measure_eq_tsum`
3. `= μ (⋃ v, ((v +ᵥ s) ∩ F))` — `measure_iUnion₀` (sigma-additivity for pairwise null-disjoint)
4. `≤ μ F` — `measure_mono` + `Set.iUnion_subset` + `Set.inter_subset_right`

Path A is **structurally the same** with one substitution: instead of `measure_iUnion₀`
(disjointness gives `∑ ≤ μ ⋃`), use **Tonelli + indicator pointwise bound** (k+1-multiplicity
gives `∑ ≤ k · μ F`). Concretely the analogue is:

| Mathlib k=1 step | Path A k+1 step |
|---|---|
| `fund.measure_eq_tsum` | `volume_eq_setLIntegral_indicator_tsum` (proved S9) |
| `measure_iUnion₀` (disjoint ⇒ ∑ μ = μ ∪) | Pointwise bound `c z ≤ k` ⇒ `∫⁻ c ≤ k · μ F` |
| `measure_mono` (∪ ⊆ F so μ ∪ ≤ μ F) | `setLIntegral_mono_ae` (`c ≤ k a.e.` so `∫⁻ c ≤ k · μ F`) |

Path A is the "k+1 generalization of the Mathlib proof" — and at the cost of an extra Tonelli +
encard bridge (8 lines combined), it stays structurally identical.

---

## 8. Open Questions for S11

* **Q1 (resolved)**: Mathlib has `tsum_subtype` and `ENNReal.tsum_set_one`. The bridge from
  tsum-of-indicators to encard is two lines, not 35. Path A line count drops from the previous
  estimate of "comparable to Path B" to **~110 lines**.
* **Q2**: Is the `T : Set L` side of the bridge the right target, or should we work directly with
  `Set.encard` over the carrier `Fin n → ℝ`? The subtype-of-`L` formulation is clean because
  `vs : Fin (k+1) → L` is injective by hypothesis (no further bookkeeping for "in lattice"); the
  carrier formulation needs extra `vs i ∈ stdLattice` membership tracking.
  Recommend: keep `T : Set L`.
* **Q3**: `lintegral_mono_ae` vs `setLIntegral_mono_ae` — verify which Mathlib v4.26.0 expects in
  the `setLIntegral` calc. (Both names appear; the `set` variant with `restrict` is the right one
  per S9 roadmap §3.) Spot-check during S11 prototype.
* **Q4 (advanced)**: After Path A lands, is the proof short enough to upstream? Mathlib's
  `exists_pair_mem_lattice_not_disjoint_vadd` is the abstract subgroup form (no `ℝⁿ`/lattice
  specialization). A k+1 generalization at the same abstraction (any `IsAddFundamentalDomain` plus
  Tonelli) might fit Mathlib upstream. Worth a one-line note in the eventual PR.

---

## 9. Build Infrastructure Reminder

`proofs/.lake -> proofs/.lake` recursive symlink (memory `feedback_researcher_lake_symlink_broken`)
makes every Docker build a 30–45 min Mathlib clone + 10 min cache fetch. Until repaired, S11 should:

1. Run a single Docker build with `LEAN_BUILD_TIMEOUT=60m` to prototype Path A end-to-end.
2. Or wait for symlink repair (which a separate mechanic/auditor session can address).

---

## 10. Recommended Session Sequence (revised)

* **S11** (1–2 hr): Prototype Path A per §4 skeleton; resolve the 3 mechanical `sorry`s.
* **S12** (post-build verify): Promote `meta.json` `axiomCount` 1→0, set `status: verified`,
  `badge: original`. Update gallery entry.
* **S13** (optional): Upstream Mathlib generalization of
  `exists_pair_mem_lattice_not_disjoint_vadd` → k+1 version at abstract subgroup level.

---

## Provenance

- Mathlib source files inspected via `gh api repos/leanprover-community/mathlib4/...` on 2026-05-08.
- `volume_eq_setLIntegral_indicator_tsum` taken from `MinkowskiTheoremOQ04.lean:185` on origin/main
  (post-PR #16995).
- `exists_pair_mem_lattice_not_disjoint_vadd` taken verbatim from
  `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean:46` on `mathlib4` master.
- `tsum_subtype` usage pattern taken from `Mathlib/MeasureTheory/Measure/Count.lean:le_count_apply`.
- `ENNReal.tsum_set_one` taken from `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`.
- Set.exists_subset_encard_eq + Set.Infinite.exists_subset_ncard_eq taken from
  `Mathlib/Data/Set/Card.lean`.
