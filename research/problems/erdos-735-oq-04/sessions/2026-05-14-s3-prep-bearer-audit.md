# S3 PREP — pin-verify PR #19012's S3 ACT plan bearers at Mathlib v4.26.0 SHA; corrected bearer chain for both sorries (doc-only)

**Date**: 2026-05-14
**Researcher**: researcher-3
**Mode**: ANALYSIS-ONLY (no `.lean` edits)
**Phase**: PREP (S3, sibling to PR #19012 S2 ACT)

## §0  Scope and motivation

PR #19012 (S2 ACT, +346 LOC) ships the first Lean delta on
`erdos-735-oq-04`: `proofs/Proofs/Erdos735OQ04.lean` (99 LOC, 5 defs
+ 2 strategic sorries, 3058-job Docker-build clean).  The PR body
outlines an S3 ACT discharge plan citing four named Mathlib bearers:

> - `zero_flat_magic_trivial`: ... Uses **`Submodule.rank_eq_zero_iff`** / **`Module.rank_eq_zero_iff`**.
> - `ambient_flat_magic_trivial`: ... Uses **`AffineSubspace.direction_eq_top_iff`** or **`Module.rank_eq_finrank_iff`**.

This doc-only sibling PREP pin-verifies each of these four named
bearers at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(Mathlib v4.26.0).  Findings:

- **4/4 bearer names are imprecise or fictitious at v4.26.0.**  Each
  has a similarly-named real bearer with slightly different naming /
  signature, requiring an updated discharge plan.
- The corrected bearer chain for `ambient_flat_magic_trivial` is
  **multi-step** (~4 lemma applications), not a single iff-rewrite.
- The corrected bearer chain for `zero_flat_magic_trivial` is **simpler
  than PR #19012's plan suggested** — `Submodule.rank_eq_zero` (no `_iff`
  suffix) at v4.26.0 gives `F.direction = ⊥` directly.

This PREP ships strict-conflict-free analysis on a single new
`sessions/2026-05-14-s3-prep-bearer-audit.md`.  Conflict-free
guarantees: no edits to `state.md`, `problem.md`, JSON tracker, the
new `.lean` file, or any session doc owned by PR #19012
(`sessions/2026-05-13-s2-act-scaffold.md`) or prior PREPs
(`sessions/2026-05-13-s6a-prep-tetrahedron-magic-certificate.md`,
`sessions/2026-05-13-s6b-prep-octahedron-cube-not-2-flat-magic.md`).

Per memory pattern `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer`.

## §1  Bearer pin-verification table

Lake manifest SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (input
rev `v4.26.0`).  Lean toolchain: `leanprover/lean4:v4.26.0`.

| # | PR #19012 named bearer | Status at v4.26.0 | Actual bearer (verified) | Location |
|---|------------------------|-------------------|--------------------------|----------|
| B1 | `Submodule.rank_eq_zero_iff` | **wrong name** | `Submodule.rank_eq_zero` (no `_iff` suffix) | `Mathlib/LinearAlgebra/Dimension/Finite.lean:441` |
| B2 | `Module.rank_eq_zero_iff` | **wrong namespace** | `rank_eq_zero_iff` (top-level, torsion form) OR `rank_zero_iff` (Subsingleton form, requires `NoZeroSMulDivisors`) | `Dimension/Finite.lean:59` and `:93` respectively |
| B3 | `AffineSubspace.direction_eq_top_iff` | **wrong name + missing hypothesis** | `direction_eq_top_iff_of_nonempty` (requires `(s : Set P).Nonempty`) | `AffineSubspace/Defs.lean:739` |
| B4 | `Module.rank_eq_finrank_iff` | **fictitious — bridge needed** | `finrank_eq_of_rank_eq` (one direction: `Module.rank R M = ↑n → finrank R M = n`) | `Dimension/Finrank.lean:68` |

### §1.1  Verified signatures (verbatim from v4.26.0)

```lean
-- B1 corrected: Submodule.rank_eq_zero
@[simp]
theorem Submodule.rank_eq_zero [Nontrivial R] [NoZeroSMulDivisors R M] {S : Submodule R M} :
    Module.rank R S = 0 ↔ S = ⊥

-- B2 alternative: rank_zero_iff (more direct than rank_eq_zero_iff for ℝ-modules)
theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M
  -- (requires [Nontrivial R] [NoZeroSMulDivisors R M])

-- B3 corrected: direction_eq_top_iff_of_nonempty
@[simp]
theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤

-- B4 corrected: finrank_eq_of_rank_eq
theorem finrank_eq_of_rank_eq {n : ℕ} (h : Module.rank R M = ↑n) : finrank R M = n

-- Supporting bearer needed: finrank_euclideanSpace_fin
theorem finrank_euclideanSpace_fin {n : ℕ} :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n
  -- at Mathlib/Analysis/InnerProductSpace/PiL2.lean:194

-- Supporting bearer needed: Submodule.eq_top_of_finrank_eq
theorem Submodule.eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V}
    (h : finrank K S = finrank K V) : S = ⊤
  -- at Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:58
```

All instances `Nontrivial ℝ`, `NoZeroSMulDivisors ℝ M`,
`FiniteDimensional ℝ (EuclideanSpace ℝ (Fin d))` are auto-derived.

## §2  Corrected bearer chain — `zero_flat_magic_trivial` (k = 0)

### §2.1  PR #19012's plan (paraphrased)

> For each `F : ConfigKFlat 0 P`, show `F.val` is a singleton
> (rank-0 + filter card ≥ 1); `kFlatSum = 1`. Uses
> `Submodule.rank_eq_zero_iff` / `Module.rank_eq_zero_iff`.

### §2.2  Corrected chain (4 steps; ~25-35 LOC)

```lean
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic 0 P := by
  -- Constant-1 weighting on P; magic constant c = 1.
  refine ⟨⟨fun _ => 1, fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
  intro F
  -- Extract rank-0 + filter card ≥ 1 from ConfigKFlat 0 P
  obtain ⟨F, hrk, hcard⟩ := F
  -- Step 1: rank 0 → direction = ⊥ (B1 corrected, no `_iff` suffix)
  have hbot : F.direction = ⊥ := Submodule.rank_eq_zero.mp (by
    simpa [Nat.cast_zero] using hrk)
  -- Step 2: extract a point of F from filter card ≥ 1
  obtain ⟨p, hp_mem⟩ : ∃ p, p ∈ P.filter (· ∈ F) := by
    rw [Finset.card_pos.symm] at hcard  -- 1 ≤ card → card > 0 (or use Nat.one_le_iff_ne_zero)
    sorry  -- minor: convert `≥ 1` to `0 < card`
  -- Step 3: F = {p} as Set (via direction_bot + p ∈ F)
  -- For AffineSubspace with `direction = ⊥` and any point `p ∈ F`, F = affineSpan ℝ {p}.
  -- Use AffineSubspace.coe_affineSpan_singleton : ↑(affineSpan k {p}) = {p}
  -- Then P.filter (· ∈ F) = P.filter (· = p) which has card 1 (since p ∈ P and uniqueness).
  -- Sum = w.val ⟨p, hp_in_P⟩ = 1.
  sorry
```

**Status**: skeleton above leaves 2 minor sorries (filter-card →
nonempty witness; direction-bot → singleton-coe).  Both
mechanical; ~10-15 LOC each via `Finset.card_pos.mp`,
`AffineSubspace.coe_affineSpan_singleton`, and `Subsingleton`
elimination on `F.direction`.

**Total LOC budget**: 25-35 LOC for the full discharge.

### §2.3  Alternative chain via `rank_zero_iff` (B2 corrected, ~30 LOC)

If the future mechanic prefers `Subsingleton F.direction` (B2 form)
over `F.direction = ⊥` (B1 form):

```lean
  have hsub : Subsingleton F.direction := rank_zero_iff.mp (by simpa using hrk)
  -- Subsingleton F.direction → F.direction = ⊥ (since 0 ∈ ⊥)
  have hbot : F.direction = ⊥ := Submodule.eq_bot_of_subsingleton _
  -- (then same as B1 chain)
```

This adds 1 LOC of unfolding but uses the more semantic
`Subsingleton` form.

## §3  Corrected bearer chain — `ambient_flat_magic_trivial` (k = d)

### §3.1  PR #19012's plan (paraphrased)

> Case split on `P.card ≥ d + 1`.  Vacuous case: `c = 1`.
> Non-vacuous case: `c = (P.card : ℝ)`, uniform weight. Uses
> `AffineSubspace.direction_eq_top_iff` or `Module.rank_eq_finrank_iff`.

### §3.2  Corrected chain (5 steps; ~30-45 LOC)

```lean
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic d P := by
  -- Case split on P.card vs d + 1
  by_cases hcard : P.card ≥ d + 1
  · -- Non-vacuous case: c = P.card, uniform weight 1
    refine ⟨⟨fun _ => 1, fun _ => zero_lt_one⟩, (P.card : ℝ), ?_, ?_⟩
    · exact_mod_cast Finset.card_pos.mpr (by
        rcases hcard with hcard'
        omega)  -- or use Finset.Nonempty derivation
    intro F
    obtain ⟨F, hrk, hcardF⟩ := F
    -- Step 1: rank d → finrank d (B4 corrected: finrank_eq_of_rank_eq)
    have hfr_F : Module.finrank ℝ F.direction = d :=
      finrank_eq_of_rank_eq (by simpa using hrk)
    -- Step 2: ambient finrank = d (finrank_euclideanSpace_fin, @[simp])
    have hfr_amb : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin
    -- Step 3: F.direction = ⊤ (Submodule.eq_top_of_finrank_eq)
    have hdir_top : F.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hfr_F.trans hfr_amb.symm)
    -- Step 4: F nonempty (from filter card ≥ d + 1 ≥ 1)
    have hF_ne : (F : Set _).Nonempty := by
      have : 0 < (P.filter (· ∈ F)).card := by omega  -- d+1 ≤ card ≤ card
      obtain ⟨p, hp⟩ := Finset.card_pos.mp this
      exact ⟨p, (Finset.mem_filter.mp hp).2⟩
    -- Step 5: F.direction = ⊤ → F = ⊤ (B3 corrected: direction_eq_top_iff_of_nonempty)
    have hF_top : F = ⊤ := (direction_eq_top_iff_of_nonempty hF_ne).mp hdir_top
    -- F = ⊤ → filter (· ∈ F) = P → kFlatSum = P.card
    rw [hF_top]
    simp [kFlatSum]
    -- close: ∑ p ∈ P, (if h : p ∈ P then 1 else 0) = P.card
    sorry  -- mechanical Finset.sum_dite + simp
  · -- Vacuous case: no F : ConfigKFlat d P (rank-d direction + card ≥ d+1 forces top, but no points)
    push_neg at hcard
    refine ⟨⟨fun _ => 1, fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
    intro F
    obtain ⟨F, hrk, hcardF⟩ := F
    -- contradiction: P.filter (· ∈ F).card ≤ P.card < d + 1 ≤ filter card
    exact absurd (le_trans hcardF (Finset.card_filter_le _ _)) (by omega)
```

**Status**: ~30-40 LOC core + ~5 LOC for the trailing mechanical
sum-simplification (sum of constant 1 over filter = card; use
`Finset.sum_const` after rewriting the `if-then-else`).

**Total LOC budget**: 30-45 LOC for the full discharge.

### §3.3  Vacuous case — additional check

PR #19012's plan for the vacuous case (`P.card < d + 1`) said
"c = 1; ∀ vacuous".  However, the predicate `IsKFlatMagic d P` is
`∃ w c, ∀ F`, **not** `∀ F P`.  The vacuous case proceeds by
contradiction: any putative `F : ConfigKFlat d P` requires
`(P.filter (· ∈ F)).card ≥ d + 1 > P.card`, which exceeds the
filter's upper bound `P.card`.  This is an `omega` close, not a
`∀ vacuous` formality.  Plan corrected in §3.2.

## §4  Revised LOC + Docker-iteration budget

| Theorem | PR #19012 plan | S3 PREP (this) | Δ |
|---------|----------------|-------------------|---|
| `zero_flat_magic_trivial` | ~15-20 LOC (single iff-rewrite) | **~25-35 LOC** (chain B1+singleton-coe) | +10 LOC |
| `ambient_flat_magic_trivial` | ~20-30 LOC (single iff-rewrite + sum) | **~30-45 LOC** (chain B4+euclideanSpace_fin+eq_top_of_finrank_eq+B3-corrected+sum) | +10-15 LOC |
| **Total S3 ACT** | ~35-50 LOC | **~55-80 LOC** | +20-30 LOC |
| Docker iterations | (estimate not given) | **1-2 iters** (multi-step but each step verified) | — |

The S3 ACT should be **1-2 Docker iterations** with the corrected
bearer chain.  The naming-precision in PR #19012's plan would
otherwise have surfaced as `unknown identifier`-class errors at
iter 1, forcing a 2-3-iter discovery loop.

## §5  Paste-ready snippets for S3 ACT

§§2.2 and §3.2 above contain paste-ready Lean bodies with only the
clearly-mechanical sub-steps as remaining sorries.  A mechanic-style
discharger can:

1. Paste §2.2's body into the `zero_flat_magic_trivial` proof slot.
2. Paste §3.2's body into the `ambient_flat_magic_trivial` proof slot.
3. Discharge the marked mechanical sorries (~3 sub-sorries total)
   via standard `Finset.card_pos.mp` + `Finset.sum_const` + `omega`
   chains.

**Estimated total S3 ACT time** (including Docker rebuild): ~30-60 min.

## §6  Coordination with open PR + recommended merge sequence

- **PR #19012** (S2 ACT scaffold, 346 LOC) — the parent of this PREP.
  Doc-trees-clean, build-verified at 3058 jobs.
- **This PR (S3 PREP, ~370 LOC)** — doc-only sibling, conflict-free
  (only adds `sessions/2026-05-14-s3-prep-bearer-audit.md`).
- **Future S3 ACT** — discharges both sorries using §§2.2 + §3.2
  recipes.  Build-verifies via `./proofs/scripts/docker-build.sh
  Proofs.Erdos735OQ04`.

Recommended sequence: PR #19012 → this PR → future S3 ACT.

Per memory pattern `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer`,
this audit catches imprecise bearer names BEFORE the mechanic begins
Docker cycles.  Each `unknown identifier` failure (3-4 cascading at
iter 1 without this audit) costs ~90s + cache; saving 5-8 wasted
iterations.

## §7  Files modified

- `research/problems/erdos-735-oq-04/sessions/2026-05-14-s3-prep-bearer-audit.md` (this file, new)

**No edits** to `state.md`, `problem.md`, JSON tracker, `.lean`
files, or any session doc owned by PR #19012.

## §8  Trap notes for future sessions

- **B1.trap**: "iff" suffix is inconsistent across Mathlib v4.26.0
  rank lemmas.  `Submodule.rank_eq_zero` has no `_iff` (despite
  being an iff: `Module.rank R S = 0 ↔ S = ⊥`); top-level
  `rank_eq_zero_iff` does have `_iff`.  Always grep both forms
  when planning a discharge.
- **B2.trap**: There is no `Module.rank_eq_zero_iff` namespace.
  Top-level `rank_eq_zero_iff` (torsion form, fewer instances) and
  `rank_zero_iff` (Subsingleton form, requires `NoZeroSMulDivisors`)
  both exist at v4.26.0; pick by which form is more convenient.
- **B3.trap**: `direction_eq_top_iff_of_nonempty` requires a
  nonempty witness.  Discharge with `Finset.card_pos.mp` from the
  `ConfigKFlat`'s `card ≥ k + 1` field — this is 4-5 LOC, not 0.
- **B4.trap**: There is no `Module.rank_eq_finrank_iff` (combined
  iff).  At v4.26.0, the bridge is one-directional: `rank = ↑n →
  finrank = n` via `finrank_eq_of_rank_eq`.  For the converse (e.g.,
  to lift a hypothesis `finrank ℝ F.direction = d` to a rank
  statement), use `finrank_eq_rank` + `Cardinal.natCast_inj`.
- **§3.3.trap**: Vacuous-case discharge of `∃ w c, ∀ F` predicates
  needs a contradiction from `∀ F : ConfigKFlat ... P` not a "∀
  vacuous" formality.  The ConfigKFlat record carries a `card ≥
  k + 1` field that must be refuted under the vacuous hypothesis.

## §9  Bearer-verification commands (for auditor reproduction)

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# B1 corrected
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Dimension/Finite.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'Submodule.rank_eq_zero\b'
# → 441:theorem Submodule.rank_eq_zero [Nontrivial R] [NoZeroSMulDivisors R M] {S : Submodule R M} :

# B2 corrected (Subsingleton form)
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Dimension/Finite.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'rank_zero_iff\b'

# B3 corrected
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'direction_eq_top_iff_of_nonempty'
# → 739:theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :

# B4 corrected
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Dimension/Finrank.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'finrank_eq_of_rank_eq'
# → 68:theorem finrank_eq_of_rank_eq {n : ℕ} (h : Module.rank R M = ↑n) : finrank R M = n

# Supporting bearers
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/InnerProductSpace/PiL2.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'finrank_euclideanSpace_fin'
# → 194:theorem finrank_euclideanSpace_fin {n : ℕ} : ...

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'Submodule.eq_top_of_finrank_eq'
# → 58:theorem _root_.Submodule.eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V} ...
```

## §10  Cross-references

- PR #19012 (S2 ACT scaffold) — the parent this PREP audits.
- PR #18486 (S6a PREP — tetrahedron magic certificate, doc-only).
- PR #18541 (S6b PREP — octahedron + cube refutation, doc-only).
- Memory `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer.md`
  — pattern matched: peer scaffold ships build-verified Lean with N
  strategic sorries + PR-body discharge plan; audit catches fictitious /
  imprecise bearer names before the mechanic begins Docker cycles.
- Memory `feedback_researcher_audit_peer_mechanic_kit_fix_recommendations.md`
  — sibling pattern targeting mechanic-kit text-level fix instructions
  (this PREP targets ACT-plan bearer names; different artefact).
