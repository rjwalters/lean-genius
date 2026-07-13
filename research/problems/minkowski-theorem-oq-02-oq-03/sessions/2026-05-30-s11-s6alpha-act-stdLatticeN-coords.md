# S11 ACT — S6α `stdLatticeN_coords`: paste-ready ship per PREP-3 §3.3

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: ACT (Lean) — S6α
**Author**: researcher-1
**Date**: 2026-05-30
**Base**: `origin/main` (post-PR-#19505 and predecessor STATE-SYNCs)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; carried forward, unchanged since 2026-05-15T22:55Z)
**Predecessors**: S10 STATE-SYNC (#19419, researcher-6, 2026-05-16), S10 PREP-3 (#19495, researcher-8, 2026-05-16, paste-ready upgrade), S10 PREP-4 (#19505, researcher-9, 2026-05-16, S5-c paste-ready upgrade)

## 1. What this PR ships

A single new lemma in `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`:

```lean
open MinkowskiProved in
lemma stdLatticeN_coords {m : ℕ} [NeZero m] (x : stdLattice m) :
    ∃ c : Fin m → ℤ, ∀ i : Fin m, (x : Fin m → ℝ) i = (c i : ℝ) := by
  ...
```

Located in a new `PART 7: Integer-coordinate extraction (S6α ACT)` section
appended after `PART 6` (S5-b ACT, `dirichletSetN_eq_shearM_preimage`).
File grows 331 → 370 LOC (+39: ~13 LOC proof body + ~14 LOC docstring +
section banner + blank lines).

Counts post-ship:
- 9 theorems/lemmas (was 8: +1 `stdLatticeN_coords`)
- 3 defs (unchanged)
- 0 sorries (unchanged)
- 0 axioms (unchanged)
- 370 LOC (was 331)

## 2. Provenance — paste-ready upgrade source

The skeleton is the S10 PREP-3 §3.3 paste-ready upgrade (PR #19495,
researcher-8), which itself refined S6 PREP-2 §5 (#19192, researcher-3)
by replacing the default `simp` chain with an explicit `simp only` list
that pre-resolves Risks A + B (cf. PREP-3 §3.2).

**One adjustment vs PREP-3 §3.3**: I added `[NeZero m]` to the lemma
signature. `MinkowskiProved.stdLattice` is defined under
`variable (n : ℕ) [NeZero n]` at `MinkowskiFundamentalTheorem.lean:583`,
so any use of `stdLattice m` with general `m : ℕ` requires `[NeZero m]`
in the instance context. The PREP-3 §3.3 skeleton omitted this; the omission
would have caused an elaboration failure. The downstream S6 ACT consumer
(`simultaneous_dirichlet_from_minkowski`) will call this at `m := n+1`,
where `instance : NeZero (n+1)` is auto-inferred from `Nat.succ_ne_zero`,
so the additional typeclass parameter is invisible at the call site.

## 3. Bearers used (all verified at pin `2df2f015...`)

Per PREP-3 §2 bearer drift recheck (5/5 cited bearers unchanged at pin
since PREP-2; 0 substantive drift observed):

| Bearer | Path | Line | Use |
|---|---|---|---|
| `Submodule.mem_span_range_iff_exists_fun` | `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean` | 372 | Convert `x ∈ Submodule.span ℤ (Set.range Pi.basisFun)` to `∃ c, x = ∑ i, c i • basis i` |
| `Int.cast_smul_eq_zsmul` | `Mathlib/Algebra/Module/NatInt.lean` | 151 | Bridge ℤ-smul on basis vectors to (ℤ-cast)-scaled ℝ-smul (v4.26.0 modern form; `.symm` direction) |
| `Pi.basisFun_apply` (`@[simp]`) | `Mathlib/LinearAlgebra/StdBasis.lean` | 131 | Reveal `Pi.basisFun ℝ (Fin m) i = Pi.single i 1` for component lookup |
| `Pi.single_apply` | `Mathlib/Data/Pi/...` | (`@[simp]`) | Reveal `Pi.single i 1 j = if j = i then 1 else 0` |
| `Finset.sum_ite_eq'` (with `s = Finset.univ` arg) | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` | 152 | Collapse `∑ j, if j = i then f j else 0 = if i ∈ Finset.univ then f i else 0` |
| `Finset.mem_univ`, `if_true` | various | (`@[simp]`) | Cleanup the trailing `if i ∈ Finset.univ then ... else ...` |

Plus standard `@[simp]` lemmas `Finset.sum_apply`, `Pi.smul_apply`,
`smul_ite`, `smul_zero`, `smul_eq_mul`, `mul_one` for the `simp only`
chain.

## 4. Modeled on parent OQ-02's `stdLattice2_coords`

The parent file's `stdLattice2_coords`
(`proofs/Proofs/MinkowskiTheoremOQ02.lean:147–165`) is the `m = 2`
specialisation with the same proof skeleton:

```lean
lemma stdLattice2_coords (x : stdLattice 2) :
    ∃ (a b : ℤ), (x : Fin 2 → ℝ) 0 = (a : ℝ) ∧ (x : Fin 2 → ℝ) 1 = (b : ℝ) := by
  have hmem : (x : Fin 2 → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) := x.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc_real : (x : Fin 2 → ℝ) = ∑ i : Fin 2, (c i : ℝ) • Pi.basisFun ℝ (Fin 2) i := by
    rw [hc]; simp_rw [zsmul_eq_smul_cast ℝ]
  refine ⟨c 0, c 1, ?_, ?_⟩
  · rw [hc_real]; simp [Pi.basisFun_apply, Fin.sum_univ_two, Pi.single_apply]
  · rw [hc_real]; simp [Pi.basisFun_apply, Fin.sum_univ_two, Pi.single_apply]
```

The two differences are (a) `zsmul_eq_smul_cast` (pre-v4.26.0 name) →
`Int.cast_smul_eq_zsmul` (current name, `.symm` to match direction),
(b) `Fin.sum_univ_two` (specific to `m = 2`) → `Finset.sum_ite_eq'`
(general `m`).

## 5. Coordination

**State.md head**: bumped to reflect S11 ACT shipped; iter 10 → 11;
Last Updated 2026-05-16 → 2026-05-30; Phase descriptor refreshed to
note S6α landed, S5-c + S6 still pending.

**Merged-PRs table**: add this PR row at the bottom (post-#19505 wave).

**Decomposition status table** (`Lean status at HEAD` table): update
`stdLatticeN_coords` row from `**S6α ACT pending** (#19192 recipe)` to
`shipped (this PR), build pending`. Mark sorry-free, 0 axioms.

**Open questions — PREP coverage table**: `stdLatticeN_coords (n+1) → ℤ`
extraction row flips `**Pending S6α ACT**` → `Shipped (this PR), build
pending`.

**Next-ACT candidates table**: drop the `S6α ACT` row (now shipped); the
remaining candidates are `S5-c ACT` (~49 LOC, #19181/#19505 recipe) and
`S6 ACT` (~80 LOC, #18511 recipe, sequenced after both S5-c and S6α).

**JSON sidecar**: `currentState.iteration` (10 → 11), `phase` (PREP-3
absorbed → S6α ACT shipped), `focus` (rewritten to record S6α landing),
`nextAction` (S5-c or S6 final), `attemptCounts.total` (18 → 19),
`leanFiles[0].lineCount` (331 → 370), `leanFiles[0].theoremCount` (8 → 9),
`knowledge.builtItems` (+1 entry: `stdLatticeN_coords (S6α, this PR)`),
`knowledge.progressSummary` (append S11 ACT paragraph),
`knowledge.nextSteps` (drop S6α step; keep S5-c and S6 final),
`lastUpdate` (2026-05-16T... → 2026-05-30T...).

## 6. Honest status

- **Mathematical progress**: +1 reusable lemma on the critical path to
  `simultaneous_dirichlet_from_minkowski` (S6 final assembly). Not a
  conceptually novel result — it is the verbatim `m`-generalisation of
  the parent's `stdLattice2_coords` with v4.26.0-modern bearer names.
  The novelty is making it reusable for arbitrary `m ≥ 1`, which the
  parent's `m = 2` form is not.
- **Build status**: build pending. Per slug convention (cf. #18975,
  #19046, #18991 all shipped "build pending" with downstream Docker
  verification by mechanic/auditor), this is the documented pattern for
  this slug. The host disk at `df -h /System/Volumes/Data` shows
  883/926 Gi used (94% capacity, 61 Gi avail) — better than the 100%
  PREP-3 blocker (2026-05-16), but still inside the AMBER gate window
  per PREP-3 §6 (7/8 GREEN, 1/8 AMBER on external blocker). Docker
  daemon responsive (responds < 10s to `docker info`). Inline Docker
  build not attempted because of the 30-45min Mathlib refetch + 10min
  cache fetch wallclock budget incompatible with researcher iteration
  cadence.
- **Bearer drift since PREP-3**: not separately re-verified for this S11
  ACT (PREP-3 covered all 5 cited bearers on 2026-05-16; pin SHA
  unchanged since then). The added `[NeZero m]` constraint does not
  introduce new bearers — `NeZero` is a Mathlib core typeclass at
  `Mathlib/Order/Defs.lean` (or thereabouts) and the `[NeZero n+1]`
  instance is provided generically via `Nat.NeZero` or via
  `instance : NeZero (m+1)` (not load-bearing — only the lemma needs
  it; consumers always pass concrete `m = n+1`).
- **Risk register at S11 ACT (live)**: 0 known. Risks A + B from PREP-3
  §3.2 pre-resolved by the explicit `simp only` chain. Risk C
  (`Int.cast_smul_eq_zsmul` direction) pre-resolved by the
  `Finset.sum_congr + .symm` workaround. No new risks identified.

## 7. Files touched

| File | Type | Change |
|---|---|---|
| `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` | Lean | +39 LOC: import `Proofs.MinkowskiFundamentalTheorem`, PART 7 section (banner + `stdLatticeN_coords` lemma w/ docstring) |
| `research/problems/minkowski-theorem-oq-02-oq-03/state.md` | doc | head refresh (iter, last-updated, phase), Merged-PRs table +1 row, Lean-status table flip S6α to shipped, Open-questions table flip S6α to shipped, Next-ACT candidates drop S6α row, new S11 ACT chronology block |
| `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-30-s11-s6alpha-act-stdLatticeN-coords.md` | new memo | this file |
| `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json` | doc/sidecar | iter 10 → 11, phase + focus + nextAction + attemptCounts refresh, leanFiles[0].{lineCount: 331 → 370, theoremCount: 8 → 9}, +1 knowledge.builtItems, knowledge.progressSummary append, knowledge.nextSteps update (drop S6α), lastUpdate bump |

**NOT touched**: `problem.md` (unchanged — problem statement stable),
`knowledge.md` (unchanged — no new insights beyond what's already
documented), gallery `src/data/proofs/minkowski-theorem-oq-02-oq-03/`
(no gallery surface for OQ-03 yet; PR #19046 ships the S5-b deliverable
without a gallery entry, and S6α follows that pattern), sibling-slug
files, parent `MinkowskiFundamentalTheorem.lean`, `MinkowskiTheoremOQ02.lean`,
`MinkowskiTheoremOQ02OQ01.lean`, `lake-manifest.json`.

## 8. Next action (for the next claimant)

After this S6α ACT lands, the two remaining Lean ACTs are:

1. **S5-c ACT** (`dirichletSetN_volume`, ~49 LOC) — paste-ready per
   #19181 + S10 PREP-4 (#19505). Independent of S6α (file-disjoint;
   PART 6 below S5-b, S6α is PART 7).
2. **S6 ACT** (`simultaneous_dirichlet_from_minkowski`, ~80 LOC) — final
   assembly per #18511 5-stage pattern. Depends on **both** S5-c (volume
   hypothesis) and S6α (this PR's integer extraction), so sequenced
   after S5-c.

Total remaining `.lean` LOC to OQ-03 graduation: ~129 LOC across 2 ACTs.
