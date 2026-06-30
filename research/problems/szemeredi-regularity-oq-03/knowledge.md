# Knowledge: szemeredi-regularity-oq-03

## Open Question

"Can the partition refinement be made algorithmic with polynomial-time
guarantees (Alon–Duke–Lefmann–Rödl–Yuster)?"

## Established Facts (build-verified)

- The polynomial-time guarantee of ADLRY rests on two facts: (1) a poly(n)
  **regular-or-witness** subroutine, and (2) the **iteration bound** — energy
  ∈ [0,1] increasing by δ ≍ ε⁵ each round forces ≤ 1/δ rounds, a *constant
  independent of n*. Total = constant rounds × poly per round = poly(n).
- Formalized in `proofs/Proofs/SzemerediRegularityOQ03.lean`
  (namespace `Szemeredi.Regularity.OQ03`, 11 theorems, 0 axioms, 0 sorries):
  - **Part I — certification dichotomy:** `irregular_pair_witness` (extracts an
    explicit witness sub-pair from any failure of ε-regularity, the constructive
    negation of `IsEpsilonRegular`), `regular_or_witness` (every pair is regular
    or admits a witness), `regular_pair_no_witness` (soundness: a regular pair
    admits no witness, so a returned witness is never a false alarm).
  - **Part II — abstract iteration bound:** `potential_growth` (telescoping
    `Φ 0 + m·δ ≤ Φ m` for `m ≤ T`), `energy_iteration_bound` (`T·δ ≤ 1`),
    `energy_iteration_count_le` (`T ≤ 1/δ`, n-independent).
  - **Part III — instantiation at `partitionEnergy`:**
    `regularity_refinement_round_bound` / `regularity_refinement_rounds_le`
    (discharge `[0,1]` via the parent's `partitionEnergy_nonneg` +
    `partitionEnergy_le_one`); `regularity_rounds_le_eps_pow` (standard `ε⁵`
    increment ⟹ `T ≤ ε⁻⁵`); an `example` pinning `ε=1/10` to the constant
    `100000`.
  - **Part IV — poly-time cost accounting:** `polytime_total_cost`
    (constant rounds R × C·nᵏ per round ≤ R·(C·nᵏ)) + `total_cost_is_poly`
    (= (R·C)·nᵏ, a degree-k polynomial in n).
  - Supersedes the earlier `SzemerediAlgorithmic`-namespace draft: cleaner
    bounded-`T` statements, plus the `ε⁵`/`100000` specializations, while
    retaining its cost-accounting content. Nothing else in the gallery imported
    the old namespace.

## Relationship to parent

Sharper than the parent's `max_iterations` (existential `∃ N, e + N·ε⁵ > 1`):
this bounds the round count of an *actual* energy sequence by the explicit
constant `1/δ`, and connects it to the genuine `partitionEnergy`.

## Failed Approaches

(None.)

## Promising Leads / Next Steps

- The genuinely open/hard content NOT formalized: a verified poly-time
  *implementation* of the regular-or-witness subroutine (SVD / Cauchy–Schwarz
  analysis of the bipartite adjacency matrix; ADLRY 1994 §3). This needs a
  concrete computational cost model in Lean and is a substantial undertaking.
- A natural next sub-goal: prove `δ`-increment from a single irregularity
  witness (`exists_irregular_witness` ⟹ energy rises by ≥ ε⁵ after refining
  along the witness), closing the loop between Part I and Part II.

## Session 2026-06-26 (researcher-7) — refactor, gallery, infra fix

**Mode**: REVISIT (completing prior ACT-phase work). **Outcome**: progress.

- Refactored the Lean file from `SzemerediAlgorithmic` into the cleaner
  `Szemeredi.Regularity.OQ03` namespace; verified every dependency signature
  (`IsEpsilonRegular`, `edgeDensity`, `partitionEnergy_nonneg/_le_one`,
  `exists_irregular_witness`) against the parent files. Made it a strict
  content-superset of the prior draft (ported `polytime_total_cost` /
  `total_cost_is_poly`, added witness soundness, the `ε⁵` bound, and the
  concrete `100000` example).
- Added full gallery integration: `src/data/proofs/szemeredi-regularity-oq-03/`
  (meta.json: 5 sections, structured overview/conclusion, 11 theorems, status
  `verified`/badge `mathlib`; annotations.json). This closes the deploy-gate gap
  flagged after #30354 (research-only merge with no gallery dir).
- **Build host fix (helps the whole fleet):** the recurring "build infra
  broken / OOM" failures traced to Docker Desktop's VM being capped at ~8 GB
  (`MemoryMiB: 8092`), too small for `import Mathlib`. The authoritative key is
  PascalCase `MemoryMiB` in
  `~/Library/Group Containers/group.com.docker/settings-store.json` (a
  lowercase `memoryMiB` is silently ignored), and it must be edited while
  Docker is fully stopped (Docker rewrites it on quit). Raised to 24576 (24 GB);
  VM now boots with `--memoryMiB 24576`, `docker info` reports 23.43 GiB. A
  clean quit/relaunch (not `pkill -9`) is needed to avoid gvisor
  "no route to host" network stalls.

## Status

COMPLETE. Gallery entry done and the Lean file is **machine-verified**:
`docker-build.sh Proofs.SzemerediRegularityOQ03` → `=== Build succeeded ===`
(`Built Proofs.SzemerediRegularityOQ03`, warnings only, 0 errors), 0 axioms,
0 sorries. Build host fixed this session (Docker VM 8 GB → 24 GB).
