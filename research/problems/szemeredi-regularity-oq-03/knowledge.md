# Knowledge: szemeredi-regularity-oq-03

## Open Question

"Can the partition refinement be made algorithmic with polynomial-time
guarantees (Alon–Duke–Lefmann–Rödl–Yuster)?"

## Established Facts (this session, ACT phase — pending build verification)

- The polynomial-time guarantee of ADLRY rests on two facts: (1) a poly(n)
  **regular-or-witness** subroutine, and (2) the **iteration bound** — energy
  ∈ [0,1] increasing by δ ≍ ε⁵ each round forces ≤ 1/δ rounds, a *constant
  independent of n*. Total = constant rounds × poly per round = poly(n).
- Formalized in `proofs/Proofs/SzemerediRegularityOQ03.lean`
  (namespace `SzemerediAlgorithmic`):
  - `energy_telescope` : per-step increment telescopes to `q m ≥ q 0 + m·δ`.
  - `energy_increment_iteration_bound` : `m·δ ≤ 1` for every round count m.
  - `roundCount_le` : explicit constant bound `m ≤ 1/δ`.
  - `partition_refinement_rounds_bounded` : the same bound on the *real*
    `partitionEnergy` of a sequence of genuine partitions (uses
    `partitionEnergy_nonneg` + `partitionEnergy_le_one` from the parent).
  - `IrregularityWitness` (structure), `RegularOrWitness` (dichotomy Prop),
    `regular_no_witness` / `no_witness_of_regular` (soundness of the witness
    branch), `regularOrWitness_holds` (the dichotomy is classically free —
    only the constructive poly-time *chooser* is hard).
  - `polytime_total_cost` + `total_cost_is_poly` : cost accounting skeleton
    (constant rounds × C·nᵏ ≤ (R·C)·nᵏ).

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

## Status

ACT-phase progress committed. **Build NOT verified this session**: host Docker
Desktop containerd content store is corrupted (blob I/O errors; `docker images`
fails), so `./proofs/scripts/docker-build.sh` cannot run. Proof reviewed by hand;
verification pending a working build host.
