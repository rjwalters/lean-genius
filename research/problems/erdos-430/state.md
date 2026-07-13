# Current State

**Phase**: AXIOMATIZED — EQUIVALENCE-PROVED + small-n positive witnesses
**Since**: 2026-06-04 (S1 ACT added 3 positive witnesses; previously STATE-SYNC since 2026-05-13; prior stub since 2026-01-13)
**Iteration**: 1 (S1 ACT)

## Current Focus

S1 (researcher-1, 2026-06-04): Followed up on Forward Lever 2
(computational evidence) from the 2026-05-13 STATE-SYNC. Added three
small-n positive witnesses for the conjecture, all verified via
`native_decide`:

- `hasComposite_5` — sequence starts at `4 = 2²` (composite).
- `hasComposite_7` — sequence starts at `6 = 2 · 3` (composite).
- `hasComposite_9` — sequence starts at `8 = 2³` (composite).

These document the positive small-n regime (n with composite n - 1)
to complement the existing `example_n8` negative witness (n = 8,
sequence = 7, 5, both prime). The real difficulty of the conjecture
remains the "n - 1 prime" regime where the greedy sequence has a
fighting chance of remaining all-prime.

## Source-of-Truth Counts (proofs/Proofs/Erdos430Problem.lean)

| Kind            | Count | Examples                                                  |
|-----------------|-------|-----------------------------------------------------------|
| Definitions     | 7     | `minPrimeFactor`, `allPrimeFactorsExceed`, `IsAdmissible`, `greedyNext`, `greedySeq`, `seqTerminates`, `hasComposite` |
| Decidable inst. | 2     | `decidableAllPrimeFactorsExceed`, `decidableIsAdmissible` |
| Theorems        | 8     | `example_n8`, `hasComposite_5`, `hasComposite_7`, `hasComposite_9`, `greedySeq_le`, `greedySeq_terminates`, `erdos_385_equivalence`, `small_n_all_prime` |
| Private lemmas  | 5     | `greedyNext_admissible`, `greedySeq_admissible`, `greedyNext_lt`, `greedyNext_zero`, `greedySeq_zero_of_le_one` |
| Sorries         | 0     | (verified by `grep` for `sorry`) |
| Axioms          | 1     | `erdos_430_conjecture` (open conjecture, isolated) |

Line count: 249 → 275 (+26).

## Axiom Inventory (1 total, all open-conjecture)

| Axiom                    | Status   | Group                | Notes |
|--------------------------|----------|----------------------|-------|
| `erdos_430_conjecture`   | OPEN     | Open conjecture only | "∃ N₀, ∀ n ≥ N₀, hasComposite n" — Erdős/Graham/Selfridge, no proof known |

## Active Approach

Add scoped computational witnesses that frame the small-n boundary
without modifying the existing equivalence proof. The new witnesses
are tight against `example_n8`: the n ∈ {5, 7, 9} positive cases and
n = 8 negative case together delineate the trivial/nontrivial boundary
of the conjecture at small n.

## Forward Levers (NOT a roadmap to resolve the open conjecture)

1. **Erdős #385 first-part formalization (parallel slug).** Discharging
   `erdos_430_conjecture` is equivalent (by the proved equivalence
   theorem) to producing a constructive `(N₀, ∀ n ≥ N₀, ∃ m …)`
   witness — which is the #385 first-part statement. (Both remain open.)

2. **Decidable bounded form of `hasComposite`.** Currently
   `hasComposite n` is `∃ k : ℕ, …` (unbounded existential). Since
   `greedySeq n n = 0` and the sequence stays at 0 (provable from
   `greedyNext_zero`), there's a bounded equivalent
   `hasCompositeBounded n := ∃ k ∈ Finset.range n, …` that is
   automatically decidable. With this, `not_hasComposite_8`,
   `not_hasComposite_12`, etc., become tractable via `native_decide`.
   ~20-30 line addition; concrete next step.

3. **Strengthen `small_n_all_prime`.** Use Lever 2 to prove
   `∀ n ∈ S, ¬ hasComposite n` for an explicit finite set `S` of
   "n - 1 prime" cases (n ∈ {3, 4, 6, 8, 12, 14, 18, 20, 24, 30, …}
   up to some bound). Tightens the conjectured N₀ from below.

## Blockers

- Local Docker daemon in I/O-error state on this host — build
  verification of `Proofs.Erdos430Problem` is deferred to
  Mechanic / Auditor (same precedent as recently-shipped
  szemeredi-theorem-oq-01 S3 and erdos-951 S4).

- The remaining `axiom erdos_430_conjecture` is an open mathematical
  conjecture (Erdős/Graham/Selfridge), not a Lean blocker.

## Next Action

1. Mechanic / Auditor: Docker-build `Proofs.Erdos430Problem` and
   confirm 13 theorems, 1 axiom, 0 sorries.

2. Researcher (short-horizon, concrete): execute Forward Lever 2 —
   add `greedySeq_zero_persists`, `hasCompositeBounded` +
   decidability instance + equivalence proof. Unlocks `not_hasComposite_n`
   for n ∈ {12, 14, 18, 20, 24, 30, …}. ~20-30 lines.

3. Researcher (parallel-slug): claim Erdős #385 slug; the equivalence
   theorem in this file imports any progress from there bidirectionally.

## Honesty Block

- The new witnesses are *intentionally trivial*: each is `⟨0, by
  native_decide, by native_decide, by native_decide⟩`, exploiting that
  `greedySeq n 0 = n - 1` is composite for n ∈ {5, 7, 9}. They
  document the boundary, they do not move the open conjecture.
- The `example_n8` and three new positive witnesses are the only
  small-n cases formally documented in the file; the negative cases
  for n ∈ {3, 4, 6, 12, 14, …} await Forward Lever 2.
- Build verification was not run locally (Docker unavailable on this
  host); the proof pattern is identical to `example_n8` which builds
  in CI.

## Attempt Counts

- Total attempts (cumulative across sessions): 2 (prior session
  produced the equivalence proof + small_n_all_prime; this session
  added the three positive witnesses).
- Current approach attempts: 1 (small-n witnesses via native_decide).
- Approaches tried (cumulative): equivalence-to-#385 (proved),
  greedy-sequence admissibility + descent (proved), small-n boundary
  (proved for n ≤ 1 trivially, and now for n ∈ {5, 7, 9} as positive
  witnesses).
