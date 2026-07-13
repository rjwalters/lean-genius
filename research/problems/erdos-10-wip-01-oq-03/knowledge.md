# Knowledge Base: erdos-10-wip-01-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-04 (Session 1, Researcher-5) — Covering-method reduction for S_k

**Mode**: FRESH · **Outcome**: progress (Lean written, 0 sorries by construction) — BUILD UNVERIFIED (host Docker/containerd corruption + disk 100%).

### What I did
- Surveyed the rich existing Erdős #10 machinery: `Erdos10OQ02` (`IsPrimePlusKPowers`, `RepWithAtMost`, `powSum`), `Erdos10WIP01` (popcount characterization `isPrimePlusKPowers_iff_popcount`, `popcount_le_iff`), and the covering-congruence files `Erdos10OQ01Incomplete01` (`prime_forced_small`, `coveringPrimes`, the six-modulus system) + `Erdos10Incomplete01OQ02` (even-case parity, `family`, `family_props`, `coveringPrimes_odd/le`).
- Wrote `proofs/Proofs/Erdos10WIP01OQ03.lean` (branch `research/erdos-10-wip-01-oq-03-covering-reduction-r5`):
  - `not_isPrimePlusKPowers_iff` — for **all k**: `¬IsPrimePlusKPowers k n ↔ ∀ w≤n, popcount w≤k → ¬(n−w).Prime`. The covering-method reduction (re-index `isPrimePlusKPowers_iff_popcount` by offset `w=n−p`).
  - `eq_two_pow_of_pos_of_popcount_le_one`, `not_isPrimePlusKPowers_of_even` (w=0 offset free for even n>2).
  - `not_isPrimePlusKPowers_one_of_even_covering` + `infinite_even_not_isPrimePlusKPowers_one` — reproduce infinitely-many-even-∉-S_1 natively in the `IsPrimePlusKPowers` predicate via `prime_forced_small`.

### Key findings
- The covering method's real target, for every k, is: *for each ≤k-bit offset w≤n, n−w is composite.* That is `not_isPrimePlusKPowers_iff`.
- **Barrier (honest):** the elementary k=1 covering controls only single powers (`q ∣ n−2^a`); it says nothing about `n−(2^a+2^b+2^c)`. So the literal OQ target (infinitely many even n ∉ S_3) needs a Crocker-type k=3 covering — deep, out of reach of a single session. Seeker tractability=5 overestimates the literal target; the *reduction skeleton* is what was tractable.

### Blocker (infrastructure, not math)
Docker Desktop VM storage corrupted this session: `meta.db` / `metadata_v2.db` `input/output error`, filesystem remounted read-only; host `/System/Volumes/Data` at ~100%. `docker-build.sh` fails at the image-build step. Could not machine-verify. File committed to the branch; **no PR opened** (avoid merging an unverified Lean file).

### Next steps
1. Re-run `docker-build.sh Proofs.Erdos10WIP01OQ03` once Docker/disk healthy → then open the research PR.
2. Toward even-S_2: axiomatize Crocker 1971 and derive via `not_isPrimePlusKPowers_of_even` with a two-power offset obstruction; or attempt a two-power covering.
3. Small bridge lemma: `sumPrimeAndTwoPows k = {n | IsPrimePlusKPowers k n}` to unify the two threads.
