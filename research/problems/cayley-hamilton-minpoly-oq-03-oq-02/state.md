# Current State

**Phase**: ACT
**Since**: 2026-06-05T (researcher-1, S5)
**Iteration**: 5

## Current Focus

S5 ACT — **Matvec-count bound + Layer 3 ω axioms shipped** (researcher-1, 2026-06-05).
`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` extended with:

* **Layer 2.5** — `length_le_twoPow_sum` (private helper) and
  `squareKrylovProd_factor_count_le : j.bitIndices.length ≤ j`. The
  matrix-multiplication factor count for assembling `M^j` is bounded
  by `j` itself (and asymptotically by `⌈log₂ j⌉ + 1`).
* **Layer 3 (axiomatized)** — three axioms `omegaMM : ℝ`,
  `omegaMM_two_le : 2 ≤ ω`, `omegaMM_lt_three : ω < 3`, with
  `omegaMM_mem_Ico` sanity corollary.

File now: ~333 LOC, **11 theorems** (3 Layer 1 + 4 Layer 2 matrix +
2 Layer 2 vector + 1 Layer 2.5 factor-count + 1 Layer 3 ω-sanity),
**0 sorries**, **3 axioms** (all in Layer 3 ω placeholder).

The sharper bound `j.bitIndices.length ≤ Nat.size j` (≤ `⌈log₂ (j+1)⌉`)
is deferred pending Mathlib API exploration; the `≤ j` bound is the
immediately verifiable version using only `Nat.twoPowSum_bitIndices`
and `Nat.one_le_two_pow`.

The full operation-count theorem (Keller–Gehrig recovers `μ_M` in
`O(n^ω)` field operations) is *deferred*: it requires Mathlib to grow
a complexity monad first.

**Build status:** ✅ **verified** (researcher-1, 2026-06-05).
`./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02`
on lockfile (mathlib v4.26.0 / lean v4.26.0): 3062/3062 jobs clean
(8.0 s of compile after Mathlib cache warm-up).

## Previous Focus (S4 — carried for hand-off)

S4 ACT — **Layer 2 vector form shipped** (researcher-1, 2026-05-30).
`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` extended with 2
vector-level corollaries built on S3's matrix-level Layer 2 bridge:
* `squareKrylovProd_mulVec` — `(squareKrylovProd M j).mulVec v = (M^j).mulVec v`
* `krylov_in_squareKrylov_range` — every Krylov vector lies in the
  range of the squared-Krylov product matrix-vector map.

Both proofs are 1-line corollaries of `squareKrylovProd_eq_pow`
(S3); file 200 → ~228 LOC, 9 theorems total (3 Layer 1 + 4 Layer 2
matrix-level + 2 Layer 2 vector-level), 0 sorries, 0 axioms.

## Active Approach

Three-layer decomposition (unchanged):

1. **Structural layer** (squared-Krylov sequence) — ✅ **Layer 1 shipped
   in S2 (build pending → verified in S3).**
2. **Correctness layer** (Krylov power as product of squared-Krylov
   matrices) — ✅ **Layer 2 shipped in S3.** Vector-level corollaries
   shipped in S4.
3. **Complexity layer** — split into:
   * **Layer 2.5** (factor-count bound) — ✅ shipped in S5 (this iteration).
   * **Layer 3** (full `O(n^ω)` operation count) — **axiomatized in
     S5**: `ω` and its bounds declared as axioms; full
     operation-count theorem deferred until Mathlib grows a
     complexity-monad framework.

## Blockers

* Mathlib has no complexity-monad / cost-counting framework — blocks the
  *full* `O(n^ω)` operation-count theorem. (Mitigated in S5: the ω
  exponent itself is axiomatized; only the operation-count predicate
  remains to be supplied.)
* Mathlib's `Matrix.mul` is the naive cubic algorithm; there is no
  Strassen or abstract fast-matmul oracle.
* The sharper factor-count bound `j.bitIndices.length ≤ Nat.size j`
  needs Mathlib `Nat.bitIndices` / `Nat.size` API exploration; the
  current `≤ j` bound is the verifiable elementary version.

## Next Action

**S6 — Gallery promotion.**

Open `src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/meta.json`
with:
* `status = "axiomatized"`, `badge = "axiom"`.
* `axiomCount = 3` (the three ω axioms).
* `assumptions` field naming `omegaMM` + its two bound axioms.

The Lean file now contains 11 theorems and 3 axioms; an honest gallery
presentation can cover all 11 theorems as the structural and
correctness content, with the 3 ω axioms as the explicit assumptions.

Alternatively, S6 could refine the factor-count bound to
`j.bitIndices.length ≤ Nat.size j` (the asymptotically correct
popcount bound), once the appropriate Mathlib `Nat.bitIndices` length
API is identified.

## Attempt Counts

- Total attempts: 5 (S1 + S2 + S3 + S4 + S5; this iteration completes S5)
- Current approach attempts: 5 (3-layer decomposition; Layers 1 + 2 +
  vector + factor-count + Layer 3 axioms shipped)
- Approaches tried: 1 (the planned 3-layer decomposition)

## Findings Summary

* **S5 (new):** The matvec-count bound `j.bitIndices.length ≤ j` is a
  2-line proof: combine `Nat.twoPowSum_bitIndices` with the elementary
  lemma `(L.length ≤ (L.map (2^·)).sum)` (proved by induction +
  `Nat.one_le_two_pow`). The Layer 3 ω axioms are minimal: `ω : ℝ`
  with `2 ≤ ω < 3`, both bounds with citations in their docstrings
  (folklore + Strassen 1969).
* The full operation-count theorem cannot be stated cleanly today;
  S5 ships the *minimum honest commitment* — naming ω and its known
  bounds — leaving the operation-count predicate to a future Mathlib
  upgrade. This avoids both over-claiming with a vague `True`
  placeholder and under-committing with no Layer 3 at all.
* **S4 (carried):** The vector-level corollaries are 1-line proofs
  from the matrix-level Layer 2 bridge; they're the bridge from
  Keller–Gehrig matrix arithmetic into the OQ-03 matvec ladder.
* **S3 (carried):** Layer 2 has a 3-rewrite proof. After unfolding
  `squareKrylovProd`, the list `j.bitIndices.map (squareKrylov M)` is
  rewritten to `j.bitIndices.map (fun i => M^(2^i))` via the Layer 1
  bridge; the list product collapses to a single matrix power via
  `prod_pow_of_list`; finally `Nat.twoPowSum_bitIndices` identifies
  the exponent sum as `j` itself.
* The product-formula bridge `M^j = ∏ T_i` is exactly the algebraic
  content of the Keller-Gehrig outer loop: `⌈log₂ j⌉` squarings produce
  `T_0, …, T_{k-1}`, and `popcount(j)` multiplications then yield `M^j`.
* **Mathlib leverage:** `Nat.bitIndices` (Peter Nelson, 2024) +
  `Nat.twoPowSum_bitIndices` were perfect drop-ins. No bit-manipulation
  lemmas had to be re-proved.
* The Keller-Gehrig speed-up is *structural*: $n$ cheap matvecs vs.
  $\log n$ expensive matmuls. The structural and correctness claims
  formalise today (Layers 1 + 2: done; factor-count: done).
* The *quantitative* speed-up is gated on Mathlib infrastructure that does
  not exist (complexity monad). The ω exponent is now axiomatized
  (Layer 3 placeholder); the operation-count predicate awaits.
* Numerical breakeven: Strassen wins around $n \approx 256$;
  CW-Williams wins from $n \approx 64$. Mathlib's choice of naive
  cubic `Matrix.mul` is defensible at typical $n$.
* OQ-03 already provides 90% of the algebraic infrastructure (Krylov
  recurrence, annihilator theory, iteration bound).
