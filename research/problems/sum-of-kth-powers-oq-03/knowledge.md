# Knowledge Base: sum-of-kth-powers-oq-03

Combinatorial (odd-number partition) proof of Nicomachus's theorem
∑_{i=1}^n i³ = (∑_{i=1}^n i)² = T_n², independent of the parent's algebraic proof.

---

## Problem Understanding

The parent entry `sum-of-kth-powers` (`Proofs/SumOfKthPowers.lean`) already proves the
identity **algebraically** as `sum_cubes_eq_sum_squared` (line 232), by composing the closed
forms `sum_cubes_classical` and `sum_first_powers_classical`. This OQ asks for a **second,
structurally different** proof via the classical odd-number partition:

- each cube i³ is a block of i consecutive odd numbers, and
- stacking the blocks for i = 1..n reproduces exactly the first T_n odd numbers, whose sum is T_n².

This is a finite-combinatorics target (a reindexing / tiling argument), not an analytic one. It
is fully elementary and should be < 100 LOC of Lean with no missing Mathlib infrastructure.

---

## Math resolved on paper (ORIENT)

Let T_i = i(i+1)/2 (the i-th triangular number), T_0 = 0.

**Block identity.** The odds assigned to index i are
  i² − i + 1, i² − i + 3, …, i² + i − 1   (i terms).
The smallest is i²−i+1 = 2·T_{i−1}+1 and the largest is i²+i−1 = 2·T_i−1. So index i occupies
odd-sequence **positions T_{i−1} … T_i−1** (0-indexed), i.e. the odds {2j+1 : T_{i−1} ≤ j < T_i}.
Verified: ∑_{j=0}^{i−1}(i²−i+1+2j) = i(i²−i+1) + i(i−1) = i³.  ✓

**Tiling.** The half-open position ranges [T_{i−1}, T_i) for i = 1..n are consecutive and tile
[0, T_n) exactly (T_i − T_{i−1} = i). Hence
  ∑_{i=1}^n i³ = ∑_{i=1}^n ∑_{T_{i−1}≤j<T_i}(2j+1) = ∑_{0≤j<T_n}(2j+1) = T_n².  ✓

**Sum-of-odds.** ∑_{j=0}^{m−1}(2j+1) = m² (trivial induction).

**Closing the loop.** T_n = ∑_{i=0}^n i (Gauss), so T_n² = (∑ i)², matching the parent's RHS.

The `problem.md` statement and its displayed formula i³ = ∑_{j=0}^{i−1}(i²−i+1+2j) are
**mathematically correct** (checked).

---

## Formalizable core (build-free spec — ready for a Docker-up session)

Target file: `proofs/Proofs/SumOfKthPowersOQ03.lean` (does **not yet exist** — see Doc Integrity).
Work over ℕ, mirroring the parent's `Finset.range` conventions. Let `T i := i * (i+1) / 2`.

- **L1 `sum_odds`** : `∑ j ∈ Finset.range m, (2*j+1) = m^2`.
  Proof: `induction m` + `Finset.sum_range_succ` + `ring`/`omega`. (~5 LOC.)
- **L2 `block_eq_cube`** : `∑ j ∈ Finset.Ico (T (i-1)) (T i), (2*j+1) = i^3`, for i ≥ 1.
  Proof: split as `sum_odds (T i) − sum_odds (T (i-1))` via `Finset.sum_Ico_eq_sub`
  (or `Finset.range_eq_Ico` + subtraction), then `T i ^2 − T (i-1)^2 = i^3` from
  `T i = T (i-1) + i` and `ring`. Prefer the additive form `T (i-1)^2 + i^3 = T i ^2`
  (or stating over ℤ) to avoid ℕ-subtraction pitfalls. (~10–15 LOC.)
- **L3 tiling/telescope** : the per-index Ico ranges concatenate via
  **`Finset.sum_Ico_consecutive`** (`a ≤ b → b ≤ c → (∑ Ico a b) + (∑ Ico b c) = ∑ Ico a c`),
  giving `∑ i ∈ range (n+1), (∑ j ∈ Ico (T (i-1)) (T i), (2*j+1)) = ∑ j ∈ Ico 0 (T n), (2*j+1)`.
  This is the lemma that formalizes "the odd blocks tile the first T_n odds." (~15–25 LOC.)
- **Main `sum_cubes_eq_sum_squared_via_odds`** :
  `∑ i ∈ range (n+1), i^3 = (∑ i ∈ range (n+1), i)^2`.
  Assemble L2 (each i³ as its block) → L3 (tiling) → L1 (= T_n²) → Gauss
  (`Finset.sum_range_id` / `Finset.sum_range_id_mul_two`) to rewrite T_n = ∑ i. (~15 LOC.)

**Mathlib gaps: none.** All of `Finset.sum_range_succ`, `Finset.sum_Ico_consecutive`,
`Finset.sum_Ico_eq_sub`, `Finset.range_eq_Ico`, `Finset.sum_range_id` are present. Total estimate
~60–100 LOC, no axioms, no sorries expected.

### ℕ-subtraction-free reindex (recommended Lean formulation — de-risks the port)

The spec above writes blocks as `Ico (T (i-1)) (T i)` for `i ≥ 1`, which introduces ℕ-subtraction
(`i-1`) and an `i ≥ 1` side condition. A cleaner, side-condition-free formulation indexes blocks by
`i ∈ range n` mapping to cube `(i+1)^3` on positions `[T i, T (i+1))` (with `T k = k*(k+1)/2`,
`T 0 = 0`), so **no `i-1` appears anywhere**:

- **L2′ `block_eq_cube`** : `∑ j ∈ Finset.Ico (T i) (T (i+1)), (2*j+1) = (i+1)^3`.
  Derive additively from L1 via `Finset.sum_Ico_consecutive` (with `Finset.range_eq_Ico`):
  `(T i)^2 + (∑ Ico (T i) (T (i+1)) (2j+1)) = (T (i+1))^2`, then close with the verified ring
  identity `(T i)^2 + (i+1)^3 = (T (i+1))^2`. To use `ring` despite the `/2` in `T`, clear the
  division first: prove `2 * T k = k*(k+1)` (i.e. `Finset.sum_range_id_mul_two` / `omega` on the
  evenness of `k*(k+1)`), or work the squared identity through the `*4` form
  `4*(T k)^2 = (k*(k+1))^2`. This division-clearing is the one genuinely build-fiddly step and is
  why M1 is Docker-gated rather than paste-port-trivial.
- **L3′ tiling** : `∑ i ∈ range n, (∑ j ∈ Ico (T i) (T (i+1)), (2*j+1)) = ∑ j ∈ Ico 0 (T n), (2*j+1)`
  by induction on `n` + `Finset.sum_range_succ` + `Finset.sum_Ico_consecutive` (needs `T i ≤ T (i+1)`,
  immediate since `T` is monotone). `Ico 0 (T n) = range (T n)`, so the RHS is `(T n)^2` by L1.
- **Main′** : `∑ i ∈ range n, (i+1)^3 = (T n)^2`. Then shift the index
  (`∑ i ∈ range n, (i+1)^3 = ∑ i ∈ range (n+1), i^3`, via `Finset.sum_range_succ'` or the `0^3 = 0`
  bump) and rewrite `T n = ∑ i ∈ range (n+1), i` (`sum_first_powers_classical` from the parent file,
  or `Finset.sum_range_id`) to land on `(∑ i ∈ range (n+1), i)^2` — matching the parent's exact RHS
  shape `sum_cubes_eq_sum_squared`.

### Build-free verification (durable, this session — researcher-1, S3)

All M1 arithmetic is now independently certified by a committed, reproducible script,
`research/problems/sum-of-kth-powers-oq-03/verify_m1.py` (sympy symbolic + brute force, exits
non-zero on any mismatch). It re-derives — not plugs in — every identity the M1 lemmas encode:
`sum_odds = m²`; the additive telescope `T(i-1)² + i³ = T(i)²`; `block = T(i)² − T(i-1)² = i³`; block
geometry (size `i`, smallest odd `i²−i+1`, largest `i²+i−1`); the ℕ-sub-free reindex
`T(i)² + (i+1)³ = T(i+1)²`; Gauss `T(n)=∑i`; and an end-to-end brute-force chain
`blocks == cubes == firstOdds == T_n² == (∑i)²` for `n = 0..60`. **All checks pass.** This makes the
M1 spec machine-checkable build-free, so the only remaining work is the Lean transcription (the
division-clearing in L2′ being the sole non-mechanical step). The eventual `.lean` is cross-checkable
against the parent, which already proves the same theorem algebraically (`sum_cubes_eq_sum_squared`).

**Milestone split**
- M1 (formalizable now): L1 + L2′ + L3′ + Main′ above (ℕ-sub-free reindex). Pure Mathlib, no gaps —
  Docker-gated only; arithmetic certified by `verify_m1.py`.
- M2 (pedagogical, optional): an explicit `Finset` **bijection** between the Σ-type {(i,j) : block}
  and `range (T n)` (via `Finset.sum_sigma`/`Finset.sum_biUnion` over a `Finset.disjiUnion`),
  to surface the "blocks ↔ initial segment of odds" bijection literally rather than by telescope.
  Strictly stronger pedagogy, same theorem; defer unless the gallery wants the explicit bijection.

---

## Doc Integrity (fixed this session)

The seeker registry `src/data/research/problems/sum-of-kth-powers-oq-03.json` (untracked local
state in main) listed `leanFiles` = [SumOfKthPowers, …OQ01, …OQ02, …OQ04, …OQ04Aristotle] — i.e.
the **parent and sibling** files, all 0-sorry. There is **no** `SumOfKthPowersOQ03.lean`. Left as
is, this misattribution makes an unsolved OQ look solved. Cleared `leanFiles` to `[]` and seeded
the `knowledge` fields. (Recurring misattribution vein: slug-prefix matching pulls in siblings'
complete files.)

---

## Decision

**ORIENT** (build-free). OQ resolved on paper; formalizable core pinned to existing Mathlib
lemmas with a milestone split; no Mathlib gap. The only blocker to ACT is the verification
blackout (Docker down + Aristotle "Resource not found"). A Docker-up session can type M1 directly.

---

## Insights

- Cleanest Lean route is **telescoping** (`Finset.sum_Ico_consecutive`), not an explicit
  bijection: `T_i² − T_{i−1}² = i³` reduces the whole proof to sum-of-odds + range concatenation.
- The block-vs-cube identity is equivalent to `T_i² − T_{i−1}² = i³`; prove it additively
  (`T (i-1)^2 + i^3 = T i^2`) to dodge ℕ-subtraction.
- Independence from the parent is genuine: parent uses closed forms (`sum_cubes_classical`),
  this uses a tiling of odds — no shared lemma beyond Gauss.

## Dead Ends

- (none yet — no proof attempt could run during the backend blackout)

---

## Session 2026-06-14 (S2, researcher-4) — build-free ℕ-spec verification

Still backend blackout (Docker `docker info` timeout; Aristotle `prove` → "Resource not found").
Re-verified the **entire formalizable core exactly as Lean would evaluate it in ℕ** (emulating
truncated subtraction `i-1` and `T i = i*(i+1)/2`), to catch off-by-one / ℕ-truncation hazards in
the spec *before* it is typed:

- **L1** `∑_{j<m}(2j+1)=m²` holds for all `m ≤ 50`.
- **L2** `∑_{j∈Ico(T(i-1),T i)}(2j+1)=i³` holds for all `1 ≤ i ≤ 40`.
- **i=0 edge (the subtle one):** in `Main` the sum runs over `range (n+1)`, which *includes* `i=0`.
  With ℕ-truncated `i-1`, the `i=0` block is `Ico (T 0) (T 0) = Ico 0 0 = ∅`, summing to `0 = 0³`.
  So including `i=0` is harmless and L2 need only be proved for `i ≥ 1` — **confirmed**, no special
  casing of `i=0` is required in `Main`.
- **L3 tiling + Main** `∑_{i<n+1} i³ = ∑_{i<n+1}(block i) = ∑_{j<T n}(2j+1) = T n² = (∑_{i<n+1} i)²`
  holds as a 5-way exact equality for all `n ≤ 40`; `T i − T(i-1) = i` confirmed (ranges tile `[0,T n)`).

Conclusion: the spec is ℕ-sound as written; M1 carries no hidden off-by-one. No spec changes needed
— this only raises confidence for the Docker-up ACT. (Verified with `python3` emulating ℕ semantics.)
