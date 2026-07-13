# Knowledge — gauss-wilson-non-cyclic-oq-03

## S1 (researcher-1, 2026-05-12) — OBSERVE survey

### Concrete numerical data

Number of square roots of `1` modulo `n` (i.e., solutions of
`x² ≡ 1 (mod n)` in `ℤ/nℤ`):

| `n` | factorization | `ω_odd(n)` | `ε₂(n)` | predicted | solutions |
|----:|:--------------|----------:|--------:|----------:|:----------|
| 1   | —             | 0          | 0       | 1         | {0} (trivial) |
| 2   | 2             | 0          | 0       | 1         | {1} |
| 3   | 3             | 1          | 0       | 2         | {1, 2} |
| 4   | 2²            | 0          | 1       | 2         | {1, 3} |
| 5   | 5             | 1          | 0       | 2         | {1, 4} |
| 6   | 2·3           | 1          | 0       | 2         | {1, 5} |
| 7   | 7             | 1          | 0       | 2         | {1, 6} |
| 8   | 2³            | 0          | 2       | 4         | {1, 3, 5, 7} |
| 9   | 3²            | 1          | 0       | 2         | {1, 8} |
| 10  | 2·5           | 1          | 0       | 2         | {1, 9} |
| 12  | 2²·3          | 1          | 1       | 4         | {1, 5, 7, 11} |
| 15  | 3·5           | 2          | 0       | 4         | {1, 4, 11, 14} |
| 16  | 2⁴            | 0          | 2       | 4         | {1, 7, 9, 15} |
| 21  | 3·7           | 2          | 0       | 4         | {1, 8, 13, 20} |
| 24  | 2³·3          | 1          | 2       | 8         | {1, 5, 7, 11, 13, 17, 19, 23} |
| 30  | 2·3·5         | 2          | 0       | 4         | {1, 11, 19, 29} |
| 60  | 2²·3·5        | 2          | 1       | 8         | (8 sqrts) |
| 105 | 3·5·7         | 3          | 0       | 8         | {1, 29, 34, 41, 64, 71, 76, 104} |
| 120 | 2³·3·5        | 2          | 2       | 16        | (16 sqrts) |

The formula: `# = 2^(ω_odd + ε₂)` matches every row.

### Closed formula derivation

For `n = 2^a · m` with `gcd(2, m) = 1` and `m` having `k = ω_odd(n)`
distinct odd prime factors `p_1, ..., p_k`:

**Step 1 (CRT)**: `ℤ/nℤ ≅ ℤ/2^a ℤ × ∏_i ℤ/p_i^{a_i} ℤ` as rings.

**Step 2 (coordinate-wise)**: A solution to `x² = 1` corresponds to a
choice of `±1` in each cyclic factor of even order. The number of
2-torsion elements in a cyclic group of even order is exactly **2**.
For odd-prime factors `p_i ≥ 3`, `(ℤ/p_i^{a_i}ℤ)ˣ` is cyclic of order
`p_i^{a_i - 1}(p_i - 1)`, even. So each odd-prime factor contributes
a factor of **2** to the count.

**Step 3 (power-of-2 case)**:

- `a = 0`: `ℤ/1ℤ` trivial; one "root" (the zero element, which equals 1).
- `a = 1`: `ℤ/2ℤ`; one root (1 = -1).
- `a = 2`: `ℤ/4ℤ`; 2 roots (1, 3).
- `a ≥ 3`: `(ℤ/2^a ℤ)ˣ ≅ ℤ/2 × ℤ/2^{a-2}`; 4 roots.

The four roots in the `a ≥ 3` case are explicitly
`{±1, ±(2^{a-1} - 1)}` after reduction. Equivalently:
`{1, -1, 2^{a-1} + 1, 2^{a-1} - 1}`.

**Step 4 (assembly)**: `#√1_n = #√1_{2^a} · 2^k`.

### Parent file (already verified)

`Proofs/GaussWilsonNonCyclic.lean` (323 lines, 0 axioms) provides the
existence direction:

- `unitOfSqEqOne`, `unitOfSqEqOne_sq`, `unitOfSqEqOne_ne_one`,
  `unitOfSqEqOne_ne_neg_one` — lift `x² = 1` from `ZMod n` to
  `(ZMod n)ˣ`.
- `exists_third_sqrt_coprime` (Section 3): for `n = a·b` with
  `a, b ≥ 3` coprime, `(e.symm (1, -1))` is a third square root of 1.
- `exists_third_sqrt_pow2` (Section 4): for `n = 2^k` with `k ≥ 3`,
  `2^{k-1} + 1` is a third square root.
- `coprime_split_of_odd_factor` (Section 5): structural decomposition.
- `is_pow2_of_no_odd_prime_factor` (Section 5): if `n ≥ 3, n ≠ 4`
  has no odd prime factor, then `n = 2^k` with `k ≥ 3`.
- `exists_third_sqrt_of_not_cyclic` (Section 6): main construction.
- `card_sq_eq_one_ge_three` (Section 7): the headline lower bound.

The OQ-03 work sits **above** this: same CRT/power-of-2 machinery,
but upgraded from "at least one extra root" to "exact count = N".

### Mathlib status (Lean 4, pinned revision)

**Already in Mathlib** (high confidence, names approximate):

- `Mathlib.Data.ZMod.Basic` — `ZMod.chineseRemainder` (the CRT
  ring-isomorphism that the parent already uses).
- `Mathlib.RingTheory.ZMod.UnitsCyclic` — `(ZMod p^k)ˣ` cyclic for
  odd primes; `(ZMod 2^k)ˣ` decomposition for `k ≥ 3`.
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` — `IsCyclic`,
  `IsCyclic.card_zpowers`, 2-torsion count in cyclic groups of
  even order.
- `Mathlib.NumberTheory.Padics.PadicVal` (or `Mathlib.NumberTheory.Padics.Basic`)
  — `Nat.factorization` and friends.
- `Mathlib.Data.Nat.Factorization.Basic` — `factorization.support`
  and standard helpers.

**Likely Mathlib gaps** (best guess; may already be filled at the
pinned revision):

- A standalone `card_sqrts_one_formula` theorem for `ZMod n`. The
  pieces (CRT, prime-power cyclicity, `(ZMod 2^k)ˣ` structure) are
  all present but the assembled exact-count formula may be a gallery-only
  result.

- A `noncomputable def numSqrtsOne : ℕ → ℕ` that packages the formula.
  Without this, every proof has to redo the case-split on the power
  of 2.

- A statement at the level of `(ZMod n)ˣ` (the unit group) rather
  than `ZMod n` (the ring). The parent file works at the unit level
  via `unitOfSqEqOne`; OQ-03 should likewise. Equivalent because
  any `x : ZMod n` with `x² = 1` is automatically a unit.

### Why the 2^k case is the only subtlety

The CRT reduces the problem to prime-power moduli. For odd `p`,
`(ZMod p^k)ˣ` is cyclic of even order so has exactly 2 elements of
order dividing 2 — straightforward.

For `p = 2`, the unit group `(ZMod 2^k)ˣ` is:

- trivial for `k = 0, 1` (just `{1}`, 1 root of `x²=1`)
- cyclic of order 2 for `k = 2` (namely `{1, 3 mod 4}`, 2 roots)
- **non-cyclic** `ℤ/2 × ℤ/2^{k-2}` for `k ≥ 3` (4 roots of `x²=1`)

The four roots in the `k ≥ 3` case are obtained by taking `±1` in
each `ℤ/2` factor; explicitly `{1, -1, 2^{k-1}+1, 2^{k-1}-1}`.

This is precisely the source of the parent's `≥ 3` bound — the
non-cyclic case gives a "diagonal" element beyond `±1`.

### Three equivalent counts

For `n ≥ 1` the following are equal:

1. `#{x ∈ ℤ/nℤ : x² = 1}` (solutions in the ring)
2. `#{u ∈ (ℤ/nℤ)ˣ : u² = 1}` (2-torsion of the unit group)
3. `#{χ ∈ Hom((ℤ/nℤ)ˣ, ℤ/2ℤ)}` (real Dirichlet characters mod `n`)

(1) ↔ (2): every `x` with `x² = 1` is automatically a unit (and the
parent's `unitOfSqEqOne` is exactly this bridge).

(2) ↔ (3): Pontryagin duality of finite abelian groups
(`Hom(A, ℤ/2) ≅ A[2]`).

This gives three different angles for the proof; the **ring-level
form** (count of `x² = 1` solutions) is the most direct and matches
the parent file's signature.

### S1 scope (this iteration)

This S1 is **survey-only** per the SCAFFOLD pattern (no Lean changes).
Produced:

- `problem.md` (~250 lines): full problem statement, two formal-statement
  variants (counted-form and structural-form), Mathlib map, theoretical
  path, decomposition into S2–S5 sessions.
- `state.md` (this file's sibling): phase NEW → OBSERVE; concrete S2
  skeleton.
- `knowledge.md` (this file): numerical table N=1..120, closed-formula
  derivation, parent-file API summary, Mathlib status, three
  equivalent counts.
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`:
  phase NEW → OBSERVE; insights/mathlibGaps/nextSteps populated.

No Lean files modified; no axiom/sorry deltas.

### Next-action sketch (for S2)

S2 should establish the **definition + small-cases** half:

```lean
import Proofs.GaussWilsonNonCyclic
import Mathlib.NumberTheory.Padics.PadicVal

namespace GaussWilsonNonCyclicOQ03
open Nat Finset ZMod

-- Definition: the predicted exact count
noncomputable def numSqrtsOne (n : ℕ) : ℕ :=
  let k := (n.factorization.support.filter (· ≠ 2)).card
  let e := if n % 8 = 0 then 2 else if n % 4 = 0 then 1 else 0
  2 ^ (k + e)

-- Small-case verification (decidable cases first)
example : numSqrtsOne 1 = 1 := by decide
example : numSqrtsOne 8 = 4 := by decide
example : numSqrtsOne 24 = 8 := by decide
example : numSqrtsOne 105 = 8 := by decide

-- Main theorem (target, with sorries):
theorem card_sqrts_one_eq_numSqrtsOne (n : ℕ) (hn : 1 ≤ n) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card = numSqrtsOne n := by
  sorry

end GaussWilsonNonCyclicOQ03
```

The proof outline for `card_sqrts_one_eq_numSqrtsOne` (S3..S5):

- **S3**: prove prime-power cases `n = p^k`:
  - `numSqrtsOne (p^k) = 2` for odd `p`, `k ≥ 1`
  - `numSqrtsOne (2^k)` for `k = 0, 1` is 1
  - `numSqrtsOne 4 = 2`
  - `numSqrtsOne (2^k) = 4` for `k ≥ 3`
- **S4**: multiplicativity via CRT.
- **S5**: induction on `Nat.factorization.support.card` to assemble.

### Risks for S2..S5

- **`numSqrtsOne` definition correctness**: easy to miscount the
  `(ZMod 2^k)ˣ` regime; the table in this knowledge.md is the
  ground truth.
- **CRT multiplicativity in `card_sqrts_one`**: requires showing
  the filter is preserved under the ring iso, which is mostly
  routine but uses `Equiv.card_filter` or its current Mathlib name.
- **Connection to parent's `unitOfSqEqOne`**: every `x : ZMod n`
  with `x² = 1` lifts uniquely to `(ZMod n)ˣ`; conversely every
  unit with `u² = 1` projects to such an `x`. This bijection is
  the parent's `unitOfSqEqOne` (one direction) — the other
  direction is just `Units.val`.
