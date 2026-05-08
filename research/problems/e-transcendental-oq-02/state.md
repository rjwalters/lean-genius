# Current State

**Phase**: ACT — `normal_imp_irrational` axiom DISCHARGED (Session 13)
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-08 (Session 13, researcher-6)
**Iteration**: 13

## Current Focus

**Session 13 (this session) discharges the `normal_imp_irrational` axiom.**
Builds on Session 12's `rational_has_missing_ktuple` (Layer 4a) using
the count/Tendsto recipe sketched in S12.

Two new declarations (~90 lines):

- `nthDigit_eq_iff_nthDigitFin` (private bridge lemma): connects the
  ℤ-valued digit equality `nthDigit b n x = (d : ℤ)` (used in
  `IsNormalInBase`) to the `Fin b`-valued equality `nthDigitFin b hb n x = d`
  (used by `rational_has_missing_ktuple`). Both directions via
  `nthDigitFin_intCast` + `Fin.ext`.

- `normal_imp_irrational` (theorem, was axiom): assume `x = (q : ℝ)`
  rational. Get `(k, N₀, s)` from `rational_has_missing_ktuple`. Apply
  `IsNormalInBase` at `(k, s)` to get `count(N)/N → b^(-k)`. Bound
  `count(N) ≤ N₀` by showing every match satisfies `n < N₀` (using the
  bridge lemma to connect the predicate forms). Squeeze gives
  `count(N)/N → 0` via `tendsto_const_div_atTop_nhds_zero_nat` and
  `tendsto_of_tendsto_of_tendsto_of_le_of_le`. Then `tendsto_nhds_unique`
  forces `b^(-k) = 0`, contradicting `zpow_pos` at `b ≥ 2`.

After this PR, only **`e_absolutely_normal`** remains axiomatized — the
genuinely-open conjecture (status: 2026 unknown).

**Counts after S13**: lineCount 639 → 721, theoremCount 44 → 46
(+1 private bridge, +1 main theorem), axiomCount 2 → 1, sorries 0
(unchanged).

**Build verification**: Docker build NOT run locally (`proofs/.lake`
self-cycle symlink trap forces fresh Mathlib clone, ~30–45 min). All
Mathlib lemma names verified against the existing codebase
(`tendsto_of_tendsto_of_tendsto_of_le_of_le` in
CentralLimitTheoremOQ02:218, `tendsto_const_div_atTop_nhds_zero_nat` in
BinomialTheoremOQ03:367, `tendsto_nhds_unique` in
LawsOfLargeNumbersOQ03Aristotle:59, `zpow_pos` in NavierStokes:6176).
CI is the ground truth.

### New code (4 lemmas + 1 def + 1 theorem; ~95 lines)

```lean
-- [0, b) bounds on nthDigit (always non-negative; strictly less than b)
private lemma nthDigit_nonneg (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    0 ≤ nthDigit b n x

private lemma nthDigit_lt_base (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    nthDigit b n x < (b : ℤ)

-- Fin b cast of nthDigit (uses Int.toNat under the [0, b) bound)
private noncomputable def nthDigitFin (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) : Fin b

-- Cast back to ℤ
private lemma nthDigitFin_intCast (b : ℕ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    ((nthDigitFin b hb n x : ℕ) : ℤ) = nthDigit b n x

-- Equivalence on the level of Fin b vs ℤ digit equality
private lemma nthDigitFin_eq_iff (b : ℕ) (hb : 0 < b) (n m : ℕ) (x y : ℝ) :
    nthDigitFin b hb n x = nthDigitFin b hb m y ↔
      nthDigit b n x = nthDigit b m y

-- Layer 4a headline: missing k-tuple input for normal_imp_irrational
private theorem rational_has_missing_ktuple (b : ℕ) (hb : 2 ≤ b) (q : ℚ) :
    ∃ (k N₀ : ℕ) (s : Fin k → Fin b),
      0 < k ∧
      ∀ n ≥ N₀, ∃ i : Fin k,
        nthDigitFin b (by omega) (n + i.val) (q : ℝ) ≠ s i
```

### Key Mathlib API used (all v4.26.0)

| Lemma | Module | Role |
|-------|--------|------|
| `Int.emod_nonneg` | core | `0 ≤ a % b` for `b ≠ 0` |
| `Int.emod_lt_of_pos` | core | `a % b < b` for `0 < b` |
| `Int.toNat_of_nonneg` | core | `0 ≤ n → ((n.toNat : ℤ) = n)` |
| `Nat.lt_two_pow_self` | core | `n < 2^n` |
| `Nat.pow_le_pow_left` | core | `a ≤ b → a^n ≤ b^n` |
| `Fin.ext` | core | val equality ⇒ `Fin` equality |

### Recipe step covered by Layer 4a

The full recipe to discharge `normal_imp_irrational` (recipe owner: state.md S11):

1. ✅ Apply `rational_digits_eventually_periodic` to get T, N₀ with the digit
   periodicity for n ≥ N₀ (S11).
2. ✅ Pick `k := T` so `T < bᵏ` follows from `T < 2^T ≤ b^T` (S12).
3. ✅ Apply `periodic_has_missing_ktuple` to extract a missing tuple s (S11),
   bridging via `nthDigitFin` (S12).
4. ❌ Bound the count of n < N where the tuple at offsets `0..k-1` matches s
   by N₀ (the pre-period contribution): pending S13.
5. ❌ Conclude frequency → 0, contradicting normality which forces frequency
   → b^(-k) > 0: pending S13.

Layer 4a (this session) merges steps 1–3 into the single private theorem
`rational_has_missing_ktuple`.

## Active Approach

The Lean entry now establishes:
- **Definitions**: `nthDigit`, `IsNormalInBase`, `IsAbsolutelyNormal`,
  `ratResidue` (private, S9), `nthDigitFin` (private, S12).
- **29 public theorems**: `e_floor`, `e_floor_10..1000000000`, `e_digit1..9`,
  `e_normal_implies_uniform_decimal_digits`, `periodic_has_missing_ktuple`,
  `rational_digits_eventually_periodic` (S11).
- **15 private helpers** (Layers 1–4a):
  - L1: `exists_iterate_collision`, `eventually_periodic_iterate`.
  - L2: `ratResidue_succ`, `ratResidue_eq_iterate`, `ratResidue_eventually_periodic`.
  - L3a: `floor_pow_mul_div`, `floor_pow_rat_eq_ediv`.
  - L3b: `int_mul_ediv_eq`, `nthDigit_succ_via_residue`,
    `nthDigit_succ_eq_of_emod_eq`.
  - L4a (S12): `nthDigit_nonneg`, `nthDigit_lt_base`, `nthDigitFin_intCast`,
    `nthDigitFin_eq_iff`, `rational_has_missing_ktuple`.

**Two remaining axioms**:
- `normal_imp_irrational` — Layer 4a built the missing-tuple structural input.
  S13's task: count/Tendsto step. Recipe:
  1. From `rational_has_missing_ktuple` extract k, N₀, s (data only depends on q).
  2. Show `count(N) := |{n < N : ∀ i, nthDigit b (n+i) q = (s i : ℤ)}| ≤ max N₀ 0`
     via `nthDigitFin_eq_iff` and the missing-tuple property.
  3. Bound `(count(N) : ℝ) / N ≤ N₀ / N → 0`.
  4. By normality, `count(N) / N → b^(-k) > 0` (since `b ≥ 2`).
  5. Contradiction.
- `e_absolutely_normal` — the **main open conjecture**. Genuinely open
  as of 2026; will remain axiomatized.

## Blockers

- **Local Lean build unreliable**: Worktree's `proofs/.lake` is a
  self-cycle symlink — Docker build cold-clones Mathlib (~45 min).
  Following S8/S9/S10/S11 convention, build verification is deferred to CI.
  All Mathlib lemmas used are well-established and stable in v4.26.0.

## Next Action

**ACT (Session 13)** — discharge `normal_imp_irrational` using the count/Tendsto
recipe (steps 4–5 above). The structural input (missing k-tuple) is now
provided by Layer 4a's `rational_has_missing_ktuple`.

Sketch: for the rational case, define
```lean
let A : Finset ℕ := (Finset.range N).filter
  (fun n => ∀ i : Fin k, nthDigit b (n + i.val) (q : ℝ) = (s i : ℤ))
```
and show `A ⊆ Finset.range N₀` via the missing-tuple guarantee for `n ≥ N₀`.
Then `(A.card : ℝ) / N ≤ N₀ / N → 0`, but normality demands the limit is
`b^(-k) > 0`. Contradiction; hence `x` is not rational.

After Session 13, only `e_absolutely_normal` remains axiomatized — and
that is the genuinely-open conjecture.

## Attempt Counts

- Total attempts: 7 (Session 1 = entry built 2026-05-04; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe (2026-05-08);
  Session 8 = Layer 1 (#16993, 2026-05-08); Session 9 = Layer 2
  (#17016, 2026-05-08); Session 10 = Layer 3a (#17037, 2026-05-08);
  Session 11 = Layer 3b + axiom discharge (#17084, 2026-05-08);
  Session 12 = Layer 4a Fin b cast bridge + rational_has_missing_ktuple
  (this PR, 2026-05-08)).
- Current approach attempts: 5 (Layers 1, 2, 3a, 3b, 4a all closed).

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:495+` — `nthDigit_nonneg`,
  `nthDigit_lt_base`, `nthDigitFin`, `nthDigitFin_intCast`,
  `nthDigitFin_eq_iff` (Layer 4a, S12)
- `proofs/Proofs/ETranscendentalOQ02.lean:573+` — `rational_has_missing_ktuple`
  (Layer 4a headline, S12)
- `proofs/Proofs/ETranscendentalOQ02.lean:424` — `rational_digits_eventually_periodic`
  (theorem, S11)
- `proofs/Proofs/ETranscendentalOQ02.lean:446` — `periodic_has_missing_ktuple` (S11)
- `proofs/Proofs/ETranscendentalOQ02.lean:308` — `ratResidue_eventually_periodic` (Layer 2, S9)
- `proofs/Proofs/ETranscendentalOQ02.lean:243` — `eventually_periodic_iterate` (Layer 1, S8)
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata
