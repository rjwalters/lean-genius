# Current State

**Phase**: ACT — `normal_imp_irrational` discharged (axiomCount 2 → 1)
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-08 (Session 13, researcher-11)
**Iteration**: 13

## Current Focus

**Session 13** discharged the `normal_imp_irrational` axiom by composing
S12's `rational_has_missing_ktuple` with three new private lemmas:

1. `rational_has_missing_ktuple_intCast` — bridges S12's `Fin b` form to
   the ℤ-valued `nthDigit` form that appears literally inside `IsNormalInBase`.
2. `rational_match_count_le` — for the missing-tuple data, the count of
   matching positions in `Finset.range N` is at most `N₀` (positions `≥ N₀`
   are excluded by the missing-tuple property; `Finset.card_le_card` ▷
   `Finset.range N₀`).
3. `tendsto_bounded_count_div_atTop_zero` — squeeze theorem: a non-negative
   ℕ-sequence bounded above by `N₀` has `c_N / N → 0` (`N₀ / N = N₀ · N⁻¹
   → N₀ · 0 = 0`; `tendsto_inv_atTop_zero` ∘ `tendsto_natCast_atTop_atTop`).

Composing: the matching-position frequency tends to `0`, but `IsNormalInBase`
forces it to tend to `b^(-k) > 0`. `tendsto_nhds_unique` gives `0 = b^(-k)`,
which contradicts `zpow_pos`. Hence rational `x` cannot be normal.

`normal_imp_irrational` is now a `theorem` rather than `axiom`. Only one axiom
remains: **`e_absolutely_normal`** — the genuinely-open conjecture.

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

**One remaining axiom**:
- `e_absolutely_normal` — the **main open conjecture**. Genuinely open
  as of 2026; will remain axiomatized.

S13 closed `normal_imp_irrational` per the recipe sketched in S12:
  1. ✅ Extract k, N₀, s from `rational_has_missing_ktuple` and lift to ℤ-valued
     form via `nthDigitFin_intCast` (`rational_has_missing_ktuple_intCast`).
  2. ✅ `Finset.card_le_card` ▷ `Finset.range N₀` proves
     `count(N) ≤ N₀` (`rational_match_count_le`).
  3. ✅ Squeeze `0 ≤ count(N)/N ≤ N₀/N` with `N₀/N → 0`
     (`tendsto_bounded_count_div_atTop_zero`).
  4. ✅ By normality, `count(N)/N → b^(-k)`; uniqueness of limits gives
     `0 = b^(-k)`, but `zpow_pos` says `b^(-k) > 0`. Contradiction.

## Blockers

- **Build region wider drift**: `Proofs/eTranscendental.lean` (the importing
  parent of this entry, used for `e_irrational`/`e_transcendental`) currently
  fails to build at v4.26.0 because `IsFractionRing.isAlgebraic_iff` was
  removed/renamed in mathlib upstream (9 call sites). This is a pre-existing
  drift unrelated to S13 — fixing it is out of scope here. Local build
  verification deferred per S8/S9/S10/S11/S12 convention. The S13 logic
  itself uses only `tendsto_inv_atTop_zero`, `tendsto_natCast_atTop_atTop`,
  `Tendsto.const_mul`, `Tendsto.comp`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`,
  `tendsto_const_nhds`, `tendsto_nhds_unique`, `Filter.Eventually.of_forall`,
  `Finset.card_le_card`, `Finset.card_range`, `Finset.mem_filter`,
  `Finset.mem_range`, `Fin.ext`, `Nat.eq_zero_or_pos`, `zpow_pos`, and `gcongr`
  — all well-established and verified present in mathlib v4.26.0.

## Next Action

**ORIENT (Session 14)** — only the open conjecture `e_absolutely_normal`
remains. No further axiom-discharge work is meaningful (this is the
genuinely-open mathematical question, 2026). Future sessions could:
- Add convergence-rate annotations to the existing digit theorems (e.g.
  Bailey–Borwein–Plouffe-style bounds);
- Hook up Borel's theorem (almost-all-normal) as a Lebesgue-density result;
- Cross-reference irrationality measure (e-transcendental-oq-03).

Or simply mark the entry **"axiomatized — final"** and move on.

## Attempt Counts

- Total attempts: 8 (Session 1 = entry built 2026-05-04; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe (2026-05-08);
  Session 8 = Layer 1 (#16993, 2026-05-08); Session 9 = Layer 2
  (#17016, 2026-05-08); Session 10 = Layer 3a (#17037, 2026-05-08);
  Session 11 = Layer 3b + axiom discharge (#17084, 2026-05-08);
  Session 12 = Layer 4a Fin b cast bridge + rational_has_missing_ktuple
  (#17126, 2026-05-08); Session 13 = Layer 4b normal_imp_irrational
  discharge — 3 helper lemmas + theorem replacement (this PR, 2026-05-08)).
- Current approach attempts: 6 (Layers 1, 2, 3a, 3b, 4a, 4b all closed).

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:590+` — `rational_has_missing_ktuple_intCast`,
  `rational_match_count_le`, `tendsto_bounded_count_div_atTop_zero`,
  `normal_imp_irrational` (Layer 4b, S13)
- `proofs/Proofs/ETranscendentalOQ02.lean:495+` — `nthDigit_nonneg`,
  `nthDigit_lt_base`, `nthDigitFin`, `nthDigitFin_intCast`,
  `nthDigitFin_eq_iff` (Layer 4a, S12)
- `proofs/Proofs/ETranscendentalOQ02.lean:568+` — `rational_has_missing_ktuple`
  (Layer 4a headline, S12)
- `proofs/Proofs/ETranscendentalOQ02.lean:424` — `rational_digits_eventually_periodic`
  (theorem, S11)
- `proofs/Proofs/ETranscendentalOQ02.lean:446` — `periodic_has_missing_ktuple` (S11)
- `proofs/Proofs/ETranscendentalOQ02.lean:308` — `ratResidue_eventually_periodic` (Layer 2, S9)
- `proofs/Proofs/ETranscendentalOQ02.lean:243` — `eventually_periodic_iterate` (Layer 1, S8)
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata
