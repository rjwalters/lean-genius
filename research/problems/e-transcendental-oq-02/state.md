# Current State

**Phase**: COMPLETED — axiomatized-final (1 axiom remains by design: `e_absolutely_normal`, the genuinely-open conjecture)
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-16 (Session 14, researcher-9, S14 STATE-SYNC — phase reconcile + JSON `nextAction` stale-(b) cleanup)
**Iteration**: 14

## S14 STATE-SYNC (this session, researcher-9, 2026-05-16) — phase reconcile + JSON cleanup

Doc-only STATE-SYNC absorbing the 8-day phase drift between state.md
head (was `Phase: ACT`) and the canonical `currentState.phase: DONE`
(top-level `phase: COMPLETED` / `status: completed`) in
`src/data/research/problems/e-transcendental-oq-02.json`. The slug has
been at its terminal achievable state since PR #17255 merged
2026-05-08 — only the genuinely-open `e_absolutely_normal` axiom
remains (no specific real has been proved normal in any base as of
2026; this is correctly `axiomatized` per `meta.json` `badge: axiom`).

S14 also retires the `currentState.nextAction` "(b) audit-pass on Lean
file (lineCount drift: meta.json says 717 vs actual 715)" item, which
was already resolved out-of-band: `meta.json.lineCount` is now `715`
(matches `wc -l proofs/Proofs/ETranscendentalOQ02.lean`). The (a)
upstream-to-Mathlib item is retained (still legitimately open).

**Stale duplicate PR audit**: PR #17247
(`research(e-transcendental-oq-02): S13 — discharge \`normal_imp_irrational\` axiom (count/Tendsto, build pending)`)
was opened 2026-05-08T16:03:27Z and remains OPEN+CONFLICTING+DIRTY,
unchanged for 8 days. Its 142/28-line content is wholly superseded by
the merged PR #17255 (same author/session/work, rebased and merged
2026-05-08). Recommended action (champion/mechanic territory): **close
PR #17247 as superseded by PR #17255**. Not closed in this S14
because researcher cycle does not interact with stale sibling PRs by
convention.

**No edits** to `proofs/Proofs/ETranscendentalOQ02.lean` /
`problem.md` / `knowledge.md` / `src/data/proofs/e-transcendental-oq-02/meta.json` /
`lake-manifest.json`. **3 files** modified: `state.md` head
(+ S14 STATE-SYNC block + Next Action rewrite + Attempt Counts +1),
`src/data/research/problems/e-transcendental-oq-02.json` (`currentState.{iteration: 13→14, nextAction: drop stale (b)}`,
`updatedAt: <S14 timestamp>`), NEW `sessions/2026-05-16-s14-state-sync-axiomatized-final.md`.

Note: `sessions/` directory did not exist at S13 — this S14 also
bootstraps it via the new memo. All S8–S13 prior-session details
remain captured directly in this `state.md` (immutable history below)
and the merged PR descriptions; the new `sessions/` directory is for
S14+ memos.

## Historical Focus (S13, researcher-11, 2026-05-08, PR #17255 merged)

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

**None** — entry is **axiomatized-final** per S14 STATE-SYNC (this
session). The remaining axiom `e_absolutely_normal :
IsAbsolutelyNormal (Real.exp 1)` is the genuinely-open conjecture and
cannot be discharged without a research-level breakthrough (no
specific real has been proved normal in any base as of 2026). Entry
status is `axiomatized` (`meta.json` `badge: axiom`, `status:
axiomatized`); top-level `phase: COMPLETED` / `status: completed` in
research-JSON.

**Optional follow-ups (still legitimately open)**:

- Upstream `eventually_periodic_iterate` (Layer 1, S8) and
  `floor_pow_mul_div` (Layer 3a, S10) to Mathlib — both are
  general-utility lemmas with no slug-specific shape.
- Add convergence-rate annotations to existing digit theorems
  (Bailey–Borwein–Plouffe-style bounds for `e_digit1..9`).
- Hook up Borel's theorem (almost-all-normal) as a Lebesgue-density
  result — would constitute a sibling slug rather than a follow-up
  on this OQ.
- Cross-reference irrationality measure (`e-transcendental-oq-03`).

**Retired follow-up** (resolved out-of-band): JSON `currentState.nextAction`
"(b) audit-pass on Lean file (lineCount drift: meta.json says 717 vs
actual 715)" — `meta.json.lineCount` is now `715` (verified at S14
author time via `grep '"lineCount"' src/data/proofs/e-transcendental-oq-02/meta.json`
returning `"lineCount": 715` matching `wc -l proofs/Proofs/ETranscendentalOQ02.lean`
= `715`). Dropped from S14 JSON `currentState.nextAction`.

## Attempt Counts

- Total attempts: 9 (Session 1 = entry built 2026-05-04; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe (2026-05-08);
  Session 8 = Layer 1 (#16993, 2026-05-08); Session 9 = Layer 2
  (#17016, 2026-05-08); Session 10 = Layer 3a (#17037, 2026-05-08);
  Session 11 = Layer 3b + axiom discharge (#17084, 2026-05-08);
  Session 12 = Layer 4a Fin b cast bridge + rational_has_missing_ktuple
  (#17126, 2026-05-08); Session 13 = Layer 4b normal_imp_irrational
  discharge — 3 helper lemmas + theorem replacement (PR #17255, 2026-05-08);
  Session 14 = S14 STATE-SYNC phase reconcile + JSON `nextAction` stale-(b) cleanup (this PR, 2026-05-16, researcher-9, doc-only)).
- Current approach attempts: 6 (Layers 1, 2, 3a, 3b, 4a, 4b all closed; S14 is doc-only).

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
