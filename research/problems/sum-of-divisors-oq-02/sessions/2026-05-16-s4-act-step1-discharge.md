# S4 ACT — Step 1 discharge (sigma_two_pow_mul_odd)

**Author:** researcher-9
**Timestamp:** 2026-05-16 ~01:10 UTC
**Phase:** S4 ACT (Lean-modifying, sorry count 6 → 5)
**Iteration:** 4
**Mathlib pin:** v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`),
confirmed via `proofs/lake-manifest.json` line 8 (unchanged since S2 SCAFFOLD).
**Pre-merge state:** PR #19169 (S3 PREP, doc-only) merged
2026-05-15T22:56:52Z by researcher-8.

## 0. Scope

Single-lemma discharge: replace `sigma_two_pow_mul_odd`'s `by sorry` with the
3-LOC term-mode body recommended verbatim in
`sessions/2026-05-14-s3-prep-step1-step5-discharge.md` §3.2. Option B of S3
PREP §6 (Step 1 only; Step 5 deferred to S7 — its final-tactic reconciliation
needs Docker-time iteration per S3 PREP §7 R3).

## 1. Lean delta

Before (lines 47-53 of `proofs/Proofs/SumOfDivisorsOQ02.lean` on `origin/main`):

```lean
/-- **Step 1** (sigma multiplicativity, specialized to `2^k · m` with `m` odd).
Since `m` is odd, `gcd(2^k, m) = 1`, so σ(2^k · m) = σ(2^k) · σ(m).
S3+ proof plan: `isMultiplicative_sigma.map_mul_of_coprime
((Odd.coprime_two_right hm_odd).pow_right _)` (mirroring the Archive line). -/
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m := by
  sorry
```

After (this PR):

```lean
/-- **Step 1** (sigma multiplicativity, specialized to `2^k · m` with `m` odd).
Since `m` is odd, `gcd(2^k, m) = 1`, so σ(2^k · m) = σ(2^k) · σ(m).
Proof: `isMultiplicative_sigma` supplies σ's multiplicativity; the coprimality
hypothesis is built by `Odd.coprime_two_right hm_odd : Coprime m 2`, symmetrized
to `Coprime 2 m`, then promoted by `pow_left k` to `Coprime (2^k) m`. -/
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m :=
  isMultiplicative_sigma.map_mul_of_coprime
    ((Odd.coprime_two_right hm_odd).symm.pow_left k)
```

File-level delta: +6 / -4 (drops `by sorry` placeholder, adds 3-LOC term-mode
body and updated docstring; header status table also updated, see §3).

## 2. Why this exact body (per S3 PREP §2.1)

Lean type-flow:

| Step | Term | Type |
|------|------|------|
| (a) | `Odd.coprime_two_right hm_odd` | `Nat.Coprime m 2` |
| (b) | `_.symm` | `Nat.Coprime 2 m` |
| (c) | `_.pow_left k` | `Nat.Coprime (2 ^ k) m` |
| (d) | `isMultiplicative_sigma` | `IsMultiplicative (σ 1)` |
| (e) | `_.map_mul_of_coprime <c>` | `σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m` |

The Archive (line 79 of `Archive/Wiedijk100Theorems/PerfectNumbers.lean`) uses
the equivalent path `(Nat.prime_two.coprime_pow_of_not_dvd hm).symm` where
`hm : ¬ 2 ∣ m`. Our SCAFFOLD takes `hm_odd : Odd m`, which is 2 LOC shorter
via `Odd.coprime_two_right` (a protected alias defined at
`Mathlib/Data/Nat/Prime/Basic.lean:151` per S3 PREP bearer table).

Term-mode preferred over tactic-mode because `map_mul_of_coprime` directly
yields the goal equality; no `by exact ...` wrapper needed (saves 2 LOC).

## 3. Lean header update

The SCAFFOLD's status block (lines 21-26) listed Step 1 among the
`sorry`-stubbed lemmas. Updated to:

```
## Status (post-S4)

- Step 1 (`sigma_two_pow_mul_odd`): proved (S4 ACT, term-mode via
  `isMultiplicative_sigma.map_mul_of_coprime` + `.symm.pow_left`).
- Step 2 (`sigma_two_pow_eq_mersenne`): proved (direct alias of Archive).
- Steps 3, 4, 5, 6: `sorry` placeholders. Discharge planned for S5+.
- Top-level theorem `euler_converse_self_contained`: `sorry` (chains steps).
```

## 4. Pre-merge bearer drift recheck

Per S3 PREP §2 + §9, all five Step 1 bearers were cited stable across
master→v4.26.0 history. Re-verified at this PR's pin SHA (`2df2f015...`,
unchanged from SCAFFOLD's S2 build):

| # | Bearer | Status | Notes |
|---|--------|--------|-------|
| 1 | `ArithmeticFunction.isMultiplicative_sigma` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:202`) | ✓ stable | Generic over `k : ℕ`; we instantiate at `k = 1`. |
| 2 | `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime` (`Mathlib/NumberTheory/ArithmeticFunction/Basic.lean`) | ✓ stable | Standard multiplicative-function method. |
| 3 | `Odd.coprime_two_right` (`Mathlib/Data/Nat/Prime/Basic.lean:151`) | ✓ stable | Returns `n.Coprime 2`; we follow with `.symm`. |
| 4 | `Nat.Coprime.symm` (core, `Mathlib/Data/Nat/GCD/Basic.lean` area) | ✓ stable | gcd_comm in disguise. |
| 5 | `Nat.Coprime.pow_left` (core) | ✓ stable | Widely used (15+ Mathlib call sites). |

No bearer drift; no risk-register-R1 fallback needed.

## 5. Sorry inventory (post-S4)

| Lemma | Pre-S4 | Post-S4 | Next-step planner |
|-------|--------|---------|-------------------|
| `sigma_two_pow_mul_odd` (Step 1) | sorry | **proved** | n/a |
| `sigma_two_pow_eq_mersenne` (Step 2) | proved | proved | n/a (Archive alias) |
| `mersenne_mul_sigma_eq_two_pow_mul` (Step 3) | sorry | sorry | S5 ACT: unfold `Nat.perfect_iff_sum_divisors_eq_two_mul`, apply Steps 1+2, `← mul_assoc + pow_succ`. ~6 LOC. |
| `mersenne_dvd_odd_part` (Step 4) | sorry | sorry | S6 ACT: `(Odd.coprime_two_right ?).pow_left.dvd_of_dvd_mul_left` on `Dvd.intro _ h_eq`. ~5 LOC. Needs `Odd (mersenne (k+1))` lemma. |
| `sigma_eq_self_add_cofactor` (Step 5) | sorry | sorry | S7 ACT: use S3 PREP §5.3 5-line body; resolve final-tactic per R3 (linarith [hm] / linear_combination h_eq + hm / explicit rw [hm]). |
| `cofactor_one_and_prime` (Step 6) | sorry | sorry | S8 ACT: `Nat.sum_divisors_eq_sum_properDivisors_add_self`, `Nat.sum_properDivisors_dvd` case-split, `Nat.sum_properDivisors_eq_one_iff_prime`. ~10 LOC, includes `cases k` branch. |
| `euler_converse_self_contained` (top-level) | sorry | sorry | S9 ACT: `eq_two_pow_mul_odd` (Archive) + chain Steps 1-6. ~8 LOC glue. |

Total: `sorryCount = 6 → 5`, `lineCount = 110 → 114`, `theoremCount = 7`
(unchanged), `axiomCount = 0` (unchanged), `defCount = 0` (unchanged).

## 6. Build status

S2 SCAFFOLD's Docker build was clean at 3063 jobs against the same pin
(`2df2f015...`). This PR swaps a single `by sorry` for a term-mode body
invoking already-imported bearers (`isMultiplicative_sigma` is exported by
`Mathlib.NumberTheory.ArithmeticFunction`, which the file already imports
transitively via `Mathlib.Tactic` + the `Archive.Wiedijk100Theorems.PerfectNumbers`
import).

**Build verified.** Ran `proofs/scripts/docker-build.sh
Proofs.SumOfDivisorsOQ02` at this PR's HEAD: 3063 jobs clean, 5 expected
sorry warnings (lines 67, 77, 87, 99, 109 — Steps 3, 4, 5, 6, top-level).
Step 1's sorry warning is gone. Log preserved at
`.loom/logs/researcher-9-sumdivisors-s4-build.log`.

```
✔ [3062/3063] Built Archive.Wiedijk100Theorems.PerfectNumbers (5.4s)
⚠ [3063/3063] Built Proofs.SumOfDivisorsOQ02 (2.2s)
warning: Proofs/SumOfDivisorsOQ02.lean:67:6: declaration uses 'sorry'
warning: Proofs/SumOfDivisorsOQ02.lean:77:6: declaration uses 'sorry'
warning: Proofs/SumOfDivisorsOQ02.lean:87:6: declaration uses 'sorry'
warning: Proofs/SumOfDivisorsOQ02.lean:99:6: declaration uses 'sorry'
warning: Proofs/SumOfDivisorsOQ02.lean:109:8: declaration uses 'sorry'
Build completed successfully (3063 jobs).
```

## 7. Path-forward — Step 3 prep guidance for S5 picker

Step 3's statement (lines 63-66 of post-S4 file):

```lean
lemma mersenne_mul_sigma_eq_two_pow_mul
    (k m : ℕ) (hm_odd : Odd m) (h_perfect : (2 ^ k * m).Perfect) :
    mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m
```

Recommended discharge (per state.md's S5 next-action):

```lean
:= by
  -- σ(2^k * m) = 2 * (2^k * m) from h_perfect
  have h_sum : σ 1 (2 ^ k * m) = 2 * (2 ^ k * m) := by
    have := (Nat.perfect_iff_sum_divisors_eq_two_mul (by positivity)).mp h_perfect
    -- bridge σ 1 → Nat.sum_divisors via Nat.sigma_one_eq_sum_divisors or similar
    sorry  -- pin-PEND: bridge lemma between σ 1 and Nat.sum_divisors
  -- apply Step 1: σ(2^k * m) = σ(2^k) * σ(m)
  rw [sigma_two_pow_mul_odd k m hm_odd] at h_sum
  -- apply Step 2: σ(2^k) = M_{k+1}
  rw [sigma_two_pow_eq_mersenne] at h_sum
  -- h_sum : mersenne (k+1) * σ 1 m = 2 * (2^k * m)
  -- want  : mersenne (k+1) * σ 1 m = 2^(k+1) * m
  -- bridge via mul_assoc + pow_succ': 2 * (2^k * m) = (2 * 2^k) * m = 2^(k+1) * m
  rw [← mul_assoc, ← pow_succ'] at h_sum
  exact h_sum
```

**Risk register for S5**:
- R1: The σ 1 ↔ `Nat.sum_divisors` bridge. `Nat.sigma_one_eq_sum_divisors`
  exists at v4.26.0 (per Archive line ~83 usage). Fallback: unfold via
  `ArithmeticFunction.sigma_one_apply` + `Finset.sum_id`. 1 lemma name pin
  needed before S5 ships.
- R2: `pow_succ'` vs `pow_succ` direction. `pow_succ : a^(n+1) = a^n * a`;
  we want `2^(k+1) = 2 * 2^k`, which is `pow_succ'` (or `← pow_succ` + `mul_comm`).
- R3: `Nat.perfect_iff_sum_divisors_eq_two_mul` may have a different positivity
  hypothesis at the pin (e.g., `0 < n` vs `n ≠ 0`). Audit before S5.

A doc-only S5 PREP (mirroring S3 PREP's pattern: pin-cite Step 3 bearers +
bridge-lemma audit + risk register) is a safe alternative if the S5 picker
wants Docker-build-time iteration insurance.

## 8. Counts

| Metric | Pre-S4 (`origin/main` post-#19169) | Post-S4 (this PR) |
|--------|---------|---------|
| `proofs/Proofs/SumOfDivisorsOQ02.lean` LOC | 110 | 114 |
| Sorries in file | 6 | 5 |
| Axioms in file | 0 | 0 |
| Theorems in file | 7 (6 lemmas + 1 top-level) | 7 |
| Definitions in file | 0 | 0 |
| New sessions/ memos | 0 | 1 (this file) |
| `state.md` edits | 0 | +Iteration→4, +S4 deliverables block, +S3 PREP entry, +S4 entry, +next-action S5 |
| `src/data/research/problems/sum-of-divisors-oq-02.json` edits | 0 | currentState (phase/since/iteration/focus/nextAction/attemptCounts) + knowledge.progressSummary + knowledge.builtItems + knowledge.nextSteps + lastUpdate + leanFiles.lineCount/sorryCount |

## 9. Orthogonality

- No other open PR currently touches `proofs/Proofs/SumOfDivisorsOQ02.lean`
  (last write: PR #19131 S2 SCAFFOLD merged 2026-05-15T22:57Z; S3 PREP
  PR #19169 was strictly orthogonal per its §0).
- No other open PR touches `state.md` or the OQ-02 JSON
  (verified via `gh pr list --search "sum-of-divisors-oq-02 in:title" --state open` = 0 results pre-PR).
- This PR adds one new file under `sessions/` and modifies three existing
  files (Lean + state.md + JSON), all under the slug's own subtree.

## 10. Honesty note

Step 1's discharge is structurally identical to the Archive's invocation,
specialized to `Odd m` rather than `¬ 2 ∣ m`. The gallery value of the
overall slug remains documentation-only (per the S2 SCAFFOLD's honesty
header at `proofs/Proofs/SumOfDivisorsOQ02.lean:28-33`). After Step 6
is discharged (S8 ACT), the slug should be closed as "covered-by-parent
/ pedagogical-only" and gallery-registered with annotations under
`src/data/proofs/sum-of-divisors-oq-02/`.
