# Iteration 34 ACT — 28b-1 bridge bound (residue-arithmetic, build verified)

**Date**: 2026-05-14
**Researcher**: researcher-3
**Phase**: ACT (Lean source — first ACT after 6-iter PREP chain Iter 28–33)
**Predecessors**:
- Iter 27 ACT (PR #18225, merged 2026-05-12, researcher-9) — `n ∈ {25,30,50,100}` `native_decide` witnesses (build pending convention).
- Iter 28 PREP (PR #18352, researcher-4) — three-route survey, recommends Route B Beta-integral with Iter 28 ACT target `choose_mul_succ_dvd_lcmRange`.
- Iter 29 PREP (PR #18485, researcher-1) — Mathlib v4.26.0 API audit, decomposes Iter 28 ACT → 28a + 28b.
- Iter 30 PREP (PR #18582, researcher-10) — strong-form identity `max_k v_p(C(n,k)) = log_p(n+1) - v_p(n+1)` at `N ≤ 200`.
- Iter 31 PREP (PR #18606, researcher-5) — pinned-rev API audit + ERRATUM 2 (corrects witness `k₀ = (n+1) - p^e`).
- Iter 32 PREP (PR #18682, researcher-3) — 28b-2 saturation residue arithmetic.
- Iter 33 PREP (PR #18730, researcher-4) — **28b-1 bridge-bound residue arithmetic, ~25-LOC Lean target** (this PREP is the direct target of this ACT).

**Anti-targets** (this ACT does NOT modify any of):
- `problem.md`, `knowledge.md` (only state.md is modified to log the ACT)
- Prior `sessions/*.md` files
- `meta.json` (axiomCount unchanged at 1)
- The axiom `hanson_bound` (still axiomatized; 28b-1 is a step toward eliminating it, not the elimination itself)

## TL;DR

Ships the Lean implementation of **Iter 33 PREP §2's skeleton** for Iter 28b-1, the
**bridge-bound side** of the Iter 28 ACT chain. Two new theorems:

- `BaselProblemOQ01OQ01OQ02OQ03.sum_mod_pow_lt_of_pow_dvd_succ` — **Lemma A** (Iter 33 PREP §1.2).
  For `p` prime, `k ≤ n`, `1 ≤ i ≤ v_p(n+1)`:
  `k % p^i + (n - k) % p^i < p^i`  (residue sum forced into `[0, p^i - 1]` by `n ≡ -1 mod p^i`).
- `BaselProblemOQ01OQ01OQ02OQ03.factorization_succ_mul_choose_le_log_succ` — **Theorem 28b-1** (Iter 33 PREP §1.3).
  For `p` prime, `k ≤ n`:
  `(n + 1).factorization p + (Nat.choose n k).factorization p ≤ Nat.log p (n + 1)`.

Both are sorry-free and axiom-free (the file's `axiom hanson_bound` is untouched).

Also bundled: two ≤3-LOC pre-existing v4.26.0 drift fixes (lines 574 + 1013 in main) that prevented this file from building since Iter 27. The slug is now `build verified` for the first time since the Iter 28-33 PREP chain began.

## What was implemented

### Iter 34 ACT proper (~119 LOC added; insertion point: new Part 4.5, between Part 4 numerical floor and Part 5 axiom block)

#### `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A)

```lean
lemma sum_mod_pow_lt_of_pow_dvd_succ
    {p i n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hi : 1 ≤ i)
    (hi_le : i ≤ (n + 1).factorization p) :
    k % p ^ i + (n - k) % p ^ i < p ^ i
```

The three-step proof (Iter 33 PREP §1.2 in Lean):

1. **`p^i ∣ n+1`** via `(Nat.pow_dvd_pow p hi_le).trans (Nat.ordProj_dvd (n + 1) p)`.
2. **`n % p^i = p^i - 1`** via:
   * `Nat.dvd_iff_mod_eq_zero.mp h_dvd` (`(n+1) % p^i = 0`),
   * `Nat.add_mod n 1 (p^i)` + `Nat.mod_eq_of_lt` on `1 < p^i` (`1 % p^i = 1`),
   * `rcases Nat.lt_or_ge` on `n % p^i + 1` vs `p^i`, with the `<` branch closed by
     `absurd h_add_succ.symm (Nat.succ_ne_zero _)` and the `≥` branch closed by `omega`
     (this resolves Iter 33 PREP §2.1 mechanical TODO #2 — the `Nat.sub_one_mod`
     chain — via a clean `rcases`-and-`absurd` pattern, no new Mathlib API needed).
3. **Residue squeeze** via `Nat.add_mod k (n - k) (p^i)` + `Nat.add_sub_cancel'` to get
   `(sum) % p^i = p^i - 1`, then `by_contra` + `Nat.mod_eq_sub_mod` + `Nat.mod_eq_of_lt`
   to ground the `p^i ≤ sum < 2*p^i` case as a contradiction (sum would be `2*p^i - 1`,
   but `sum ≤ 2*(p^i - 1) = 2*p^i - 2`).

#### `factorization_succ_mul_choose_le_log_succ` (Theorem 28b-1)

```lean
theorem factorization_succ_mul_choose_le_log_succ
    {p : ℕ} (hp : p.Prime) {n k : ℕ} (hkn : k ≤ n) :
    (n + 1).factorization p + (Nat.choose n k).factorization p
      ≤ Nat.log p (n + 1)
```

The four-step proof (Iter 33 PREP §1.3 in Lean):

1. **Apply `Nat.factorization_choose`** with `b = e + 1` where `e = log_p(n+1)`.
   Validity (`log p n < e + 1`) via `Nat.log_mono_right (Nat.le_succ n)`
   (Iter 33 PREP §1.1).
2. **Bound `a ≤ e`** via `Nat.le_log_of_pow_le hp.one_lt (Nat.le_of_dvd (Nat.succ_pos n) h_dvd)`
   on `Nat.ordProj_dvd (n + 1) p` (Iter 33 PREP §2.1 mechanical TODO #3 — confirmed
   the `Nat.le_log_of_pow_le` direction at v4.26.0).
3. **Carries-set ⊆ Ico (a+1) (e+1)** via `Finset.mem_filter` + `Finset.mem_Ico`
   destructuring + `Nat.lt_succ_iff.mp` + the helper `sum_mod_pow_lt_of_pow_dvd_succ`
   (Lemma A applied with `hi_le : i ≤ a`).
4. **Cardinality bound** via `Nat.card_Ico` (`#Ico (a+1) (e+1) = e - a`) + `Finset.card_le_card`,
   then `omega` to close `a + carries ≤ e`.

### Pre-existing drift fixes (~6 LOC)

Two v4.26.0 simp/decide-set drift fixes bundled per the `feedback_researcher_parent_file_build_unblocker_inpr_pattern` pattern (≤3-LOC parent fix INTO research PR):

* **Line 573** (`primorial_le_lcmRange` for `n = 0` case): `simp [primorial, lcmRange_zero]`
  leaves `∏ x ∈ {0} with Nat.Prime x, x ≤ 1` open under v4.26.0. Fix: `simp only [primorial, lcmRange_zero]; native_decide` (closes via compiled bytecode, no `Decidable` unfolding stall).

* **Line 1012** (`example :` block: `∏_{p ≤ 10, p² ≤ 10} (10 / p) ≤ 5^(√10)`):
  `decide` no longer reduces this `Decidable` instance because `Nat.decidablePrime`
  short-circuits to a stuck `match` on `.ble`. Fix: swap `decide` → `native_decide`
  (proven pattern from `hanson_n15`/`hanson_n20`/`hanson_n25`+ Iter 27 family in
  the same file).

## §1 — File delta accounting

```
proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean: 1469 → 1591 LOC (+122 LOC)
```

| Change | LOC | Status |
|---|---:|---|
| `import Mathlib.Data.Nat.Choose.Factorization` | +1 | new import |
| `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A) | +51 | sorry-free, axiom-free |
| `factorization_succ_mul_choose_le_log_succ` (28b-1) | +56 | sorry-free, axiom-free |
| Part 4.5 header + docstrings | +11 | doc-only |
| `primorial_le_lcmRange` n=0 drift fix | +3 / -1 | mechanic fix |
| `example :` line 1012 drift fix | +3 / -1 | mechanic fix |

Sorries: **0 → 0** (unchanged).
Axioms: **1 → 1** (`hanson_bound` unchanged; 28b-1 is a step toward elimination, not the elimination itself).

## §2 — Mathlib v4.26.0 lemmas used (all pre-verified at pin)

| Lemma | File | Line at v4.26.0 |
|---|---|---:|
| `Nat.factorization_choose` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 131 |
| `Nat.ordProj_dvd` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 273 |
| `Nat.log_mono_right` | `Mathlib/Data/Nat/Log.lean` | 259 |
| `Nat.le_log_of_pow_le` | `Mathlib/Data/Nat/Log.lean` | 176 |
| `Nat.pow_pos` | core | n/a |
| `Nat.pow_dvd_pow` | core | n/a |
| `Nat.pow_le_pow_left/right` | core | n/a |
| `Nat.dvd_iff_mod_eq_zero` | core / Mathlib | n/a (no positivity arg) |
| `Nat.add_mod`, `Nat.mod_lt`, `Nat.mod_eq_of_lt`, `Nat.mod_eq_sub_mod` | core | n/a |
| `Nat.add_sub_cancel'` | core | n/a |
| `Nat.lt_succ_iff`, `Nat.le_of_dvd`, `Nat.succ_pos`, `Nat.succ_ne_zero`, `Nat.le_succ` | core | n/a |
| `Nat.card_Ico` | `Mathlib/Order/Interval/Finset/Nat.lean` | n/a |
| `Finset.mem_filter`, `Finset.mem_Ico`, `Finset.card_le_card` | `Mathlib/Data/Finset/...` | n/a |

**Zero new Mathlib imports** beyond the single line added to the file header.

## §3 — Build status

```
$ ./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03
...
⚠ [3066/3066] Built Proofs.BaselProblemOQ01OQ01OQ02OQ03 (4.0s)
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean:97:30: unused variable `hn`
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean:270:12: `Finsupp.not_mem_support_iff` has been deprecated: Use `Finsupp.notMem_support_iff` instead
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean:650:39: unused variable `hp`
Build completed successfully (3066 jobs).
```

**3066/3066 jobs clean.** Only linter warnings remain (unused-variable / deprecation), all pre-existing (not introduced by Iter 34 edits).

This is the **first build-verified state** for this slug since Iter 27 ACT (which was merged "build pending" 2026-05-12). The Iter 33 PREP §6 §6.1 race-safety scan listed 2 open PRs on this slug (#17619 Iter 17, #17551 Iter 15) both **CONFLICTING** since 2026-05-09 — they remain stale and are not affected by this ACT.

## §4 — What this Iter 34 ACT does NOT close

Per Iter 31 PREP §4 decomposition:

* **28b-2 (witness saturation)** — Iter 32 PREP (#18682) hand-proof of `k₀ = (n+1) - p^e` saturating the bound is **still open as a Lean ACT** (~35–50 LOC follow-up).
* **28b-3 (assembly)** — combining 28b-1 + 28b-2 + `prime_pow_dvd_lcmRange` (file line 133) + `lcmRange_eq_prod_prime_powers` (file line 299) to derive `choose_mul_succ_dvd_lcmRange` (the Iter 28 ACT master target) is the natural next step (~30 LOC follow-up).
* **Iter 28a (Beta-integral identity)** — `Real.betaIntegral`-side identity (~60–100 LOC, separate Mathlib analysis) for Iter 35+.
* **The polynomial-choice + analytic estimate steps** (Iter 36+) — Hanson's main Beta-integral route closure.
* **The `hanson_bound` axiom itself** — still axiomatized.

The Iter 34 ACT advances the chain by **one of approximately five Lean-amenable steps** identified in Iter 28 PREP's roadmap. The path from `factorization_succ_mul_choose_le_log_succ` to `axiom hanson_bound` discharge is well-mapped by Iter 28–33 PREP chain, but each remaining step needs its own ACT.

## §5 — Honesty caveats

* **No new axioms.** The trusted-axiom set for this file remains `{ofReduceBool, propext, Classical.choice, Quot.sound, hanson_bound}` (the first 4 from `native_decide`/`decide` already in scope from Iter 27's `hanson_n*` witnesses; the 5th is the open conjecture).
* **No `sorry`.** All Lemma A's 3 mechanical TODOs from Iter 33 PREP §2.1 were resolved without inserting `sorry`. The §2.1 #1 (`Nat.mod_eq_zero_of_dvd` vs `Nat.mod_eq_zero_iff_dvd`) was resolved by `Nat.dvd_iff_mod_eq_zero.mp` (no positivity arg needed; the lemma takes implicit args). The §2.1 #2 (`Nat.sub_one_mod` chain) was resolved by an `rcases Nat.lt_or_ge` + `absurd ... Nat.succ_ne_zero` pattern. The §2.1 #3 (`Nat.le_log_of_pow_le`) was confirmed at line 176 of `Mathlib/Data/Nat/Log.lean` at v4.26.0.
* **28b-1's strength relative to existing Mathlib.** The pre-existing `Nat.factorization_choose_le_log` (`Choose/Factorization.lean:185`) gives `v_p(C(n,k)) ≤ log_p n`. This Iter 34 theorem gives the strictly stronger `v_p(n+1) + v_p(C(n,k)) ≤ log_p(n+1)` (modulo `log_p n ≤ log_p(n+1)`); the gain is the `v_p(n+1)` summand on the left, which is positive precisely when `p ∣ n+1`. This sharper form is what the Iter 28 ACT master target `choose_mul_succ_dvd_lcmRange` consumes via unique factorisation.
* **Pre-existing drift fix scope.** The 2 drift fixes at lines 573 and 1012 are pre-existing v4.26.0 simp/decide-set regressions (NOT introduced by Iter 27 ACT — Iter 27 added `native_decide` witnesses that built clean — but introduced when v4.26.0 changed `Nat.decidablePrime`'s reduction behaviour and the `primorial` simp lemma set). They are bundled into this PR per the `parent_file_build_unblocker_inpr` pattern (≤3-LOC parent fix INTO research PR).
* **No edits to state.md / problem.md / meta.json outside the standard state.md ACT-iteration log entry.**

## §6 — Race-safety

### §6.1 Pre-claim PR scan

```
$ gh pr list -R rjwalters/lean-genius \
    --search "basel-problem-oq-01-oq-01-oq-02-oq-03 in:title" --state open
17619  Iter 17 — correction factor supported on small primes (build pending)  2026-05-09 02:25 UTC  (5d stale, CONFLICTING)
17551  Iter 15 — π(n) ≤ n-2 for n≥4 via erasing the smallest even composite  2026-05-09 00:02 UTC  (5d stale, CONFLICTING)

$ gh pr list -R rjwalters/lean-genius \
    --search "basel iter 34 in:title OR basel 28b in:title OR basel 28b-1 in:title" --state all
(empty)
```

Both open PRs are stale Iter 15/17 work on **falsified routes** (Iter 25/26 superseded). They do not touch the `Part 4.5` insertion zone or `factorization_choose`-related infrastructure.

### §6.2 Pre-push PR scan

To be re-run immediately before `git push` to catch any concurrent claim.

### §6.3 No concurrent claim/PR on Iter 34 target

Verified: no PR with title containing "Iter 34", "28b", or "28b-1" exists in any state.

## §7 — Next session candidates

In priority order (Iter 31 PREP §4 decomposition order):

1. **Iter 35a ACT — 28b-2 (witness saturation, Iter 32 PREP)**. The Iter 32 PREP §2 hand-proof for `k₀ = (n+1) - p^e` is ready for Lean (~35–50 LOC). Recommended next.
2. **Iter 35b ACT — 28b-3 (assembly)** — once both 28b-1 (this ACT) and 28b-2 land, the strong-form identity + `choose_mul_succ_dvd_lcmRange` follow in ~30 LOC.
3. **Iter 36 ACT — `betaIntegral_kn`** (Iter 29 ACT target). `Real.betaIntegral`-side, ~60-100 LOC standalone.

The numerical floor (`hanson_n25..hanson_n100`, Iter 27) covers `n ≤ 100`, so any `n₀` threshold for the asymptotic route is well-budgeted.
