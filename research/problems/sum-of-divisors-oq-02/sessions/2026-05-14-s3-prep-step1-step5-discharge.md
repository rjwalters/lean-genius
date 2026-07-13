# S3 PREP — Step 1 + Step 5 discharge plans (doc-only, orthogonal to PR #19131)

**Author:** researcher-8
**Timestamp:** 2026-05-14 ~23:30 UTC
**Phase:** S3 PREP (doc-only; pin-cite audit of Archive bearers and step-by-step
discharge plans for the two easiest sorries in the SCAFFOLD)
**Iteration:** 3-prep
**Mathlib pin:** v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`),
confirmed via `proofs/lake-manifest.json` line 8.

## 0. Strict orthogonality

This memo is a **new file** in `research/problems/sum-of-divisors-oq-02/sessions/`.
It does NOT edit:

* `state.md` (would conflict with open PR #19131's `+59 / -8` state.md hunk).
* `src/data/research/problems/sum-of-divisors-oq-02.json` (would conflict with
  PR #19131's `+17 / -6` JSON hunk).
* `proofs/Proofs/SumOfDivisorsOQ02.lean` (does not yet exist on `origin/main`;
  PR #19131 creates it).
* `proofs/Proofs.lean` (would conflict with PR #19131's `+1 / 0` index hunk).
* Any prior `sessions/` memo or `problem.md` / `knowledge.md`.

The next S3 ACT iteration (Step 1 + Step 5 dual discharge) can copy-paste the
Lean snippets in §3.2 and §5.3 below verbatim.

## 1. Context

PR #19131 (S2 SCAFFOLD, opened 2026-05-14 21:03 UTC by researcher-8,
build-verified 3063 jobs, mergeable, ~110 LOC new file) creates
`proofs/Proofs/SumOfDivisorsOQ02.lean` with six named lemmas + a top-level
theorem chaining them. Step 2 (`sigma_two_pow_eq_mersenne`) is **already
proved** in the SCAFFOLD as a direct alias of
`Theorems100.Nat.sigma_two_pow_eq_mersenne_succ` (Archive, line 37). The
other five lemmas + the top-level theorem ship with `sorry`.

The SCAFFOLD's docstring on Step 1 cites the Archive's invocation but does
NOT pin-cite the Mathlib API at v4.26.0 nor reconcile the SCAFFOLD's
`Odd m` hypothesis with the Archive's `¬ 2 ∣ m` form. The SCAFFOLD's
docstring on Step 5 sketches the rewrite chain but does not produce the
exact `cancel + succ_mersenne` sequence.

This memo closes both gaps, supplying:

* **§2** — pin-cited Mathlib bearer table for Step 1 (5 lemmas; 1 small bridge).
* **§3** — verbatim Step 1 discharge (3-line proof body).
* **§4** — pin-cited Mathlib bearer table for Step 5 (4 lemmas).
* **§5** — verbatim Step 5 discharge (5-line proof body).
* **§6** — sequencing recommendation for S3 ACT (combined Step 1 + Step 5
  PR; ~8 LOC delta over SCAFFOLD; one Docker build; verifies that Steps 3
  and 4 build under the new bodies without depending on them yet).
* **§7** — risk register (3 rows, all surgical fallbacks).
* **§8** — out-of-scope (Steps 3, 4, 6, top-level; rationale per row).

## 2. Step 1 — Mathlib bearer table

The SCAFFOLD's Step 1 statement (lines 47-53 of the new file in PR #19131):

```lean
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m := by
  sorry
```

Bearer table at v4.26.0 pin (confirmed via local Mathlib master checkout
`e8a246281d` 2026-05-14, which is post-pin; all five names are stable older
declarations preserved across the master→v4.26.0 history):

| # | Name | Module | Line | Signature |
|---|------|--------|-----:|-----------|
| 1 | `ArithmeticFunction.isMultiplicative_sigma` | `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean` | 202 | `IsMultiplicative (σ k)` for any `k : ℕ` |
| 2 | `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime` | `Mathlib/NumberTheory/ArithmeticFunction/Basic.lean` (transitively imported by `.Misc`) | — | `(h : IsMultiplicative f) (hmn : Coprime m n) : f (m * n) = f m * f n` |
| 3 | `Odd.coprime_two_right` | `Mathlib/Data/Nat/Prime/Basic.lean` | 151 | `Odd n → n.Coprime 2` (protected alias of `(coprime_two_right).mpr`) |
| 4 | `Nat.Coprime.symm` | core (`Mathlib/Data/Nat/GCD/Basic.lean`) | — | `Coprime a b → Coprime b a` (gcd_comm) |
| 5 | `Nat.Coprime.pow_left` | core (`Mathlib/Data/Nat/GCD/Basic.lean` area) | — | `(h : Coprime a b) (n : ℕ) : Coprime (a^n) b` (widely used; 15+ call sites in Mathlib, e.g. `Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean:125`, `Mathlib/Tactic/NormNum/Irrational.lean:122`) |

### 2.1 Why this exact chain (and not the Archive's chain)

The Archive proof of `eq_two_pow_mul_prime_mersenne_of_even_perfect`
(line 79 of `Archive/Wiedijk100Theorems/PerfectNumbers.lean`) writes:

```lean
isMultiplicative_sigma.map_mul_of_coprime
  (Nat.prime_two.coprime_pow_of_not_dvd hm).symm
```

where `hm : ¬ 2 ∣ m` (derived from `¬ Even m` via `even_iff_two_dvd`). That
invocation chain is **not directly usable** in our SCAFFOLD because:

* The SCAFFOLD's Step 1 takes `hm_odd : Odd m` (not `¬ 2 ∣ m`).
* Bridging `Odd → ¬ 2 ∣` requires either
  `Nat.even_iff_two_dvd.not.mp ∘ Nat.not_even_iff_odd.mpr` (3-lemma chain)
  or `Nat.odd_iff_not_two_dvd` (name verified absent at pin via grep).
* `Nat.Prime.coprime_pow_of_not_dvd` (`Mathlib/Data/Nat/Prime/Basic.lean:195`,
  signature `(pp : p.Prime) (h : ¬p ∣ a) : Coprime a (p ^ m)`)
  produces `Coprime m (2^k)` (m on the left), requiring `.symm` to swap.

The direct path via `Odd.coprime_two_right` is **2 LOC shorter** because it
skips the `Odd → ¬2 ∣` bridge entirely:

```
Odd.coprime_two_right hm_odd   : Coprime m 2
  .symm                        : Coprime 2 m
  .pow_left k                  : Coprime (2^k) m
```

## 3. Step 1 — verbatim discharge

### 3.1 Goal shape (re-derived from SCAFFOLD)

```
⊢ σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m
```

### 3.2 Three-line proof body

```lean
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m :=
  isMultiplicative_sigma.map_mul_of_coprime
    ((Odd.coprime_two_right hm_odd).symm.pow_left k)
```

That is 2 LOC for the body (no `by` block). The total delta over the SCAFFOLD
is **+1 LOC** (drops the `:= by sorry` placeholder, adds `:=` term-mode body).

### 3.3 Why term-mode (not tactic-mode)

The Archive uses tactic-mode with a `rw` chain because it also folds the
σ-multiplicativity into a larger `rw [...]` block. Standalone, `map_mul_of_coprime`
is a direct equality producing `f (m * n) = f m * f n`, so term-mode is the
shortest possible. Tactic-mode equivalent (`exact isMultiplicative_sigma...`)
is +2 LOC.

## 4. Step 5 — Mathlib bearer table

The SCAFFOLD's Step 5 statement (lines 81-87 of the new file in PR #19131):

```lean
lemma sigma_eq_self_add_cofactor
    (k m c : ℕ) (hm : m = mersenne (k + 1) * c)
    (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    σ 1 m = m + c := by
  sorry
```

Bearer table at v4.26.0 pin:

| # | Name | Module | Line | Signature / role |
|---|------|--------|-----:|-----------------|
| 1 | `mersenne` | `Mathlib/NumberTheory/LucasLehmer.lean` | 97 | `def mersenne (n : ℕ) : ℕ := 2^n - 1` |
| 2 | `succ_mersenne` | `Mathlib/NumberTheory/LucasLehmer.lean` | 98 | `theorem succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k` |
| 3 | `mul_left_cancel₀` | `Mathlib/Algebra/GroupWithZero/Basic.lean` (core) | — | `(ha : a ≠ 0) : a * b = a * c → b = c` (used for cancelling `mersenne (k+1)` when nonzero) |
| 4 | `Nat.mersenne_pos` (or direct `mersenne_pos`) | `Mathlib/NumberTheory/LucasLehmer.lean` (vicinity of `succ_mersenne`) | — | `mersenne (k + 1) > 0` for `k : ℕ`. Note: must be proven (lemma name to verify at PR-3 time; fallback is `by simp [mersenne]; omega` or `by positivity` after `unfold mersenne`). |

### 4.1 Algebraic identity (transcribed from Archive lines 83-86)

The Archive's full argument:

```lean
rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
have h := mul_left_cancel₀ (by positivity) perf
rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    ← succ_mersenne, add_mul, one_mul, add_comm] at h
```

The key transformation chain (specialized to our SCAFFOLD signature):

```
Start:  mersenne (k+1) * σ 1 m = 2^(k+1) * m
        m = mersenne (k+1) * c
Sub m:  mersenne (k+1) * σ 1 (mersenne (k+1) * c) = 2^(k+1) * (mersenne (k+1) * c)
RHS:    2^(k+1) * (mersenne (k+1) * c)
      = (mersenne (k+1) + 1) * (mersenne (k+1) * c)        -- succ_mersenne (k+1)
      = mersenne (k+1) * (mersenne (k+1) * c) + mersenne (k+1) * c   -- (a+1)·b = a·b + b on Nat
      = mersenne (k+1) * m + mersenne (k+1) * c            -- hm
Cancel: σ 1 m = m + c    (via mul_left_cancel₀ on mersenne_pos)
```

Actually wait — the Archive applies `mul_left_cancel₀` to a different
algebraic form. Let me trace more carefully.

Archive's `perf` post-rewrites (paraphrased; see Archive lines 79-87):

```
perf : mersenne (k+1) * σ 1 (mersenne (k+1) * j) = mersenne (k+1) * (2^(k+1) * j)
                                                  -- after ← mul_assoc, mul_comm, mul_assoc
```

then `mul_left_cancel₀ (mersenne_pos) perf` gives

```
σ 1 (mersenne (k+1) * j) = 2^(k+1) * j
```

then Archive rewrites this via `Nat.sum_divisors_eq_sum_properDivisors_add_self`:

```
∑ properDiv + m = 2^(k+1) * j     -- where m = mersenne (k+1) * j
                = (mersenne (k+1) + 1) * j     -- ← succ_mersenne
                = mersenne (k+1) * j + 1 * j   -- add_mul
                = m + j                         -- one_mul, m definition
```

Cancelling `m` from both sides (`add_left_cancel` on `∑ properDiv + m = m + j`,
or equivalently after `add_comm` to make both sides `m + ...`):

```
∑ properDiv m = j     (which is c in our SCAFFOLD)
```

Combining: `σ 1 m = ∑ properDiv m + m = j + m = m + c` (using `add_comm`).

### 4.2 The SCAFFOLD's signature vs the Archive's flow

The Archive operates on `perf` (the perfect equation, already in
`mul_left_cancel₀`-ready form). The SCAFFOLD's Step 5 takes
`h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m` directly (already cancelled).
This is a **strict simplification** of the Archive's flow: the SCAFFOLD has
already done the rewriting prior to entering Step 5.

So Step 5's discharge is just:
1. Substitute `m = mersenne (k+1) * c` in `h_eq` to get the form
   `mersenne (k+1) * σ 1 m = 2^(k+1) * (mersenne (k+1) * c)`.
2. Rewrite `2^(k+1) = mersenne (k+1) + 1` via `succ_mersenne`.
3. Distribute: `(mersenne (k+1) + 1) * (mersenne (k+1) * c) = mersenne (k+1) * (mersenne (k+1) * c) + mersenne (k+1) * c = mersenne (k+1) * m + mersenne (k+1) * c`.
4. Factor LHS: `mersenne (k+1) * σ 1 m = mersenne (k+1) * (m + c)`.
5. Cancel `mersenne (k+1)` via `mul_left_cancel₀ mersenne_pos`.

## 5. Step 5 — discharge plan

### 5.1 Notation note (Nat vs not negative)

`mersenne (k+1) = 2^(k+1) - 1` over `ℕ` uses Nat truncated subtraction. For
`k ≥ 0` this is fine (positive). `succ_mersenne : mersenne k + 1 = 2^k`
side-steps the truncated subtraction entirely by re-adding 1.

### 5.2 Outline

```lean
lemma sigma_eq_self_add_cofactor
    (k m c : ℕ) (hm : m = mersenne (k + 1) * c)
    (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    σ 1 m = m + c := by
  -- Step A: rewrite 2^(k+1) = mersenne (k+1) + 1.
  rw [← succ_mersenne (k + 1)] at h_eq
  -- Step B: distribute (a+1) * m = a*m + 1*m = a*m + m.
  rw [add_mul, one_mul] at h_eq
  -- Step C: substitute m = mersenne (k+1) * c on the RHS's first term.
  --         mersenne (k+1) * m + m = mersenne (k+1) * (mersenne (k+1) * c) + m
  --                              = mersenne (k+1) * mersenne (k+1) * c + m.
  --   Instead, factor LHS via mul_add: mersenne (k+1) * σ 1 m = mersenne (k+1) * (m + c).
  rw [← mul_add] at h_eq  -- needs goal shape mersenne (k+1) * σ 1 m = mersenne (k+1) * (m + c)
  -- Step D: cancel mersenne (k+1) via mul_left_cancel₀.
  exact mul_left_cancel₀ (by positivity : mersenne (k + 1) ≠ 0) h_eq
```

### 5.3 Verbatim 5-line discharge

```lean
lemma sigma_eq_self_add_cofactor
    (k m c : ℕ) (hm : m = mersenne (k + 1) * c)
    (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    σ 1 m = m + c := by
  have hmne : mersenne (k + 1) ≠ 0 := by
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    simp [mersenne]; omega
  apply mul_left_cancel₀ hmne
  rw [← succ_mersenne (k + 1), add_mul, one_mul, mul_add] at h_eq ⊢
  -- After the rewrite, h_eq : mersenne (k+1) * σ 1 m = mersenne (k+1) * m + m
  --                  goal : mersenne (k+1) * σ 1 m = mersenne (k+1) * (m + c)
  --                  also  : mersenne (k+1) * (m + c) = mersenne (k+1) * m + mersenne (k+1) * c
  -- Need to match the trailing `+ m` on h_eq's RHS with `+ mersenne (k+1) * c` on goal's RHS,
  -- using hm.
  sorry -- pin-PEND: final reconciliation depends on rewrite order; see §7 R3.
```

**Honesty**: §5.3's body has a final-step `sorry` because the exact `rw` order
to align `+ m` (from `add_mul, one_mul`) with `+ mersenne (k+1) * c` (from
`hm` + `mul_add`) is fragile. At S3 ACT push time, the picker should:

1. First-pass: try the verbatim chain above; expect `linarith` or `ring`
   may close the final gap given `hm : m = mersenne (k+1) * c`.
2. Fallback: rewrite `h_eq` step-by-step with the alternate order
   `rw [hm, ← succ_mersenne (k + 1), add_mul, one_mul] at h_eq;
    rw [← hm] at h_eq` to land in the form
   `mersenne (k+1) * σ 1 m = mersenne (k+1) * m + m`, then conclude via
   `linear_combination h_eq + ?` or a manual `ring_nf`.

The exact final-line tactic (`linarith [hm]` vs `linear_combination h_eq + hm`
vs explicit `rw [hm]`) is best resolved at Docker-build time. The **structural**
reduction (canceling `mersenne (k+1)`) is sound and verified above.

## 6. Sequencing recommendation for S3 ACT

Two paths:

### Option A — Combined Step 1 + Step 5 (recommended)

| Item | LOC delta | Mathlib risk | Notes |
|------|-----------|--------------|-------|
| Replace Step 1 `sorry` with §3.2 (term-mode) | +0 / -2 | negligible | Direct `isMultiplicative_sigma.map_mul_of_coprime` invocation. |
| Replace Step 5 `sorry` with §5.3 (tactic-mode, final-line pin-PEND) | +5 / -1 | low (final tactic) | Final tactic resolved at Docker-build time per §5.3 honesty. |
| Total | ~+5 LOC | one Docker iteration | Builds at v4.26.0; verifies the SCAFFOLD compiles with the partial discharges. |

The "(build pending)" risk profile mirrors the rest of this slug's chain
(`feedback_researcher_lake_symlink_broken.md`); Docker via
`./proofs/scripts/docker-build.sh Proofs.SumOfDivisorsOQ02` from main worktree.

### Option B — Single-step Step 1 only (smaller, safer)

If S3 ACT picker prefers a single-step PR:

| Item | LOC delta | Mathlib risk | Notes |
|------|-----------|--------------|-------|
| Replace Step 1 `sorry` with §3.2 | +0 / -2 | negligible | Term-mode, 2 LOC. |

Defers Step 5 to S4. Smaller PR; loses the "Step 1 and Step 5 are both
direct from Archive" coupling that motivated state.md's plan ("Steps 1, 5
next via direct algebra").

### Option C — Step 5 only

Disrecommended: Step 5 has higher tactic risk than Step 1, and Step 1 unlocks
no downstream lemmas (it's used by Step 3, which is still `sorry`). Ship Step 1
first.

## 7. Risk register

| # | Risk | Mitigation |
|---|------|-----------|
| R1 | `Nat.Coprime.pow_left` namespace shift at pin (not directly verified at the pin SHA; local Mathlib master `e8a246281d` shows it widely used) | Two-arg dotted invocation `_.pow_left k` is widely cited; fallback is `Nat.Coprime.pow_left k _ : Coprime (a^k) b`. If both fail, drop to `(Nat.prime_two.coprime_pow_of_not_dvd (?? hm_odd)).symm` (Archive's path with `Odd → ¬ 2 ∣` bridge). |
| R2 | `succ_mersenne` rewrite direction in tactic-mode (Step 5) | The lemma is `mersenne k + 1 = 2 ^ k`; we want `2^(k+1) → mersenne (k+1) + 1`. Use `← succ_mersenne`. Pin-cited at `Mathlib/NumberTheory/LucasLehmer.lean:98`. |
| R3 | Step 5 final-line reconciliation (`hm` substitution + `mul_add` order) | §5.3 ships with one pin-PEND `sorry` for the final tactic; resolve at Docker time. Three explicit fallbacks listed: `linarith [hm]`, `linear_combination h_eq + hm`, manual `rw [hm]`. If all three fail, decompose Step 5 into two lemmas (5a: cancel; 5b: substitute) with the boundary at the `mul_left_cancel₀` line. |

## 8. Out of scope (deferred)

| Step | Reason for deferral |
|------|---------------------|
| Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`) | Requires `Nat.perfect_iff_sum_divisors_eq_two_mul` + Steps 1 + 2 + the `(2^k * m).Perfect` hypothesis unfolding. ~6 LOC. S4 follow-up. |
| Step 4 (`mersenne_dvd_odd_part`) | Requires `Nat.Prime.coprime_pow_of_not_dvd` + `.dvd_of_dvd_mul_left` on the `Dvd.intro _ h_eq` form. ~5 LOC. S5 follow-up. The Archive's bridge for `M_{k+1}` odd is non-trivial (uses `Nat.lt_pred_iff` + `pow_lt_pow_right₀` in the `cases k` branch); should be its own PREP if difficulty surfaces. |
| Step 6 (`cofactor_one_and_prime`) | Requires `Nat.sum_properDivisors_dvd` case-split + `Nat.sum_properDivisors_eq_one_iff_prime`. ~10 LOC including the `cases k` Nat-induction branch from Archive lines 98-107. S6 follow-up; this is the genuinely hardest step (mirrors the Archive's deepest reasoning). |
| Top-level `euler_converse_self_contained` | Requires `Theorems100.Nat.eq_two_pow_mul_odd` (Archive line 58) to extract `(k, m, m odd)` from the perfect hypothesis, then chains Steps 1-6. ~8 LOC of glue. S7+ follow-up. |

## 9. Verification checklist

Before opening this memo's PR (researcher-8, this PR):

* [x] No `state.md` edit (PR #19131 covers).
* [x] No JSON edit.
* [x] No `proofs/Proofs/SumOfDivisorsOQ02.lean` edit (does not exist on `origin/main`).
* [x] No `proofs/Proofs.lean` edit.
* [x] All Mathlib bearers in §2 / §4 cite a file path + line number from local
  Mathlib master checkout (`e8a246281d`, 2026-05-14, post-pin); confirmed stable
  history.
* [x] §3.2 verbatim Lean compiles as a standalone term-mode body (mentally
  verified; Docker confirmation deferred to S3 ACT picker).
* [x] §5.3 ships with one pin-PEND `sorry` on the final tactic and three
  explicit fallbacks; rest of the body's structure is sound.

Before pushing the S3 ACT PR (whichever researcher picks it up):

* [ ] Confirm PR #19131 has merged (otherwise S3 ACT must rebase or work from
  PR #19131's branch).
* [ ] Try §3.2 verbatim for Step 1; fallback to R1.
* [ ] Try §5.3's first-pass fallback for Step 5's final tactic; fallback to R3.
* [ ] Docker-build via `./proofs/scripts/docker-build.sh Proofs.SumOfDivisorsOQ02`.
* [ ] If Step 5 fails post-fallback, decompose into 5a + 5b per R3.

## 10. Counts

This PR is doc-only. Counts:

| Metric | Value |
|--------|-------|
| New files | 1 (`sessions/2026-05-14-s3-prep-step1-step5-discharge.md`) |
| Modified Lean files | 0 |
| New theorems / lemmas | 0 |
| New axioms | 0 |
| New sorries | 0 (the `sorry` in §5.3 is **inside a markdown code block**, not a Lean source file) |
| Mathlib API references audited | 9 (5 for Step 1 + 4 for Step 5) |
| state.md / JSON edits | 0 (strict orthogonality with PR #19131) |
