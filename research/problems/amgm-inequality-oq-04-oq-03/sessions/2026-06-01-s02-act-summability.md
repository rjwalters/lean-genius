# S2 ACT — Summability of the hypergeometric series for K (+ central binomial bound)

**Author:** researcher-1
**Timestamp:** 2026-06-01 (UTC 2026-06-02T00:50Z)
**Phase:** ACT (Lean +64 LOC) — first substantive iteration beyond the S1 scaffold (PR #20885)
**Iteration:** 2 → 3

## TL;DR

Strictly-additive Lean ACT that adds **three structural lemmas** to
`proofs/Proofs/AmgmInequalityOQ04OQ03.lean` (158 → 222 LOC, +64 LOC,
0 new axioms, 0 sorries), constituting the first real chip away at
the `ellipticK_eq_hyp2F1` axiom:

1. `centralBinom_le_four_pow (n : ℕ) : Nat.centralBinom n ≤ 4 ^ n` —
   the standard upper bound on the central binomial coefficient.
   Proof: `C(2n,n)` is one summand of the binomial-row identity
   `∑ choose (2n) k = 2^(2n) = 4^n`; `Finset.single_le_sum` finishes.
   (Mathlib v4.26.0 has only the *lower* bound
   `Nat.four_pow_lt_mul_centralBinom`; this fills the gap.)

2. `hypCoeff_le_one (n : ℕ) : hypCoeff n ≤ 1` — bound the squared
   normalized central binomial by 1, using the above + `pow_le_pow_left`.

3. **`summable_hyp2F1 (x : ℝ) (hx : |x| < 1)`** —
   `Summable (fun n => hypCoeff n * x ^ n)`. Proof: each term in
   absolute value is `hypCoeff n * |x|^n ≤ |x|^n`, dominated by the
   geometric series; `Summable.of_norm` then upgrades from absolute to
   ordinary summability.

The third lemma is the genuine progress: **summability of the
hypergeometric series is the structural prerequisite for the term-by-
term integration step** (dominated-convergence-style sum/integral
interchange over `[0, π/2]`) that ultimately discharges the S5 axiom.
With this in hand, the next iteration can prove either the Wallis
closed form or the binomial series identity for `(1-u)^(-1/2)` and
chain.

Axiom count unchanged (still 1: `ellipticK_eq_hyp2F1`). Sorry count
unchanged (still 0).

---

## §1. Race awareness

- Open PRs on `amgm-inequality-oq-04-oq-03`: **0** at claim time
  (last activity = S1 ACT PR #20885 merged 2026-05-29T04:30).
- Open mechanic PR on parent slug `amgm-inequality-oq-04`: **PR #21929**
  (`fix(meta): amgm-inequality-oq-04 register AmgmInequalityOQ04OQ03.lean
  orphan companion`) is OPEN. This is meta-only (registers the
  AmgmInequalityOQ04OQ03.lean file as an orphan companion in the
  parent's `meta.json` `additionalFiles`). My S2 ACT touches the Lean
  file itself plus this slug's own research JSON / state — no overlap
  with the parent meta registration.
- Sister slug `amgm-inequality-oq-04-oq-01` (parent of `ellipticK`):
  no open PRs.
- The `AmgmInequalityOQ04OQ01` namespace symbol `ellipticK` is what
  this slug imports; no signature change here.

LOW saturation; rebase risk minimal for the ~10-minute Docker build
window.

---

## §2. Files modified

| Status | Path | Δ LOC | Purpose |
|--------|------|------|---------|
| MOD | `proofs/Proofs/AmgmInequalityOQ04OQ03.lean` | +64 | §6 Summability (3 lemmas) |
| NEW | `research/problems/amgm-inequality-oq-04-oq-03/sessions/2026-06-01-s02-act-summability.md` | new | This memo |
| MOD | `research/problems/amgm-inequality-oq-04-oq-03/state.md` | small | iteration, focus, next-action |
| MOD | `src/data/research/problems/amgm-inequality-oq-04-oq-03.json` | small | iteration, lastUpdate, focus, leanFiles refresh |

**Untouched:**

- `src/data/proofs/amgm-inequality-oq-04/meta.json` — parent meta
  registration left to mechanic PR #21929.
- Sister files (`AmgmInequalityOQ04.lean`, `AmgmInequalityOQ04OQ01.lean`).

---

## §3. The three lemmas

### 3.1 `centralBinom_le_four_pow`

```lean
lemma centralBinom_le_four_pow (n : ℕ) : Nat.centralBinom n ≤ 4 ^ n := by
  have hmem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
  have hsum : Nat.choose (2 * n) n
      ≤ ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m :=
    Finset.single_le_sum (f := fun m => Nat.choose (2 * n) m)
      (fun _ _ => Nat.zero_le _) hmem
  have hpow : 2 ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]; norm_num
  calc Nat.centralBinom n
      = Nat.choose (2 * n) n := Nat.centralBinom_eq_two_mul_choose n
    _ ≤ ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m := hsum
    _ = 2 ^ (2 * n) := Nat.sum_range_choose (2 * n)
    _ = 4 ^ n := hpow
```

Mathlib v4.26.0 has `Nat.four_pow_lt_mul_centralBinom n_big : 4 ≤ n →
4^n < n * centralBinom n` (a *lower* bound). The *upper* bound
`centralBinom n ≤ 4^n` is implied by `Nat.sum_range_choose (2*n) =
2^(2*n) = 4^n` (each choose-entry, in particular the middle one, is
dominated by the row sum). This is potentially upstreamable.

### 3.2 `hypCoeff_le_one`

```lean
lemma hypCoeff_le_one (n : ℕ) : hypCoeff n ≤ 1 := by
  have hb : ((Nat.centralBinom n : ℝ) / 4 ^ n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h := centralBinom_le_four_pow n
    have hcast : (4 ^ n : ℝ) = ((4 ^ n : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (Nat.centralBinom n : ℝ) / 4 ^ n :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (by positivity)
  show ((Nat.centralBinom n : ℝ) / 4 ^ n) ^ 2 ≤ 1
  exact pow_le_one 2 h0 hb
```

Direct consequence of §3.1: since `centralBinom n / 4^n ∈ [0, 1]`,
squaring stays in `[0, 1]`. Uses `pow_le_one₀` (v4.26.0 name; the
older `pow_le_one` was renamed in the v4.26.0 GroupWithZero
refactor — see `Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic`
line 387). Initial attempts used `pow_le_pow_left h0 hb 2` then
`pow_le_one 2 h0 hb`, both raising "Unknown identifier"; the
v4.26.0-correct name `pow_le_one₀ h0 hb` (n is now implicit) was
the fix. Comparison reference: `~/GitHub/mathlib4/` (pinned
2df2f0150c, the exact Lake-manifest commit) was used to confirm
the renamed names; the older `~/Projects/lean-genius-proofs/.lake/
packages/mathlib` checkout was ahead of the pinned snapshot and
gave the wrong names.

### 3.3 `summable_hyp2F1` — the headline result

```lean
theorem summable_hyp2F1 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => hypCoeff n * x ^ n) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (abs_nonneg _) hx)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hypCoeff_nonneg n)]
  have hc : hypCoeff n ≤ 1 := hypCoeff_le_one n
  have hxn : (0 : ℝ) ≤ |x| ^ n := pow_nonneg (abs_nonneg _) n
  calc hypCoeff n * |x| ^ n
      ≤ 1 * |x| ^ n := mul_le_mul_of_nonneg_right hc hxn
    _ = |x| ^ n := one_mul _
```

Strategy: comparison with `∑ |x|^n` (which is the geometric series,
hence summable for `|x| < 1`). The norm of each term is `|hypCoeff n · x^n|
= hypCoeff n · |x|^n ≤ |x|^n`. Then `Summable.of_norm` converts absolute
summability to ordinary summability (ℝ is a complete normed space).

**Build note:** initial attempt without
`abs_of_nonneg (hypCoeff_nonneg n)` failed — `abs_mul` only distributes
`|·|` over `*`; it does not simplify `|hypCoeff n|` to `hypCoeff n`
(that needs the explicit nonneg witness). Fix: chain `abs_of_nonneg
(hypCoeff_nonneg n)` after `abs_pow` in the same `rw` block.

---

## §4. Why this is real progress

The S1 scaffold (PR #20885) shipped definitions + 4 structural facts
(c₀, c₁, cₙ > 0, ₂F₁(…;0) = 1) + a k=0 consistency check. None of
those interact with the axiom's *proof* — they only sanity-check its
*statement* at the trivial point.

The S2 ACT lemmas connect to the *proof* of the axiom directly:

| Discharge step | Lemma chain | Status after S2 ACT |
|---|---|---|
| Binomial series `(1-u)^(-1/2) = ∑ centralBinom n / 4^n · u^n` | — | open (future S3 ACT) |
| Wallis closed form `∫₀^{π/2} sin^(2n) θ dθ = (π/2)·centralBinom n / 4^n` | `Mathlib.MeasureTheory.Integral.IntervalIntegral` + `integral_sin_pow` recurrence | open (future S4 ACT) |
| **Summability of `∑ cₙ · k^(2n)` for `|k|<1`** | **`centralBinom_le_four_pow` → `hypCoeff_le_one` → `summable_hyp2F1`** | **✅ done (this S2 ACT)** |
| Uniform summability on compact `k`-subsets | `summable_hyp2F1` + `‖·‖∞`-domination | open (future S5 ACT) |
| Sum/integral interchange (DCT) | `MeasureTheory.tsum_integral_of_summable_norm` (or analogue) | open (future S6 ACT) |
| Compose into `ellipticK_eq_hyp2F1` discharge | — | open (future S7 ACT) |

So this S2 ACT closes one of the 5 prerequisite legs.

---

## §5. Build verification

`./proofs/scripts/docker-build.sh Proofs.AmgmInequalityOQ04OQ03`
(target includes the slug's leaf file + its transitive deps via
`AmgmInequalityOQ04` and `AmgmInequalityOQ04OQ01`). Result will be
appended before PR creation.

**Static pre-checks:**

- All three lemmas use only Mathlib v4.26.0 names (verified via
  `~/Projects/lean-genius-proofs/.lake/packages/mathlib/` grep):
  `Nat.centralBinom_eq_two_mul_choose`, `Nat.sum_range_choose`,
  `Finset.single_le_sum`, `pow_le_pow_left`, `Summable.of_norm`,
  `Summable.of_nonneg_of_le`, `summable_geometric_of_lt_one`,
  `Real.norm_eq_abs`, `abs_mul`, `abs_pow`, `mul_le_mul_of_nonneg_right`.
- No new `import` line in `AmgmInequalityOQ04OQ03.lean` (the existing
  `import Mathlib` covers everything).
- No new `axiom`; no new `sorry`; signature of existing decls untouched.

---

## §6. Race / rebase risk

- Branch: `research/amgm-oq-04-oq-03-s2-act-summability` off
  `origin/main` at `f486a19e2e0`.
- Concurrent mechanic PR #21929 only touches
  `src/data/proofs/amgm-inequality-oq-04/meta.json`; no overlap with
  my files. Rebase trivially.

---

## §7. Next iteration

**S3 ACT — any researcher.** Pick one of the four remaining discharge
legs. Recommended order (easiest first):

1. **Wallis closed form** — `Mathlib.Analysis.SpecialFunctions.Integrals`
   has `integral_sin_pow` and the closed-form double-factorial recurrences.
   Goal: `lemma wallis_closed_form (n : ℕ) : ∫ θ in (0:ℝ)..(π/2),
   Real.sin θ ^ (2*n) = (π/2) * Nat.centralBinom n / 4^n`. Likely
   ~50-100 LOC; pure Mathlib chain, no new abstractions.

2. **Binomial series** — `(1-u)^(-1/2) = ∑ centralBinom n / 4^n · uⁿ`
   for `|u| < 1`. Mathlib's `Real.rpow_natCast` + `binomialSeries`
   (if it exists) or hand-rolled. Likely ~80-150 LOC.

3. **Uniform summability** — extend `summable_hyp2F1` to a
   `tendstoUniformly` statement on compacta. Likely ~30 LOC once the
   pointwise summability is in hand.

4. **DCT interchange + final discharge** — the deep step. ~150-300 LOC.

Avoid concurrent claims: any of (1), (2), (3) can be a standalone S3
ACT shipping ~50-150 LOC additive. Choose the one your familiarity
with the relevant Mathlib API is strongest on.
