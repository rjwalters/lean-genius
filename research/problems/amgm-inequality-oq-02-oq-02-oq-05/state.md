# Research State: amgm-inequality-oq-02-oq-02-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 9 (PART VIII)

## Iteration 9 (PART VIII — Vieta closure of the TOP step: calculus route reaches Newton's inequality on esymm(roots)), researcher-5
Two verified additions (28 → 30 theorems; 0 sorries, 0 axioms; docker-build clean,
7743 jobs, Lean 4.26.0). **CLOSES the documented Vieta gap for the TOP step** —
substitutes the top three coefficients of the split polynomial via Mathlib's
`Polynomial.coeff_eq_esymm_roots_of_splits`, turning Part VII's coefficient
inequality `newton_top_coeff_ineq` into the classical Newton inequality on the
elementary symmetric functions of the roots. The calculus proof (differentiate →
discriminant → Vieta) now runs end-to-end to a symmetric-function inequality for
every arity `n = m + 2`:
- `newton_top_esymm_roots (m) {p} (hp : p.Splits) (hdeg : p.natDegree = m + 2)` :
  `4·(m+2)!desc·m!desc·lc²·e₂ ≤ ((m+1)!desc)²·lc²·e₁²`, `lc = p.leadingCoeff`,
  `e₁ = p.roots.esymm 1`, `e₂ = p.roots.esymm 2`. The Vieta substitution.
- `newton_top_esymm_roots_monic (m) {p} (hp : p.Splits) (hmonic : p.Monic)
  (hdeg : p.natDegree = m + 2)` : the recognizable classical `2·(m+2)·e₂ ≤
  (m+1)·e₁²`, i.e. the first Newton/Maclaurin inequality for every arity — via the
  calculus route (matching Part III's QM–AM proof of the same inequality).

**What remains (interior steps):** the general interior Newton step
`pₖ² ≥ pₖ₋₁pₖ₊₁` for `2 ≤ k ≤ n−2` needs the same engine on a *sub-window*
iterated derivative isolating `eₖ₋₁,eₖ,eₖ₊₁`. The reciprocal polynomial
`Xⁿ·p(1/X)` (`Polynomial.reverse`) maps the bottom window to the top window, so
the top-step machinery plus a `reverse`-coefficient bridge should reach the
second-from-top / second-from-bottom steps next; strictly interior windows
differentiate both `p` and its reverse. Purely algebraic — no analysis blocker.

**Reusable Lean gotchas (researcher-5, Part VIII):**
- `Polynomial.coeff_eq_esymm_roots_of_splits (hsplit : p.Splits) (h : k ≤
  p.natDegree) : p.coeff k = p.leadingCoeff·(-1)^(natDegree−k)·p.roots.esymm
  (natDegree−k)` (in `RingTheory/Polynomial/Vieta.lean`) is the ready-made Vieta
  substitution for a split polynomial's coefficients — no need to construct
  `∏(X−xᵢ)` by hand. Use `coeff_natDegree` for the top coefficient (`k =
  natDegree`) to avoid unfolding `esymm 0`.
- `newton_top_coeff_ineq` weights are in `(2+m),(1+m),(0+m)` form; `2+m` is a
  STUCK nat, so `rw [show (2:ℕ)+m = m+2 from by omega, …] at h` first to get the
  `succ`-reducible `(m+2)` bases before `Nat.succ_descFactorial` can collapse them.
- Weight collapse `2·(m+2).descFactorial m = (m+2)·(m+1).descFactorial m` and
  `(m+1).descFactorial m = (m+1)·m.descFactorial m` both fall out of
  `Nat.succ_descFactorial`; cast to ℝ then `linear_combination` for
  `2(m+2)B² = (m+1)·4AC`, multiply the inequality by `(m+1)≥0`, cancel `B²>0`.

## Iteration 8 (PART VII — the general-`n` TOP Newton step via the actual Rolle route), researcher-8
Two verified additions (26 → 28 theorems; 0 sorries, 0 axioms; docker-build clean,
7743 jobs, Lean 4.26.0). **Closes the documented "coefficient bookkeeping" gap for
the TOP step at arbitrary arity** — the first time the three engine pieces are run
end-to-end on ONE split polynomial of arbitrary degree:
- `discrim_iterate_derivative_top (m) {p} (hp : Splits p) (hdeg : p.natDegree = m+2)`
  : `0 ≤ discrim ((2+m).descFactorial m • p.coeff (2+m)) ((1+m).descFactorial m •
  p.coeff (1+m)) ((0+m).descFactorial m • p.coeff (0+m))`. Differentiate a split
  degree-`(m+2)` polynomial `m` times → a split *quadratic* (Part V
  `splits_iterate_derivative`), whose discriminant is `≥ 0` (Part VI
  `discrim_coeff_nonneg_of_splits_deg_two`), then read the three coefficients back
  on `p` itself via Mathlib's `Polynomial.coeff_iterate_derivative`. NO sign
  hypothesis (only real-rootedness). The `natDegree = 2` side condition is
  discharged by sandwiching `natDegree_iterate_derivative` (`≤ (m+2)-m = 2`)
  against `le_natDegree_of_ne_zero` on `coeff 2 = (2+m).descFactorial m •
  leadingCoeff p ≠ 0`.
- `newton_top_coeff_ineq (m) {p} …` : the same as the recognizable log-concavity
  inequality `4·(2+m)!desc·m!desc·p.coeff(m+2)·p.coeff m ≤ ((1+m)!desc)²·p.coeff(m+1)²`
  (i.e. `b² ≥ 4ac` on consecutive coefficients), via `rw [discrim]; simp
  [nsmul_eq_mul]; nlinarith`.

**What remains (narrowed to pure Vieta):** specialise `p = ∏(X−xᵢ)` (monic,
`Splits` automatic) and substitute the top coefficients `p.coeff (n−k) = (−1)^k eₖ`
(Vieta / `Polynomial.coeff_prod_X_sub_C` / `Multiset.esymm`) to turn
`newton_top_coeff_ineq` into the classical `pₙ₋₁² ≥ pₙ₋₂ pₙ` for all `n`. This is
now the ONLY missing piece for the general top step and is purely algebraic (no
analysis). The general *interior* steps (`k` strictly between) need the reversed /
sub-window derivative (differentiate to isolate `eₖ₋₁,eₖ,eₖ₊₁` rather than the top
three) — same machinery, different coefficient window.

**Reusable Lean gotchas (researcher-8, Part VII):**
- `Polynomial.coeff_iterate_derivative {k} (p) (m) : ((⇑derivative)^[k] p).coeff m
  = (m + k).descFactorial k • p.coeff (m + k)` — the coefficient of an iterated
  derivative is a `descFactorial`-weighted shifted coefficient. Rewriting produces
  the index in the form `m + k` (e.g. `2 + m`, `0 + m` — NOT normalized to `m`),
  so state the target with `(i + m)` to `rwa` cleanly.
- `Polynomial.natDegree_iterate_derivative (p) (k)` gives only `≤ natDegree p − k`;
  pin equality by pairing it with `le_natDegree_of_ne_zero` on the top coefficient.
- `Nat.descFactorial_pos : 0 < n.descFactorial k ↔ k ≤ n` (use `.mpr (by omega) |>.ne'`
  then `exact_mod_cast` into `ℝ`); `Nat.descFactorial_self : n.descFactorial n = n!`.
- `rw [discrim]` unfolds `discrim a b c = b^2 - 4*a*c` directly (equation lemma),
  then `simp only [nsmul_eq_mul]` + `nlinarith` reconciles the `•` scalars.

## Iteration 7 (PART VI — join the crux to a discriminant; normalized p-form), researcher-11

## Iteration 7 (PART VI — join the crux to a discriminant; normalized p-form), researcher-11
Two verified additions (24 → 26 theorems; 0 sorries, 0 axioms; docker-build clean,
7743 jobs, Lean 4.26.0):
- `discrim_coeff_nonneg_of_splits_deg_two {p : ℝ[X]} (hp : Splits p)
  (hdeg : p.natDegree = 2) : 0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0)` —
  the **first end-to-end join** of the two halves the file had proved only in
  isolation. Part V's `splits_iterate_derivative` reduces a split degree-`n`
  polynomial to a split *quadratic* (its `(n-2)`-nd derivative); this lemma turns
  that quadratic's real-rootedness into Newton's discriminant inequality on its
  three coefficients, in coordinate-free `coeff` form, for all `n`, no sign
  hypothesis. Proof: `splits_iff_card_roots` + `hdeg` gives `card roots = 2 > 0`,
  so `∃ r ∈ roots`; `isRoot_of_mem_roots` + `eval_eq_sum_range` expand
  `p.eval r = 0` to `coeff 2·r² + coeff 1·r + coeff 0 = 0`; the Part I atom
  `discrim_nonneg_of_root` finishes. This is the honest general per-derivative
  Newton step the header/knowledge documented as still missing.
- `newton_first_general_normalized (n : ℕ) (hn : 2 ≤ n) (x : ℕ → ℝ)` — the
  arbitrary-`n` first Newton inequality in genuine normalized p-form
  `p₀·p₂ ≤ p₁²` with `p₁ = e₁/n`, `p₂ = e₂/binom(n,2) = e₂/(n(n-1)/2)`, closing the
  documented "Next Action 2". `newton_first_general` (`2n·e₂ ≤ (n-1)·e₁²`) divided
  down by the binomial normalizations.

**Reusable Lean gotchas (researcher-11, Part VI):**
- `div_le_div_iff` is GONE in Mathlib 4.26.0 ("unknown identifier"); the current
  name is **`div_le_div_iff₀ (hb) (hd) : a/b ≤ c/d ↔ a*d ≤ c*b`**. Same story for
  the `div_le_iff`/`le_div_iff` family → `…₀`.
- `nlinarith`/`ring` over un-abstracted `Finset.sum` atoms (the `e₁`, `e₂` sums)
  can **SIGSEGV/SIGBUS the elaborator (exit 139/135, no diagnostic)**. Fix:
  `set S := ∑ … ; set E := ∑ …` FIRST so nlinarith sees small opaque variables.
  (Independently, concurrent docker builds contend for memory and also surface as
  flaky 135/139 — re-run to distinguish; a clean origin/main build in the same
  container confirms the env is healthy.)
- `eval_eq_sum_range r` (p implicit, x explicit) + `sum_range_succ`×2 +
  `sum_range_one` cleanly unfolds a degree-≤2 `p.eval r` into its three coeffs;
  `linear_combination` reconciles `r^0/r^1/r^2` with `r*r`.

## Iteration 6 (PART V — general Rolle crux, closed via Mathlib)

## Iteration 6 (PART V — general Rolle crux, closed via Mathlib)
**Retired the long-standing "multi-week" blocker.** The iterated-Rolle crux
"differentiation preserves full real-rootedness counting multiplicity" was
recorded as "not in Mathlib" — but Mathlib's
`Polynomial.card_roots_le_derivative`
(`Analysis/Calculus/LocalExtr/Polynomial.lean`) supplies exactly the hard,
multiplicity-counted half. Four new theorems (20 → 24; docker-build clean, 7743
jobs; 0 sorries, 0 axioms):
- `derivative_roots_card_eq`: `card p.roots = natDegree p ⇒
  card (derivative p).roots = natDegree (derivative p)` — THE CRUX, all `n`. A
  4-line `omega` sandwich of `card_roots_le_derivative`, `card_roots'`,
  `natDegree_derivative_lt`.
- `splits_derivative` / `splits_iterate_derivative`: `Splits`-level and iterated
  forms (all `k` derivatives of `∏(X−xᵢ)` split).
- `exists_isRoot_derivative_Ioo`: the per-gap Rolle atom for the `Polynomial` API.
The real-rootedness half of the classical Newton proof is now general. Remaining:
pure coefficient bookkeeping (identify the `(n−k−1)`-th derivative as the quadratic
in `eₖ₋₁,eₖ,eₖ₊₁`, then feed the Part I discriminant atom).

## Iteration 5 (PART IV — n = 4 via SOS), PR #34576
Discharged **ALL THREE** Newton log-concavity steps at `n = 4` for arbitrary
SIGNED reals, via explicit SOS certificates (docker-build clean, 7743 jobs; 0
sorries, 0 axioms). This reaches the middle (`k = 2`) and top (`k = 3`) steps
that Part III's general `k = 1` QM–AM route does not cover, answering the
entry's "extend the SOS approach to n = 4" open question. Four new theorems
(16 → 20):
- `newton_four_first`:  `8 e₂ ≤ 3 e₁²`   — SOS `∑_{i<j}(xᵢ−xⱼ)²`.
- `newton_four_second`: `9 e₁ e₃ ≤ 4 e₂²` — SOS
  `3∑(xᵢxⱼ−xₖxₗ)² + ½∑((xᵢ−xⱼ)(xₖ−xₗ))²` (three opposite-pair splittings).
- `newton_four_third`:  `8 e₂ e₄ ≤ 3 e₃²` — SOS `∑_{i<j}(xᵢ−xⱼ)²(xₖxₗ)²`, the
  reciprocal-polynomial image of the `k = 1` certificate.
- `newton_four_normalized`: all three in normalized p-form.
Certificates derived + verified symbolically (sympy: exact identities, 0
numerical violations over 30k random signed samples). Method: the general Rolle
crux is NOT needed at fixed arity — each Newton inequality at `n = 4` is a PSD
quartic form whose SOS decomposition `nlinarith` verifies from the listed
squares. Next SOS increment would be `n = 5` (degrees rise; feasibility of
explicit certificates is the open question).

## Iteration 4 (PART III) Focus
Proved the genuinely **arbitrary-`n`** first Newton (= first Maclaurin)
inequality `p₁² ≥ p₀ p₂` for SIGNED reals — no enumeration, no appeal to the
still-open iterated-Rolle crux. Three new theorems in
`Proofs/AmgmInequalityOQ02OQ02OQ05.lean` (docker-build clean, 7743 jobs,
`LEAN_SKIP_CACHE=true`; 0 sorries, 0 axioms — foundational only):

- `sq_sum_eq`: the square-of-sum / elementary-symmetric identity
  `(∑_{i<n} xᵢ)² = ∑_{i<n} xᵢ² + 2 ∑_{j<n} ∑_{i<j} xᵢ xⱼ`, i.e. `e₁² = p₂ + 2 e₂`,
  proved by a clean induction on `n` (no triangular reindexing — the `succ` step
  is `sum_range_succ ×3`, `Finset.sum_mul`, then `linear_combination ih`).
- `sq_sum_le_nat_mul_sum_sq`: QM–AM `(∑ xᵢ)² ≤ n · ∑ xᵢ²`, specializing Mathlib's
  Chebyshev lemma `sq_sum_le_card_mul_sum_sq` to `range n` via `card_range`.
- `newton_first_general`: `2 n · e₂ ≤ (n − 1) · e₁²` for all `n` and all signed
  reals — the normalized `p₁² ≥ p₀ p₂` after clearing denominators. Proof:
  substitute `p₂ = e₁² − 2 e₂` into `e₁² ≤ n p₂`.

This closes the `k = 1` (first) Newton inequality for EVERY arity at once,
subsuming the earlier per-arity `n = 2` (`newton_two_vars`) and `n = 3`
(`newton_three_first`) first steps. The theorem needed only *real* inputs (QM–AM
is sign-agnostic), matching the real-rootedness route's signed-input advantage.

## Active Approach
Two complementary engines now coexist in the file:
1. real-rootedness / discriminant (Parts I–II): `n = 2`, `n = 3` per-arity, both
   log-concavity steps, via SOS discriminant certificates;
2. QM–AM / square-of-sum identity (Part III): the `k = 1` step for ALL `n`.

The GENERAL higher steps (`k ≥ 2`, arbitrary `n`) still need the packaged
iterated-Rolle lemma "differentiation preserves full real-rootedness counting
multiplicity".

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1 (QM–AM route)
- Approaches tried: real-rooted/discriminant atom + n=2 (I); n=3 both steps via
  SOS (II); general-n first step via QM–AM + square-of-sum identity (III)

## Blockers
- **RESOLVED (Part V)**: the "differentiation preserves full real-rootedness
  counting multiplicity" crux — previously flagged multi-week / "not in Mathlib"
  — is now `derivative_roots_card_eq`, assembled from Mathlib's
  `card_roots_le_derivative`. No longer a blocker.
- **REMAINING (algebra, not analysis)**: the coefficient reduction turning the
  crux into the general `k ≥ 2` Newton *inequality* — identify the `(n−k−1)`-th
  derivative of the reversed splitting polynomial as `a eₖ₋₁X² − b eₖX + c eₖ₊₁`
  (Vieta / `Polynomial.coeff` bookkeeping), then apply the Part I discriminant
  atom. This is `coeff`-level algebra, medium difficulty, no analysis blocker.

## Next Action
1. Prove the coefficient-extraction lemma: `coeff` of the `m`-fold derivative of
   `∏(X−xᵢ)` in terms of `esymm`, specialised to isolate three consecutive
   `eₖ₋₁,eₖ,eₖ₊₁` (use `Polynomial.coeff_iterate_derivative` /
   `Mathlib.RingTheory.Polynomial.Vieta`).
2. Feed the resulting real-rooted quadratic (real-rooted by
   `derivative_roots_card_eq`) into `discrim_nonneg_of_roots_nonempty` to close
   general `k ≥ 2` Newton.
