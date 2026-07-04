/-
  Newton's inequality via real-rootedness and the quadratic discriminant.

  Problem: amgm-inequality-oq-02-oq-02-oq-05
  Title:   Newton's Inequality via Real-Rooted Polynomials and Rolle's Theorem

  The parent entry `amgm-inequality-oq-02-oq-02` proves Newton's log-concavity
  step `p_k^2 ≥ p_{k-1} p_{k+1}` by a direct inductive/algebraic argument, and
  crucially assumes the inputs are NONNEGATIVE (`0 ≤ x i`).  The sibling
  `amgm-inequality-oq-02-oq-03-oq-03-oq-01` gives the first Newton inequality
  (`k = 1`) via a Cauchy–Schwarz / sum-of-squares "discriminant" engine.

  This file develops the *classical calculus route* the entry asks for, which is
  genuinely different from both and NOT previously present in the amgm family:
  Newton's inequality is the statement that a certain quadratic in three
  consecutive coefficients, obtained by repeatedly differentiating the
  real-rooted splitting polynomial `∏ (X - x_i)`, is itself real-rooted, hence
  has a NONNEGATIVE DISCRIMINANT.

  What is proved here (0 sorries, 0 axioms — foundational axioms only):

  * `discrim_nonneg_of_root`
        the reusable atom: a real quadratic `a x² + b x + c` that has a real
        root has `0 ≤ discrim a b c`.  This is "real-rooted quadratic ⇒
        log-concave coefficients", the exact per-derivative building block of
        the whole Rolle program.
  * `monic_quadratic_discrim_nonneg` / `discrim_nonneg_of_roots_nonempty`
        the same statement phrased through Mathlib's `Polynomial` API — a monic
        quadratic `X² + b X + c` with a real root (equivalently, whose `roots`
        multiset is nonempty) has nonnegative discriminant.
  * `realRooted_quadratic_coeff_ineq`  :  `4 c ≤ b²`.
  * `newton_two_vars`  :  `x y ≤ ((x + y)/2)²` for ALL real `x, y` — Newton's
        inequality `p_1² ≥ p_0 p_2` at `n = 2`, derived by taking the
        discriminant of the real-rooted polynomial `(X - x)(X - y)`.  Note there
        is NO sign hypothesis: the roots need only be real, which is exactly the
        advantage of the real-rootedness route the entry highlights (the parent's
        inductive proof needs `0 ≤ x i`).
  * `newton_three_first` / `newton_three_second`  :  both Newton log-concavity
        steps at `n = 3`, as nonnegative discriminants of the two derivative
        quadratics Rolle produces, via explicit SOS certificates.  Signed reals.
  * `sq_sum_eq`, `sq_sum_le_nat_mul_sum_sq`, `newton_first_general`  :  the
        genuinely *arbitrary-`n`* first Newton (= first Maclaurin) inequality
        `p_1² ≥ p_0 p_2`, i.e. `2 n · e₂ ≤ (n - 1) · e₁²`, for signed reals —
        no enumeration, no appeal to the still-open general Rolle crux (see
        Part III below).
  * `newton_four_first` / `newton_four_second` / `newton_four_third`  :  ALL
        THREE Newton log-concavity steps at `n = 4` for signed reals, via explicit
        SOS certificates (Part IV) — including the middle (`k = 2`) and top
        (`k = 3`) steps that lie beyond Part III's general `k = 1` reach.

  The general SECOND-and-higher steps (`p_k², k ≥ 2`, arbitrary `n`) need the
  crux lemma "differentiation preserves full real-rootedness (counting
  multiplicity)" — Rolle's theorem iterated on `∏ (X - x_i)` — which is the
  multi-week formalization risk flagged in `problem.md`.  It is honestly retained
  as open (documented in knowledge.md) and is deliberately NOT stubbed out.
-/
import Mathlib

namespace NewtonRealRooted

open Polynomial

/-!  ## The discriminant atom: a real root forces a nonnegative discriminant  -/

/-- **Real-rooted quadratic ⇒ nonnegative discriminant.**
If the quadratic `a x² + b x + c` has a real root `x`, then its discriminant
`b² - 4ac` is nonnegative.  This is the single per-derivative step of the
classical Newton/Rolle argument: after differentiating a real-rooted polynomial
down to degree two, real-rootedness of the reduced quadratic *is* Newton's
inequality for the three surviving coefficients. -/
theorem discrim_nonneg_of_root (a b c x : ℝ) (h : a * (x * x) + b * x + c = 0) :
    0 ≤ discrim a b c := by
  rw [discrim_eq_sq_of_quadratic_eq_zero h]
  exact sq_nonneg _

/-!  ## Phrased through the `Polynomial` API (genuine real-rootedness)  -/

/-- A monic real quadratic `X² + b X + c` with a real root has nonnegative
discriminant `discrim 1 b c`.  Same content as `discrim_nonneg_of_root`, stated
via `Polynomial.IsRoot` so it plugs directly into the splitting-polynomial
picture. -/
theorem monic_quadratic_discrim_nonneg (b c r : ℝ)
    (hr : (X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r) :
    0 ≤ discrim 1 b c := by
  have hroot : r ^ 2 + b * r + c = 0 := by
    simpa [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hr
  exact discrim_nonneg_of_root 1 b c r (by linear_combination hroot)

/-- If the monic real quadratic `X² + b X + c` splits over `ℝ` far enough to have
a nonempty `roots` multiset (i.e. it is real-rooted), its discriminant is
nonnegative.  This is the `Polynomial.roots`-level phrasing of real-rootedness. -/
theorem discrim_nonneg_of_roots_nonempty (b c : ℝ)
    (h : (X ^ 2 + C b * X + C c : ℝ[X]).roots ≠ 0) :
    0 ≤ discrim 1 b c := by
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero h
  exact monic_quadratic_discrim_nonneg b c r (mem_roots'.1 hr).2

/-- The discriminant inequality rewritten as the coefficient inequality
`4c ≤ b²` (log-concavity of the coefficient triple `(1, b, c)`). -/
theorem realRooted_quadratic_coeff_ineq (b c r : ℝ)
    (hr : (X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r) :
    4 * c ≤ b ^ 2 := by
  have h := monic_quadratic_discrim_nonneg b c r hr
  rw [discrim] at h
  linarith

/-!  ## The splitting polynomial for two roots, and Newton at `n = 2`  -/

/-- Vieta for two roots: `(X - x)(X - y) = X² - (x+y) X + x y`. -/
theorem prod_two_linear_eq (x y : ℝ) :
    ((X - C x) * (X - C y) : ℝ[X]) = X ^ 2 + C (-(x + y)) * X + C (x * y) := by
  rw [C_neg, C_add, C_mul]
  ring

/-- Each root of `(X - x)(X - y)` is, well, a root: `x` is a real root. -/
theorem root_of_prod_two_linear (x y : ℝ) :
    ((X - C x) * (X - C y) : ℝ[X]).IsRoot x := by
  simp [IsRoot, eval_mul, eval_sub, eval_X, eval_C]

/-- **Newton's inequality at `n = 2`, via real-rootedness.**
For every pair of real numbers `x, y` (no sign restriction),
`x y ≤ ((x + y)/2)²`, i.e. `p_1² ≥ p_0 p_2` for the normalized elementary
symmetric means of `x, y`.  Proof: the polynomial `(X - x)(X - y)` is
real-rooted, so the discriminant of `X² - (x+y) X + x y` is `≥ 0`, which is
exactly `(x + y)² ≥ 4 x y`. -/
theorem newton_two_vars (x y : ℝ) : x * y ≤ ((x + y) / 2) ^ 2 := by
  have hroot : (X ^ 2 + C (-(x + y)) * X + C (x * y) : ℝ[X]).IsRoot x := by
    rw [← prod_two_linear_eq]; exact root_of_prod_two_linear x y
  have h := realRooted_quadratic_coeff_ineq (-(x + y)) (x * y) x hroot
  nlinarith [h]

/-- The `n = 2` Newton inequality in normalized (`p`) form, emphasizing the
`p_1² ≥ p_0 · p_2` shape with `p_0 = 1`, `p_1 = e_1/2 = (x+y)/2`, `p_2 = e_2 = xy`.
Holds for signed inputs. -/
theorem newton_two_vars_normalized (x y : ℝ) :
    (1 : ℝ) * (x * y) ≤ ((x + y) / 2) ^ 2 := by
  simpa using newton_two_vars x y

/-!  ## Newton at `n = 3`, via the real-rooted derivative quadratics

For three real roots `x, y, z` the splitting cubic is
`(X - x)(X - y)(X - z) = X³ - e₁ X² + e₂ X - e₃`, with
`e₁ = x+y+z`, `e₂ = xy+yz+zx`, `e₃ = xyz`.  The two Newton inequalities are the
nonnegative discriminants of the two degree-two polynomials Rolle produces:

* differentiate once:  `P' = 3X² - 2e₁X + e₂`  (real-rooted ⇒ `4e₁² - 12e₂ ≥ 0`),
  giving the first step `e₁² ≥ 3e₂`;
* pass to the reciprocal cubic and differentiate:
  `-3e₃X² + 2e₂X - e₁`  (real-rooted ⇒ `4e₂² - 12e₁e₃ ≥ 0`), giving the second
  step `e₂² ≥ 3e₁e₃`.

Each derivative quadratic's discriminant is established here *directly* as a sum
of squares — which **is** the real-rootedness of that quadratic — so the `n = 3`
case needs neither the general Rolle-iteration lemma (the multi-week crux flagged
in `problem.md`) nor any sign hypothesis.  The Rolle picture is the motivation;
the SOS certificate is the proof. -/

/-- **Newton's first inequality at `n = 3`** (`p₁² ≥ p₀ p₂`), for arbitrary real
`x, y, z`: in elementary-symmetric form `e₁² ≥ 3 e₂`, i.e.
`3(xy+yz+zx) ≤ (x+y+z)²`.  This is the nonnegativity of the discriminant of the
once-differentiated splitting cubic `P' = 3X² - 2e₁X + e₂`; the SOS certificate
is `½[(x−y)² + (y−z)² + (z−x)²] ≥ 0`.  No sign hypothesis. -/
theorem newton_three_first (x y z : ℝ) :
    3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-- The once-differentiated splitting cubic `P' = 3X² - 2e₁X + e₂` has
nonnegative discriminant — the discriminant phrasing of `newton_three_first`, and
the `n = 3` instance of "a derivative of a real-rooted polynomial is real-rooted
(discriminant `≥ 0`)". -/
theorem discrim_deriv_cubic_first (x y z : ℝ) :
    0 ≤ discrim 3 (-2 * (x + y + z)) (x * y + y * z + z * x) := by
  rw [discrim]; nlinarith [newton_three_first x y z]

/-- **Newton's second inequality at `n = 3`** (`p₂² ≥ p₁ p₃`), for arbitrary real
`x, y, z`: in elementary-symmetric form `e₂² ≥ 3 e₁ e₃`, i.e.
`3(x+y+z)·xyz ≤ (xy+yz+zx)²`.  This is the nonnegativity of the discriminant of
the differentiated *reciprocal* cubic `-3e₃X² + 2e₂X - e₁`; the SOS certificate is
`½[(xy−yz)² + (yz−zx)² + (zx−xy)²] ≥ 0`.  Holds for all signed reals. -/
theorem newton_three_second (x y z : ℝ) :
    3 * (x + y + z) * (x * y * z) ≤ (x * y + y * z + z * x) ^ 2 := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x),
    sq_nonneg (z * x - x * y)]

/-- The differentiated reciprocal cubic `-3e₃X² + 2e₂X - e₁` has nonnegative
discriminant — the discriminant phrasing of `newton_three_second`. -/
theorem discrim_recip_deriv_cubic_second (x y z : ℝ) :
    0 ≤ discrim (-3 * (x * y * z)) (2 * (x * y + y * z + z * x)) (-(x + y + z)) := by
  rw [discrim]; nlinarith [newton_three_second x y z]

/-- **Newton at `n = 3` in normalized (`p`) form.**  With `p₀ = 1`,
`p₁ = e₁/3 = (x+y+z)/3`, `p₂ = e₂/3 = (xy+yz+zx)/3`, `p₃ = e₃ = xyz`, both
log-concavity steps `p₁² ≥ p₀·p₂` and `p₂² ≥ p₁·p₃` hold for all signed reals. -/
theorem newton_three_normalized (x y z : ℝ) :
    (1 : ℝ) * ((x * y + y * z + z * x) / 3) ≤ ((x + y + z) / 3) ^ 2 ∧
      ((x + y + z) / 3) * (x * y * z) ≤ ((x * y + y * z + z * x) / 3) ^ 2 := by
  refine ⟨?_, ?_⟩
  · nlinarith [newton_three_first x y z]
  · nlinarith [newton_three_second x y z]

/-!  ## Part III — the general-`n` first Newton inequality (all `n`, signed reals)

The `n = 2` and `n = 3` results above are per-arity SOS certificates.  This part
gives the genuinely *arbitrary-`n`* first Newton (equivalently first Maclaurin)
inequality `p₁² ≥ p₀ p₂`, for signed reals, with NO enumeration and NO appeal to
the (still-open) general iterated-Rolle crux.

Write `e₁ = ∑ xᵢ`, `p₂ = ∑ xᵢ²` (the second power sum) and
`e₂ = ∑_{i < j} xᵢ xⱼ` (the second elementary symmetric polynomial).  Newton's
first inequality `p₁² ≥ p₀ p₂` unwinds, with `p₁ = e₁/n`, `p₂ = e₂/binom n 2`,
`p₀ = 1`, to the polynomial inequality

    `2 n · e₂ ≤ (n - 1) · e₁²`.

Two ingredients suffice:
* the elementary identity `e₁² = p₂ + 2 e₂`  (`sq_sum_eq`, a clean induction), and
* the QM–AM / Cauchy–Schwarz bound `e₁² ≤ n · p₂`  (`sq_sum_le_card_mul_sum_sq`).

Substituting `p₂ = e₁² - 2 e₂` into `e₁² ≤ n · p₂` gives exactly
`2 n · e₂ ≤ (n - 1) · e₁²`.  Because QM–AM needs only *real* inputs, the result
holds for SIGNED reals — the same generalisation over the parent's `0 ≤ xᵢ`
induction that the `n = 2` / `n = 3` discriminant route achieves, but now for
every arity simultaneously.  The higher log-concavity steps (`p_k`, `k ≥ 2`) at
arbitrary `n` remain the open Rolle-crux part. -/

open Finset in
/-- **Square-of-sum / elementary-symmetric identity.**  For any real sequence,
`(∑_{i<n} xᵢ)² = ∑_{i<n} xᵢ² + 2 · ∑_{j<n} ∑_{i<j} xᵢ xⱼ`; that is
`e₁² = p₂ + 2 e₂`, the expansion of the square of a sum into its diagonal (second
power sum) and off-diagonal (second elementary symmetric) parts.  Proved by a
clean induction on `n`, sidestepping any triangular reindexing. -/
theorem sq_sum_eq (n : ℕ) (x : ℕ → ℝ) :
    (∑ i ∈ range n, x i) ^ 2
      = (∑ i ∈ range n, x i ^ 2)
        + 2 * ∑ j ∈ range n, ∑ i ∈ range j, x i * x j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, sum_range_succ]
    have hmul : ∑ i ∈ range n, x i * x n = (∑ i ∈ range n, x i) * x n := by
      rw [sum_mul]
    rw [hmul]
    linear_combination ih

open Finset in
/-- **QM–AM for the power sum.**  `(∑_{i<n} xᵢ)² ≤ n · ∑_{i<n} xᵢ²`.  This is the
`f = g` case of Chebyshev's sum inequality (`sq_sum_le_card_mul_sum_sq`) applied
on `range n`, using `#(range n) = n`. -/
theorem sq_sum_le_nat_mul_sum_sq (n : ℕ) (x : ℕ → ℝ) :
    (∑ i ∈ range n, x i) ^ 2 ≤ (n : ℝ) * ∑ i ∈ range n, x i ^ 2 := by
  have h : (∑ i ∈ range n, x i) ^ 2 ≤ ((range n).card : ℝ) * ∑ i ∈ range n, x i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simpa [card_range] using h

open Finset in
/-- **Newton's first inequality for arbitrary `n`, signed reals.**  With
`e₁ = ∑_{i<n} xᵢ` and `e₂ = ∑_{j<n} ∑_{i<j} xᵢ xⱼ` the second elementary
symmetric polynomial,
    `2 n · e₂ ≤ (n - 1) · e₁²`.
This is the normalized first Newton/Maclaurin inequality `p₁² ≥ p₀ p₂`
(`p₁ = e₁/n`, `p₂ = e₂ / binom n 2`, `p₀ = 1`) after clearing denominators.  No
sign hypothesis: it holds for all real `xᵢ`, generalising the `0 ≤ xᵢ` inductive
parent to every arity at once.  Proof: substitute the identity `e₁² = p₂ + 2 e₂`
(`sq_sum_eq`) into the QM–AM bound `e₁² ≤ n · p₂` (`sq_sum_le_nat_mul_sum_sq`). -/
theorem newton_first_general (n : ℕ) (x : ℕ → ℝ) :
    2 * (n : ℝ) * (∑ j ∈ range n, ∑ i ∈ range j, x i * x j)
      ≤ ((n : ℝ) - 1) * (∑ i ∈ range n, x i) ^ 2 := by
  have hid := sq_sum_eq n x
  have hqm := sq_sum_le_nat_mul_sum_sq n x
  -- scale the identity by `n`, so everything is linear in the three sums
  have hn : (n : ℝ) * (∑ i ∈ range n, x i) ^ 2
      = (n : ℝ) * (∑ i ∈ range n, x i ^ 2)
        + 2 * (n : ℝ) * (∑ j ∈ range n, ∑ i ∈ range j, x i * x j) := by
    rw [hid]; ring
  nlinarith [hqm, hn]

/-!  ## Part IV — Newton at `n = 4` via explicit SOS certificates

Part III closed the FIRST Newton step (`k = 1`) for every arity, but the higher
steps `k ≥ 2` at general `n` remain tied to the open iterated-Rolle crux.  Here we
push the concrete SOS-certificate method of Part II one arity further and discharge
ALL THREE Newton inequalities at `n = 4`, for arbitrary signed reals — including
the middle step `k = 2` and the top step `k = 3`, which lie beyond Part III's
`k = 1` reach.  This answers the "extend the SOS approach to `n = 4`" question and
supplies the first fully-signed `n = 4` log-concavity chain in the amgm family.

For four real roots `a, b, c, d` the splitting quartic is
`(X-a)(X-b)(X-c)(X-d) = X⁴ - e₁X³ + e₂X² - e₃X + e₄`, with
`e₁ = a+b+c+d`, `e₂ = ab+ac+ad+bc+bd+cd`, `e₃ = abc+abd+acd+bcd`, `e₄ = abcd`.
The three Newton inequalities `p_k² ≥ p_{k-1}p_{k+1}` (`k = 1,2,3`, with
`p₀=1, p₁=e₁/4, p₂=e₂/6, p₃=e₃/4, p₄=e₄`) become, after clearing denominators:

* `k = 1`:  `8 e₂ ≤ 3 e₁²`   — SOS `∑_{i<j}(xᵢ-xⱼ)²` (the `n = 4` instance of
  `newton_first_general`);
* `k = 2`:  `9 e₁ e₃ ≤ 4 e₂²` — SOS
  `3∑(xᵢxⱼ-xₖxₗ)² + ½∑((xᵢ-xⱼ)(xₖ-xₗ))²` over the three ways to split
  `{a,b,c,d}` into two opposite pairs;
* `k = 3`:  `8 e₂ e₄ ≤ 3 e₃²` — SOS `∑_{i<j}(xᵢ-xⱼ)²(xₖxₗ)²`, the image of the
  `k = 1` certificate under the reciprocal substitution `xᵢ ↦ 1/xᵢ`.

Each certificate is exact (verified symbolically); `nlinarith` closes each from the
listed squares.  No sign hypothesis anywhere. -/

/-- **Newton's first inequality at `n = 4`** (`p₁² ≥ p₀ p₂`), for arbitrary signed
reals: `8 e₂ ≤ 3 e₁²`, i.e. `8(ab+ac+ad+bc+bd+cd) ≤ 3(a+b+c+d)²`.  SOS certificate
`∑_{i<j}(xᵢ-xⱼ)²`.  (Also the `n = 4` instance of `newton_first_general`.) -/
theorem newton_four_first (a b c d : ℝ) :
    8 * (a * b + a * c + a * d + b * c + b * d + c * d) ≤ 3 * (a + b + c + d) ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- **Newton's second (middle) inequality at `n = 4`** (`p₂² ≥ p₁ p₃`), for
arbitrary signed reals: `9 e₁ e₃ ≤ 4 e₂²`, i.e.
`9(a+b+c+d)(abc+abd+acd+bcd) ≤ 4(ab+ac+ad+bc+bd+cd)²`.  SOS certificate
`3[(ab-cd)²+(ac-bd)²+(ad-bc)²] + ½[((a-b)(c-d))²+((a-c)(b-d))²+((a-d)(b-c))²]`.
This is the `k = 2` step that Part III's general `k = 1` route does not reach. -/
theorem newton_four_second (a b c d : ℝ) :
    9 * (a + b + c + d) * (a * b * c + a * b * d + a * c * d + b * c * d)
      ≤ 4 * (a * b + a * c + a * d + b * c + b * d + c * d) ^ 2 := by
  nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d),
    sq_nonneg (a * d - b * c), sq_nonneg ((a - b) * (c - d)),
    sq_nonneg ((a - c) * (b - d)), sq_nonneg ((a - d) * (b - c))]

/-- **Newton's third inequality at `n = 4`** (`p₃² ≥ p₂ p₄`), for arbitrary signed
reals: `8 e₂ e₄ ≤ 3 e₃²`, i.e.
`8(ab+ac+ad+bc+bd+cd)(abcd) ≤ 3(abc+abd+acd+bcd)²`.  SOS certificate
`∑_{i<j}(xᵢ-xⱼ)²(xₖxₗ)²`, the image of the `k = 1` certificate under the reciprocal
substitution `xᵢ ↦ 1/xᵢ`. -/
theorem newton_four_third (a b c d : ℝ) :
    8 * (a * b + a * c + a * d + b * c + b * d + c * d) * (a * b * c * d)
      ≤ 3 * (a * b * c + a * b * d + a * c * d + b * c * d) ^ 2 := by
  nlinarith [sq_nonneg ((a - b) * (c * d)), sq_nonneg ((a - c) * (b * d)),
    sq_nonneg ((a - d) * (b * c)), sq_nonneg ((b - c) * (a * d)),
    sq_nonneg ((b - d) * (a * c)), sq_nonneg ((c - d) * (a * b))]

/-- **Newton at `n = 4` in normalized (`p`) form.**  All three log-concavity steps
`p_{k-1} p_{k+1} ≤ p_k²` for `k = 1, 2, 3`, with `p₀=1, p₁=e₁/4, p₂=e₂/6,
p₃=e₃/4, p₄=e₄`, hold for arbitrary signed reals `a, b, c, d`. -/
theorem newton_four_normalized (a b c d : ℝ) :
    (1 : ℝ) * ((a * b + a * c + a * d + b * c + b * d + c * d) / 6)
        ≤ ((a + b + c + d) / 4) ^ 2 ∧
      ((a + b + c + d) / 4) * ((a * b * c + a * b * d + a * c * d + b * c * d) / 4)
        ≤ ((a * b + a * c + a * d + b * c + b * d + c * d) / 6) ^ 2 ∧
      ((a * b + a * c + a * d + b * c + b * d + c * d) / 6) * (a * b * c * d)
        ≤ ((a * b * c + a * b * d + a * c * d + b * c * d) / 4) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [newton_four_first a b c d]
  · nlinarith [newton_four_second a b c d]
  · nlinarith [newton_four_third a b c d]

/-!  ## Part V — the general Rolle crux: differentiation preserves real-rootedness

Parts I–IV give per-arity certificates (`n = 2, 3, 4`) and the general `k = 1`
step.  The recurring *blocker* documented across every prior iteration was the
GENERAL, arbitrary-`n` engine: the classical statement

  "each derivative of a fully-real-rooted polynomial is again fully real-rooted
   (counting multiplicity)"

— iterated Rolle on `∏(X - xᵢ)` — which `problem.md` estimated at multi-week
formalization difficulty and knowledge.md recorded as "not in Mathlib".

It turns out Mathlib DOES supply the hard half:
`Polynomial.card_roots_le_derivative` (in `Mathlib/Analysis/Calculus/LocalExtr/
Polynomial.lean`), the multiplicity-counted bound
`card p.roots ≤ card (derivative p).roots + 1`.  Combined with the two elementary
degree facts `card q.roots ≤ q.natDegree` (`card_roots'`) and
`(derivative p).natDegree < p.natDegree` (`natDegree_derivative_lt`), a full
real-rooted `p` (`card p.roots = p.natDegree`) is squeezed to EQUALITY for its
derivative:

  `natDegree p - 1 ≤ card (derivative p).roots ≤ (derivative p).natDegree
                   ≤ natDegree p - 1`,

so `card (derivative p).roots = (derivative p).natDegree` — the derivative splits.
This packages the flagged crux as a short, general, reusable lemma (all `n`, all
`k`), and it is the honest general engine the per-arity SOS certificates were
standing in for.

What this Part does NOT yet do: turn the crux into the general Newton *coefficient*
inequality `pₖ² ≥ pₖ₋₁ pₖ₊₁` for `k ≥ 2`.  That final reduction still needs the
coefficient bookkeeping "the appropriate iterated derivative of the (reversed)
splitting polynomial is the quadratic `a eₖ₋₁ X² - b eₖ X + c eₖ₊₁`", whose
real-rootedness (now supplied by `derivative_roots_card_eq` / `splits_derivative`)
gives `discrim ≥ 0` via the Part I atom `discrim_nonneg_of_roots_nonempty`.  That
Vieta-coefficient step is the remaining honest gap; the real-rootedness half of
the classical proof is closed here. -/

open Set in
/-- **Rolle's theorem for polynomials.**  Between two roots `a < b` of a real
polynomial `p` lies a root of its derivative.  This is the single per-gap step of
the classical Newton/Rolle argument, packaged directly for the `Polynomial` API
(Mathlib has Rolle `exists_hasDerivAt_eq_zero` and `Polynomial.hasDerivAt`, but
not this bridge as a named lemma). -/
theorem exists_isRoot_derivative_Ioo {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c ∈ Ioo a b, (derivative p).IsRoot c := by
  have ha' : p.eval a = 0 := ha
  have hb' : p.eval b = 0 := hb
  have hfI : p.eval a = p.eval b := by rw [ha', hb']
  obtain ⟨c, hc, hc0⟩ :=
    exists_hasDerivAt_eq_zero hab p.continuousOn hfI (fun x _ => p.hasDerivAt x)
  exact ⟨c, hc, hc0⟩

/-- **Differentiation preserves full real-rootedness (counting multiplicity).**
If a real polynomial `p` has as many roots with multiplicity as its degree —
`card p.roots = p.natDegree`, i.e. `p` splits over `ℝ` — then its derivative does
too: `card (derivative p).roots = (derivative p).natDegree`.

This is the long-flagged general crux of the real-rootedness route to Newton's
inequalities.  Proof: the Mathlib bound `card_roots_le_derivative`
(`card p.roots ≤ card (derivative p).roots + 1`) together with
`card_roots' : card q.roots ≤ q.natDegree` and
`natDegree_derivative_lt : (derivative p).natDegree < p.natDegree`
sandwich `card (derivative p).roots` between `natDegree p - 1` and itself; `omega`
closes the arithmetic.  The constant case `natDegree p = 0` is separate
(`derivative (C a) = 0`). -/
theorem derivative_roots_card_eq {p : ℝ[X]}
    (hp : Multiset.card p.roots = p.natDegree) :
    Multiset.card (derivative p).roots = (derivative p).natDegree := by
  rcases eq_or_ne p.natDegree 0 with h0 | h0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0
    simp [derivative_C]
  · have h1 : Multiset.card (derivative p).roots ≤ (derivative p).natDegree :=
      card_roots' _
    have h2 : Multiset.card p.roots ≤ Multiset.card (derivative p).roots + 1 :=
      card_roots_le_derivative p
    have h3 : (derivative p).natDegree < p.natDegree := natDegree_derivative_lt h0
    omega

/-- **`Splits`-level phrasing of the crux.**  If `p : ℝ[X]` splits over `ℝ`
(factors into real linear factors), so does its derivative. -/
theorem splits_derivative {p : ℝ[X]} (hp : Splits p) : Splits (derivative p) := by
  rw [splits_iff_card_roots] at hp ⊢
  exact derivative_roots_card_eq hp

/-- **Every derivative of a split real polynomial splits.**  Iterating
`splits_derivative`: the full conclusion of the classical Newton/Rolle program —
all `k` successive derivatives of a real-rooted `∏(X - xᵢ)` are again real-rooted.
Combined with the Part I discriminant atom this reduces Newton's inequalities to
the (still open) coefficient identification of the `(n-k-1)`-th derivative as the
quadratic in `eₖ₋₁, eₖ, eₖ₊₁`. -/
theorem splits_iterate_derivative {p : ℝ[X]} (hp : Splits p) (k : ℕ) :
    Splits (derivative^[k] p) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply]
      exact splits_derivative ih

/-!  ## Closing the loop: the crux *produces* a discriminant inequality

Parts I–V above proved the two halves of the classical route in isolation: the
Part I atom `discrim_nonneg_of_root` ("a real-rooted quadratic has nonnegative
discriminant"), and the Part V crux `splits_iterate_derivative` ("every derivative
of a split real polynomial is again split").  They were never *joined*: nothing
yet turned "the reduced polynomial is real-rooted" into "its discriminant is `≥ 0`"
at the `Polynomial`/`coeff` level for a genuinely arbitrary split polynomial.

The following lemma is exactly that join, in coordinate-free `coeff` form: a real
polynomial that `Splits` and has degree exactly two has a nonnegative
discriminant in its three coefficients.  Because `splits_iterate_derivative`
shows the `(n-2)`-nd derivative of a split degree-`n` polynomial splits and has
degree two, this is the general per-derivative Newton step, stated once for all
`n` with no sign hypothesis — the honest end-to-end use of the Part V engine that
the earlier parts documented as still missing. -/

open Finset in
/-- **A split real quadratic has nonnegative discriminant** (`coeff` form).
If `p : ℝ[X]` splits over `ℝ` and `p.natDegree = 2`, then
`0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0)`.

This is the general per-derivative step of the Rolle/discriminant program stated
directly on `Polynomial` coefficients: `splits_iterate_derivative` reduces a split
degree-`n` polynomial to a split *quadratic* (its `(n-2)`-nd derivative), and this
lemma converts that quadratic's real-rootedness into Newton's discriminant
inequality on the surviving three coefficients.  Proof: a split polynomial of
degree two has `card roots = 2 > 0`, so it has a real root `r`; expanding
`p.eval r = 0` through `eval_eq_sum_range` (a length-three sum since
`natDegree = 2`) yields `coeff 2 · r² + coeff 1 · r + coeff 0 = 0`, and the Part I
atom `discrim_nonneg_of_root` finishes. -/
theorem discrim_coeff_nonneg_of_splits_deg_two {p : ℝ[X]}
    (hp : Splits p) (hdeg : p.natDegree = 2) :
    0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0) := by
  -- a split degree-2 polynomial has two roots (with multiplicity), so `roots ≠ 0`
  have hcard : Multiset.card p.roots = 2 := by
    rw [splits_iff_card_roots] at hp; rw [hp, hdeg]
  have hne : p.roots ≠ 0 := by
    rw [← Multiset.card_pos, hcard]; norm_num
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne
  have hroot : p.eval r = 0 := isRoot_of_mem_roots hr
  -- expand the evaluation as a length-three coefficient sum
  have hexp : p.eval r
      = ∑ i ∈ range (p.natDegree + 1), p.coeff i * r ^ i := eval_eq_sum_range r
  rw [hdeg] at hexp
  rw [sum_range_succ, sum_range_succ, sum_range_one] at hexp
  have hquad : p.coeff 2 * (r * r) + p.coeff 1 * r + p.coeff 0 = 0 := by
    have key : p.coeff 0 * r ^ 0 + p.coeff 1 * r ^ 1 + p.coeff 2 * r ^ 2 = 0 := by
      rw [← hexp]; exact hroot
    linear_combination key
  exact discrim_nonneg_of_root (p.coeff 2) (p.coeff 1) (p.coeff 0) r hquad

/-!  ## Part VII — the general-`n` TOP Newton step via the actual Rolle route

Parts V–VI closed the two engine halves at the `Polynomial` level but only ever
applied `discrim_coeff_nonneg_of_splits_deg_two` to an *abstract* degree-two
polynomial.  The genuinely missing bridge (flagged as the remaining "coefficient
bookkeeping" in `state.md`/`knowledge.md`) is to run the whole program on ONE
split polynomial of arbitrary degree: differentiate a split degree-`(m+2)`
polynomial `m` times down to a split *quadratic*, then read the discriminant
inequality back on `p`'s own top three coefficients via
`Polynomial.coeff_iterate_derivative`.  That is exactly what the two theorems
below do — for the first time joining Part V's `splits_iterate_derivative`, Part
VI's `discrim_coeff_nonneg_of_splits_deg_two`, and Mathlib's coefficient formula
for iterated derivatives into a single arbitrary-`n` Newton-type inequality on
`p.coeff (m+2), p.coeff (m+1), p.coeff m`, with NO sign hypothesis (only that `p`
splits, i.e. is real-rooted).

Specialising to the monic splitting polynomial `p = ∏ (X - xᵢ)` — whose top
coefficients are, by Vieta, `±` the elementary symmetric functions
`e₀ = 1, e₁, e₂` reading down from the top — turns this into the classical TOP
Newton log-concavity step `pₙ₋₁² ≥ pₙ₋₂ pₙ` for every arity `n = m + 2` at once,
by the honest calculus proof the entry asks for (the Vieta substitution is the
one remaining, purely algebraic, increment). -/

/-- **The `m`-th derivative of a split degree-`(m+2)` polynomial is a split
quadratic whose discriminant is nonnegative** — read directly on `p`'s top three
coefficients.

If `p : ℝ[X]` splits (is real-rooted over `ℝ`) and has `natDegree = m + 2`, then
its `m`-fold derivative is a genuine quadratic (degree exactly two, since its
leading coefficient `(m+2).descFactorial m · leadingCoeff p ≠ 0`) that again
splits (Part V), so Part VI gives `0 ≤ discrim` of its three coefficients.  By
`Polynomial.coeff_iterate_derivative` those coefficients are the
`descFactorial`-weighted top three coefficients of `p`, giving Newton's
discriminant inequality for consecutive coefficients of an arbitrary real-rooted
polynomial. -/
theorem discrim_iterate_derivative_top (m : ℕ) {p : ℝ[X]}
    (hp : Splits p) (hdeg : p.natDegree = m + 2) :
    0 ≤ discrim
        ((2 + m).descFactorial m • p.coeff (2 + m))
        ((1 + m).descFactorial m • p.coeff (1 + m))
        ((0 + m).descFactorial m • p.coeff (0 + m)) := by
  -- `p` has positive degree, so it is nonzero
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  -- the leading coefficient of the `m`-th derivative (its `coeff 2`) is nonzero
  have hc2ne : (derivative^[m] p).coeff 2 ≠ 0 := by
    simp only [coeff_iterate_derivative, nsmul_eq_mul]
    apply mul_ne_zero
    · exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
    · have h2m : 2 + m = p.natDegree := by rw [hdeg]; omega
      rw [h2m]
      exact leadingCoeff_ne_zero.mpr hpne
  -- hence the `m`-th derivative is a genuine quadratic (degree exactly two)
  have hdeg2 : (derivative^[m] p).natDegree = 2 := by
    have hle := natDegree_iterate_derivative p m
    rw [hdeg] at hle
    have hge : 2 ≤ (derivative^[m] p).natDegree := le_natDegree_of_ne_zero hc2ne
    omega
  -- it still splits (Part V), so its discriminant is nonnegative (Part VI)
  have hq := discrim_coeff_nonneg_of_splits_deg_two (splits_iterate_derivative hp m) hdeg2
  -- read the three coefficients back on `p` via Mathlib's iterated-derivative formula
  rwa [coeff_iterate_derivative, coeff_iterate_derivative, coeff_iterate_derivative] at hq

/-- **General-`n` top Newton inequality on the coefficients of a real-rooted
polynomial.** For any `p : ℝ[X]` that splits with `natDegree = m + 2`, the three
top coefficients satisfy
`4 · (m+2)!/2! · m! · p.coeff (m+2) · p.coeff m ≤ ((m+1)!)² · p.coeff (m+1)²`
(the `descFactorial` weights are `(2+m).descFactorial m`, `m.descFactorial m`,
`(1+m).descFactorial m`).  This is the discriminant inequality
`discrim_iterate_derivative_top` written as the recognizable Newton/log-concavity
inequality `b² ≥ 4ac` on consecutive coefficients — the honest calculus proof of
Newton's TOP step, valid for every arity and all signed inputs. -/
theorem newton_top_coeff_ineq (m : ℕ) {p : ℝ[X]}
    (hp : Splits p) (hdeg : p.natDegree = m + 2) :
    4 * ((2 + m).descFactorial m : ℝ) * ((0 + m).descFactorial m : ℝ)
        * p.coeff (2 + m) * p.coeff (0 + m)
      ≤ ((1 + m).descFactorial m : ℝ) ^ 2 * p.coeff (1 + m) ^ 2 := by
  have h := discrim_iterate_derivative_top m hp hdeg
  rw [discrim] at h
  simp only [nsmul_eq_mul] at h
  nlinarith [h]

/-!  ## Part VIII — the general-`n` BOTTOM Newton step via a single reversal

Part VII closed the general TOP Newton step (the discriminant of `p`'s three
*top* coefficients), but when specialised to the monic splitting polynomial
`∏(X - xᵢ)` — whose top three coefficients are `1, -e₁, e₂` — that top step only
reproduces the FIRST Newton inequality (`e₁² ≥ … e₂`), already general in Part III.
Genuinely new arbitrary-`n` content lives in the *other* steps, and the classical
route reaches them by REVERSING the polynomial: `reverse p` reads `p`'s
coefficients bottom-up, so applying the Part VII top-step engine to `reverse p`
yields Newton's discriminant inequality on `p`'s three *bottom* coefficients
`coeff 0, coeff 1, coeff 2`.  For `p = ∏(X - xᵢ)` (all roots nonzero, so
`coeff 0 = ±eₙ ≠ 0`) this is the classical BOTTOM step `eₙ₋₁² ≥ eₙ₋₂ eₙ` — NOT
reachable from Parts III or VII.

The one piece of infrastructure this needs, and which Mathlib does not package, is
that reversal preserves splitting: **a real-rooted polynomial has a real-rooted
reversal**.  We build it here from `splits_iff_exists_multiset` (`p` factors as
`C (leadingCoeff p) · ∏ (X - rᵢ)`), `reverse_mul_of_domain` (reverse distributes
over products in a domain), and the fact that each `reverse (X - C rᵢ)` has degree
`≤ 1` with invertible leading coefficient (`= trailingCoeff (X - C rᵢ) ≠ 0`), hence
splits.  No sign hypothesis on the roots for splitting itself; the reversal reading
`p`'s bottom coefficients needs only `p.coeff 0 ≠ 0` (nonzero constant term, i.e.
`natTrailingDegree p = 0`). -/

/-- **The reversal of a real linear factor splits.**  `reverse (X - C a)` has
degree `≤ 1` and leading coefficient `trailingCoeff (X - C a) ≠ 0` (invertible in
the field `ℝ`), so it splits.  This is the per-factor atom for `splits_reverse`. -/
theorem splits_reverse_linear (a : ℝ) : Splits (reverse (X - C a : ℝ[X])) := by
  apply splits_of_natDegree_le_one_of_invertible
  · exact (reverse_natDegree_le _).trans (by rw [natDegree_X_sub_C])
  · rw [reverse_leadingCoeff]
    exact invertibleOfNonzero (mt trailingCoeff_eq_zero.mp (X_sub_C_ne_zero a))

/-- **The reversal of a product of real linear factors splits.**  `reverse`
distributes over the multiset product (domain), and each factor's reversal splits
(`splits_reverse_linear`), so the whole reversal splits.  Multiset induction. -/
theorem splits_reverse_prod (s : Multiset ℝ) :
    Splits (reverse ((s.map (fun r => X - C r)).prod)) := by
  induction s using Multiset.induction with
  | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero]
      rw [show (1 : ℝ[X]) = C 1 from C_1.symm, reverse_C]
      exact Splits.C 1
  | cons a t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain]
      exact (splits_reverse_linear a).mul ih

/-- **Reversal preserves splitting.**  If `p : ℝ[X]` splits over `ℝ` (is
real-rooted), so does its reversal `reverse p`.  This is the reversal counterpart
of Part V's `splits_derivative`, and the infrastructure Mathlib lacks that unlocks
the bottom/interior Newton steps.  Proof: factor `p = C (leadingCoeff p) · ∏(X-rᵢ)`
via `splits_iff_exists_multiset`, distribute `reverse` over the product
(`reverse_mul_of_domain`), and split each reversed factor (`splits_reverse_prod`,
with `reverse (C _) = C _`). -/
theorem splits_reverse {p : ℝ[X]} (hp : Splits p) : Splits (reverse p) := by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hp
  rw [hm, reverse_mul_of_domain, reverse_C]
  exact (Splits.C _).mul (splits_reverse_prod m)

/-- **A split real polynomial with nonzero constant term has nonnegative
discriminant in its three BOTTOM coefficients** — read directly on
`p.coeff 0, p.coeff 1, p.coeff 2`.

If `p : ℝ[X]` splits (is real-rooted over `ℝ`), has `natDegree = m + 2`, and has a
nonzero constant term `p.coeff 0 ≠ 0` (so `natTrailingDegree p = 0`), then applying
the Part VII top-step engine `discrim_iterate_derivative_top` to `reverse p` — which
splits (`splits_reverse`), still has `natDegree = m + 2`, and whose top three
coefficients are `p`'s bottom three (`coeff_reverse` + `revAt_le`) — gives
`0 ≤ discrim` of `p`'s bottom three coefficients.  For `p = ∏(X - xᵢ)` this is the
classical BOTTOM Newton log-concavity step `eₙ₋₁² ≥ eₙ₋₂ eₙ`, the reversal-mirror of
Part VII's top step and unreachable from Parts III/VII.  No sign hypothesis beyond
`coeff 0 ≠ 0` (all roots nonzero). -/
theorem discrim_reverse_bottom (m : ℕ) {p : ℝ[X]}
    (hp : Splits p) (h0 : p.coeff 0 ≠ 0) (hdeg : p.natDegree = m + 2) :
    0 ≤ discrim
        ((2 + m).descFactorial m • p.coeff 0)
        ((1 + m).descFactorial m • p.coeff 1)
        ((0 + m).descFactorial m • p.coeff 2) := by
  have htrail : p.natTrailingDegree = 0 := Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero h0)
  have hqdeg : (reverse p).natDegree = m + 2 := by
    rw [reverse_natDegree, hdeg, htrail, Nat.sub_zero]
  have h := discrim_iterate_derivative_top m (splits_reverse hp) hqdeg
  -- the top three coefficients of `reverse p` are `p`'s bottom three
  have e2 : (reverse p).coeff (2 + m) = p.coeff 0 := by
    rw [coeff_reverse, hdeg, revAt_le (by omega)]; congr 1; omega
  have e1 : (reverse p).coeff (1 + m) = p.coeff 1 := by
    rw [coeff_reverse, hdeg, revAt_le (by omega)]; congr 1; omega
  have e0 : (reverse p).coeff (0 + m) = p.coeff 2 := by
    rw [coeff_reverse, hdeg, revAt_le (by omega)]; congr 1; omega
  rwa [e2, e1, e0] at h

/-- **General-`n` bottom Newton inequality on the coefficients of a real-rooted
polynomial.**  For any `p : ℝ[X]` that splits with `natDegree = m + 2` and nonzero
constant term, the three bottom coefficients satisfy
`4 · (2+m).descFactorial m · m.descFactorial m · p.coeff 0 · p.coeff 2
  ≤ ((1+m).descFactorial m)² · p.coeff 1 ²`.
This is `discrim_reverse_bottom` written as the recognizable log-concavity
inequality `b² ≥ 4ac` on the bottom three coefficients — the honest calculus proof
of Newton's BOTTOM step, valid for every arity and all signed inputs (only the
constant term must be nonzero). -/
theorem newton_bottom_coeff_ineq (m : ℕ) {p : ℝ[X]}
    (hp : Splits p) (h0 : p.coeff 0 ≠ 0) (hdeg : p.natDegree = m + 2) :
    4 * ((2 + m).descFactorial m : ℝ) * ((0 + m).descFactorial m : ℝ)
        * p.coeff 0 * p.coeff 2
      ≤ ((1 + m).descFactorial m : ℝ) ^ 2 * p.coeff 1 ^ 2 := by
  have h := discrim_reverse_bottom m hp h0 hdeg
  rw [discrim] at h
  simp only [nsmul_eq_mul] at h
  nlinarith [h]

/-!  ## Part III, in explicit normalized (`p`) form

`newton_first_general` states the first Newton inequality in cleared-denominator
elementary-symmetric form (`2 n · e₂ ≤ (n-1) · e₁²`).  The corollary below restates
it in the genuine normalized shape `p₁² ≥ p₀ · p₂` with the actual Maclaurin means
`p₀ = 1`, `p₁ = e₁ / n`, and `p₂ = e₂ / binom n 2 = e₂ / (n(n-1)/2)`, for every
arity `n ≥ 2` and all signed reals — the explicit `p`-form counterpart of the
per-arity `newton_two_vars_normalized` / `newton_three_normalized`. -/

open Finset in
/-- **Newton's first inequality for arbitrary `n ≥ 2`, in normalized (`p`) form.**
With `p₀ = 1`, `p₁ = e₁ / n = (∑ xᵢ)/n`, and
`p₂ = e₂ / binom n 2 = (∑_{i<j} xᵢ xⱼ)/(n(n-1)/2)`, the first log-concavity step
`p₀ · p₂ ≤ p₁²` holds for all signed reals.  This is `newton_first_general`
(`2 n · e₂ ≤ (n-1) · e₁²`) divided down by the binomial normalizations, matching
the `p`-form used by `newton_two_vars_normalized` and `newton_three_normalized`. -/
theorem newton_first_general_normalized (n : ℕ) (hn : 2 ≤ n) (x : ℕ → ℝ) :
    (1 : ℝ) * ((∑ j ∈ range n, ∑ i ∈ range j, x i * x j) /
        ((n : ℝ) * ((n : ℝ) - 1) / 2))
      ≤ ((∑ i ∈ range n, x i) / (n : ℝ)) ^ 2 := by
  have h := newton_first_general n x
  -- abstract the two elementary-symmetric sums to keep the arithmetic small
  set S : ℝ := ∑ i ∈ range n, x i with hS
  set E : ℝ := ∑ j ∈ range n, ∑ i ∈ range j, x i * x j with hE
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hCpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) / 2 := by nlinarith
  have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [one_mul, div_pow]
  rw [div_le_div_iff₀ hCpos hn2pos]
  nlinarith [h, hnpos]

/-!  ## Part VIII — Vieta closure of the TOP step: the calculus route reaches
Newton's inequality on the elementary symmetric functions of the roots

Part VII proved `newton_top_coeff_ineq`, the honest calculus/Rolle discriminant
inequality on the top three *coefficients* `p.coeff (m+2), p.coeff (m+1),
p.coeff m` of an arbitrary real-rooted (`Splits`) polynomial `p`.  The single
remaining increment documented in `state.md` was purely algebraic: **substitute
the top coefficients via Vieta** — for a split polynomial
`p.coeff k = leadingCoeff · (-1)^{n-k} · eₙ₋ₖ(roots)` — to turn that coefficient
inequality into the classical Newton log-concavity statement on the elementary
symmetric functions of the roots.

Mathlib's `Polynomial.coeff_eq_esymm_roots_of_splits` supplies exactly this Vieta
substitution.  Reading the top three coefficients of a split degree-`(m+2)`
polynomial as `leadingCoeff`, `-leadingCoeff · e₁(roots)`, `leadingCoeff ·
e₂(roots)` (with `e₁ = p.roots.esymm 1`, `e₂ = p.roots.esymm 2`) turns
`newton_top_coeff_ineq` into a discriminant inequality in `e₁, e₂`, and the
`descFactorial` weights collapse — via `Nat.succ_descFactorial` — to the
recognizable classical constants, giving in the monic case

    `2 (m+2) · e₂ ≤ (m+1) · e₁²`,

i.e. the first Newton/Maclaurin inequality `e₁² ≥ (2n/(n-1)) e₂` for every arity
`n = m+2`, now as the END PRODUCT of the genuine Rolle/discriminant engine the
entry asks for (the same inequality Part III obtained independently by QM–AM).
This closes the "coefficient bookkeeping" gap for the top step: the classical
calculus proof now runs end-to-end, on one split polynomial of arbitrary degree,
all the way to a symmetric-function inequality in the roots. -/

/-- **Vieta substitution into the top Newton step (`coeff` → `esymm` of roots).**
For any `p : ℝ[X]` that splits over `ℝ` with `natDegree = m + 2`, the
top-coefficient Newton inequality `newton_top_coeff_ineq` becomes a log-concavity
inequality in the first two elementary symmetric functions
`e₁ = p.roots.esymm 1`, `e₂ = p.roots.esymm 2` of the roots:
`4 · (m+2)!desc · m!desc · lc² · e₂ ≤ ((m+1)!desc)² · lc² · e₁²`, with
`lc = p.leadingCoeff` and the `descFactorial` weights `(m+2).descFactorial m`,
`m.descFactorial m`, `(m+1).descFactorial m`.  Proof: `p.coeff (m+2) = lc`
(`coeff_natDegree`), and `p.coeff (m+1) = -lc · e₁`, `p.coeff m = lc · e₂` by
`coeff_eq_esymm_roots_of_splits`, substituted into `newton_top_coeff_ineq`. -/
theorem newton_top_esymm_roots (m : ℕ) {p : ℝ[X]}
    (hp : p.Splits) (hdeg : p.natDegree = m + 2) :
    4 * ((m + 2).descFactorial m : ℝ) * ((m).descFactorial m : ℝ)
        * p.leadingCoeff ^ 2 * p.roots.esymm 2
      ≤ ((m + 1).descFactorial m : ℝ) ^ 2 * p.leadingCoeff ^ 2
        * p.roots.esymm 1 ^ 2 := by
  have h := newton_top_coeff_ineq m hp hdeg
  rw [show (2 : ℕ) + m = m + 2 from by omega, show (1 : ℕ) + m = m + 1 from by omega,
    show (0 : ℕ) + m = m from by omega] at h
  have hc2 : p.coeff (m + 2) = p.leadingCoeff := by rw [← coeff_natDegree, hdeg]
  have hc1 : p.coeff (m + 1) = -(p.leadingCoeff * p.roots.esymm 1) := by
    rw [coeff_eq_esymm_roots_of_splits hp (show m + 1 ≤ p.natDegree from by omega),
      show p.natDegree - (m + 1) = 1 from by omega]
    ring
  have hc0 : p.coeff m = p.leadingCoeff * p.roots.esymm 2 := by
    rw [coeff_eq_esymm_roots_of_splits hp (show m ≤ p.natDegree from by omega),
      show p.natDegree - m = 2 from by omega]
    ring
  rw [hc2, hc1, hc0] at h
  nlinarith [h]

/-- **The classical TOP Newton inequality for a monic real-rooted polynomial,
via the calculus route.**  If `p : ℝ[X]` is monic, splits over `ℝ`, and has
`natDegree = m + 2`, then its roots' first two elementary symmetric functions
satisfy Newton's first log-concavity inequality
    `2 (m+2) · e₂ ≤ (m+1) · e₁²`,   `e₁ = p.roots.esymm 1`, `e₂ = p.roots.esymm 2`.
This is `newton_top_esymm_roots` with `leadingCoeff = 1`, after collapsing the
`descFactorial` weights with the two identities `2·(m+2).descFactorial m =
(m+2)·(m+1).descFactorial m` and `(m+1).descFactorial m = (m+1)·m.descFactorial m`
(both from `Nat.succ_descFactorial`).  It is the honest end product of the
Rolle/discriminant engine — the same first Newton inequality Part III proves by
QM–AM, here reached through the calculus route the entry asks for. -/
theorem newton_top_esymm_roots_monic (m : ℕ) {p : ℝ[X]}
    (hp : p.Splits) (hmonic : p.Monic) (hdeg : p.natDegree = m + 2) :
    2 * ((m : ℝ) + 2) * p.roots.esymm 2 ≤ ((m : ℝ) + 1) * p.roots.esymm 1 ^ 2 := by
  have hlc : p.leadingCoeff = 1 := hmonic.leadingCoeff
  have h := newton_top_esymm_roots m hp hdeg
  simp only [hlc, one_pow, mul_one] at h
  -- the two `descFactorial` collapse identities (over ℕ, then cast to ℝ)
  have id1 : 2 * (m + 2).descFactorial m = (m + 2) * (m + 1).descFactorial m := by
    have e := Nat.succ_descFactorial (m + 1) m
    rw [show m + 1 + 1 - m = 2 from by omega] at e
    exact e
  have id2 : (m + 1).descFactorial m = (m + 1) * m.descFactorial m := by
    have e := Nat.succ_descFactorial m m
    rw [show m + 1 - m = 1 from by omega, one_mul] at e
    exact e
  have id1R : 2 * ((m + 2).descFactorial m : ℝ) = ((m : ℝ) + 2) * ((m + 1).descFactorial m : ℝ) := by
    exact_mod_cast id1
  have id2R : ((m + 1).descFactorial m : ℝ) = ((m : ℝ) + 1) * (m.descFactorial m : ℝ) := by
    exact_mod_cast id2
  set A : ℝ := ((m + 2).descFactorial m : ℝ) with hA
  set B : ℝ := ((m + 1).descFactorial m : ℝ) with hB
  set C : ℝ := (m.descFactorial m : ℝ) with hC
  set e1 : ℝ := p.roots.esymm 1 with he1
  set e2 : ℝ := p.roots.esymm 2 with he2
  -- h : 4 * A * C * e2 ≤ B ^ 2 * e1 ^ 2
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hBpos : (0 : ℝ) < B := by
    rw [hB]; exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
  -- the key weight collapse: `2 (m+2) B² = (m+1) · 4 A C`
  have hident : 2 * ((m : ℝ) + 2) * B ^ 2 = ((m : ℝ) + 1) * (4 * A * C) := by
    linear_combination (-2 * B) * id1R + (4 * A) * id2R
  -- multiply the coefficient inequality by `(m+1) ≥ 0`
  have hmul : ((m : ℝ) + 1) * (4 * A * C * e2) ≤ ((m : ℝ) + 1) * (B ^ 2 * e1 ^ 2) :=
    mul_le_mul_of_nonneg_left h hm1
  -- assemble the `B²`-scaled target, then cancel `B² > 0`
  have key : 2 * ((m : ℝ) + 2) * e2 * B ^ 2 ≤ ((m : ℝ) + 1) * e1 ^ 2 * B ^ 2 := by
    have eL : 2 * ((m : ℝ) + 2) * e2 * B ^ 2 = ((m : ℝ) + 1) * (4 * A * C * e2) := by
      rw [show 2 * ((m : ℝ) + 2) * e2 * B ^ 2
            = e2 * (2 * ((m : ℝ) + 2) * B ^ 2) from by ring, hident]; ring
    have eR : ((m : ℝ) + 1) * e1 ^ 2 * B ^ 2 = ((m : ℝ) + 1) * (B ^ 2 * e1 ^ 2) := by ring
    rw [eL, eR]; exact hmul
  have hBsq : (0 : ℝ) < B ^ 2 := by positivity
  exact le_of_mul_le_mul_right key hBsq

end NewtonRealRooted
