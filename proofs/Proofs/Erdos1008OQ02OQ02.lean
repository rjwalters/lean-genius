/-
Erdős Problem #1008 — Explicit Kővári–Sós–Turán bound for K_{2,t}-free graphs
(the algebraic quadratic core)

The sibling file `Proofs.Erdos1008OQ02` solves the *C₄-case* Kővári–Sós–Turán
quadratic (`reiman_quadratic_solve`): from the cherry-counting inequality
`4 m² ≤ n²(n-1) + 2 n m` — valid because in a C₄-free (= K_{2,2}-free) graph any
two vertices share at most **one** common neighbour — it extracts Reiman's
explicit bound `4 m ≤ n(1 + √(4n-3))`.

This file generalises that algebraic core to the full **K_{2,t}** family.  A
K_{2,t}-free graph is one in which any two vertices share at most `t-1` common
neighbours.  Double-counting cherries `a — v — b` then gives

      ∑_v C(d_v, 2) ≤ (t-1) · C(n, 2),

and with `∑ d_v = 2m` and convexity `∑ d_v² ≥ (2m)²/n` this rearranges to the
generalised Kővári–Sós–Turán quadratic

      4 m² ≤ (t-1) · n²(n-1) + 2 n m.

`kst_quadratic_solve` solves this quadratic in `m`, extracting the upper root

      4 m ≤ n · (1 + s),   where   s = √(1 + 4(t-1)(n-1)),

i.e. the classical closed form

      ex(n ; K_{2,t}) ≤ ¼ · (1 + √(1 + 4(t-1)(n-1))) · n
                      = ½ · (√(t-1) · n^{3/2} + n)   (leading order).

The C₄ result is the special case `t = 2` (`reiman_quadratic_solve_of_kst`,
where `1 + 4(t-1)(n-1) = 4n-3`), and `kst_root_exact` certifies that the extracted
root is *exact* — it makes the generalised quadratic vanish — so the algebra loses
nothing (sharpness is a matter of an extremal graph construction, not of the bound).

Everything here is a self-contained real-number identity/inequality (pure
quadratic-formula manipulation, `Real.sqrt` avoided via the defining identity
`s² = 1 + 4(t-1)(n-1)`); no graph theory and no axioms are used.  The remaining
gap toward a graph-level `ex(n ; K_{2,t})` theorem is the general cherry-count
`∑_v C(d_v,2) ≤ (t-1)·C(n,2)`, which would replay the parent's `kovari_sos_turan`
double-count with `t-1` in place of `1`; that graph corollary is the natural next
step.

Reference: T. Kővári, V. T. Sós, P. Turán, "On a problem of K. Zarankiewicz",
Colloq. Math. 3 (1954), 50–57.

Status: VERIFIED (0 sorries, 0 axioms).
-/

import Mathlib

namespace Erdos1008

/-- **Solving the general Kővári–Sós–Turán quadratic (K_{2,t}).**

Given nonnegative reals `m, n, s` with `n ≥ 1`, `s = √(1 + 4(t-1)(n-1))` (encoded
as `s² = 1 + 4(t-1)(n-1)`, `s ≥ 0`), and the generalised KST inequality
`4 m² ≤ (t-1)·n²(n-1) + 2 n m`, the edge count satisfies `4 m ≤ n (1 + s)`.

`n(1 ± s)/4` are exactly the two roots of the quadratic
`4 x² - 2 n x - (t-1) n²(n-1)`; here we extract the upper root.  Setting `t = 2`
recovers `reiman_quadratic_solve` (the C₄ case, `s = √(4n-3)`).  The proof avoids
`Real.sqrt`, using only the defining identity for `s²`. -/
theorem kst_quadratic_solve (t m n s : ℝ)
    (hn : 1 ≤ n) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1))
    (hkst : 4 * m ^ 2 ≤ (t - 1) * n ^ 2 * (n - 1) + 2 * n * m) :
    4 * m ≤ n * (1 + s) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hns : 0 ≤ n * s := mul_nonneg hn0 hs
  -- (n·s)² = n²·s² = n²(1 + 4(t-1)(n-1)), and the KST bound forces (4m - n)² ≤ (n·s)².
  have hnssq : (n * s) ^ 2 = n ^ 2 * (1 + 4 * (t - 1) * (n - 1)) := by rw [mul_pow, hs2]
  have hsq : (4 * m - n) ^ 2 ≤ (n * s) ^ 2 := by nlinarith [hkst, hnssq]
  rcases le_or_gt (4 * m) n with h | h
  · -- Trivial side: 4m ≤ n ≤ n(1+s).
    nlinarith [hns]
  · -- Main side: 4m > n, so 4m - n ≥ 0; with (4m-n)² ≤ (n·s)² this gives
    -- 4m - n ≤ n·s, hence 4m ≤ n + n·s = n(1+s).
    have hpos : 0 < 4 * m - n := by linarith
    have h4mn : 4 * m - n ≤ n * s := by nlinarith [hsq, hns, hpos]
    nlinarith [h4mn]

/-- **The C₄ case is `t = 2`.**  Specialising `kst_quadratic_solve` to `t = 2`
(where `1 + 4(t-1)(n-1) = 4n - 3` and `(t-1) = 1`) reproduces the sibling file's
`reiman_quadratic_solve` verbatim, certifying that the K_{2,t} generalisation is a
faithful extension of the C₄ result. -/
theorem reiman_quadratic_solve_of_kst (m n s : ℝ)
    (hn : 1 ≤ n) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = 4 * n - 3)
    (hkst : 4 * m ^ 2 ≤ n ^ 2 * (n - 1) + 2 * n * m) :
    4 * m ≤ n * (1 + s) := by
  refine kst_quadratic_solve 2 m n s hn hs ?_ ?_
  · rw [hs2]; ring
  · nlinarith [hkst]

/-- **Exactness of the extracted root.**  The upper root `R = n(1 + s)/4`, with
`s² = 1 + 4(t-1)(n-1)`, makes the generalised Kővári–Sós–Turán quadratic vanish:

      4 R² = (t-1) n²(n-1) + 2 n R.

So `kst_quadratic_solve` extracts a *genuine* root of the quadratic — the algebraic
bound is tight; any slack in `ex(n ; K_{2,t})` comes from the (in)existence of an
extremal graph attaining it, not from the quadratic-formula step.  Setting `t = 2`
recovers `reiman_root_exact`. -/
theorem kst_root_exact (t n s : ℝ) (hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1)) :
    let R := n * (1 + s) / 4
    4 * R ^ 2 = (t - 1) * n ^ 2 * (n - 1) + 2 * n * R := by
  intro R
  simp only [R]
  nlinarith [hs2]

end Erdos1008
