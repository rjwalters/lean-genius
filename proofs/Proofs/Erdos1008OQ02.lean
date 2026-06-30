/-
Erdős Problem #1008 — Explicit Reiman / Zarankiewicz bound for C₄-free graphs

The parent formalization (`Proofs.Erdos1008Problem`, theorem
`Erdos1008.kovari_sos_turan`) proves the *implicit* Kővári–Sós–Turán quadratic
bound for the number of edges `m` of a C₄-free graph on `n` vertices:

    4 m² ≤ n²(n - 1) + 2 n m.

This file closes the obvious remaining gap: we *solve* that quadratic to obtain
the classical **explicit** extremal bound (Reiman 1958):

    m ≤ ¼ · n · (1 + √(4n - 3)),    i.e.   ex(n ; C₄) ≤ ¼ (1 + √(4n - 3)) · n.

This is the standard textbook closed form of the C₄ Zarankiewicz number; the
parent only carried the pre-solved quadratic inequality.

The core algebraic step `reiman_quadratic_solve` is a self-contained real-number
lemma (pure quadratic-formula manipulation, no graph theory), and the graph
corollary `c4free_edge_bound_explicit` simply feeds the parent's KST quadratic
into it.

Status: VERIFIED (0 axioms — depends only on `Erdos1008.kovari_sos_turan`,
which is itself axiom-free; the parent's `axiom erdos_1008` is *not* used).

Reference: I. Reiman, "Über ein Problem von K. Zarankiewicz", Acta Math. Acad.
Sci. Hungar. 9 (1958), 269–273.
-/

import Mathlib
import Proofs.Erdos1008Problem

open SimpleGraph Finset

namespace Erdos1008

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Solving the Kővári–Sós–Turán quadratic.**

Given nonnegative reals `m, n, s` with `n ≥ 1`, `s = √(4n-3)` (encoded as
`s² = 4n-3`, `s ≥ 0`), and the KST inequality `4 m² ≤ n²(n-1) + 2 n m`, the
edge count satisfies `4 m ≤ n (1 + s)`.

`n(1 ± s)/4` are exactly the two roots of `4 x² - 2 n x - n²(n-1)`; here we
extract the upper root. The proof avoids `Real.sqrt` entirely, working only with
the defining identity `s² = 4n-3`. -/
theorem reiman_quadratic_solve (m n s : ℝ)
    (hn : 1 ≤ n) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = 4 * n - 3)
    (hkst : 4 * m ^ 2 ≤ n ^ 2 * (n - 1) + 2 * n * m) :
    4 * m ≤ n * (1 + s) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hns : 0 ≤ n * s := mul_nonneg hn0 hs
  -- (n·s)² = n²·s² = n²(4n-3), and the KST bound forces (4m - n)² ≤ (n·s)².
  have hnssq : (n * s) ^ 2 = n ^ 2 * (4 * n - 3) := by rw [mul_pow, hs2]
  have hsq : (4 * m - n) ^ 2 ≤ (n * s) ^ 2 := by nlinarith [hkst, hnssq]
  rcases le_or_gt (4 * m) n with h | h
  · -- Trivial side: 4m ≤ n ≤ n(1+s).
    nlinarith [hns]
  · -- Main side: 4m > n, so 4m - n ≥ 0; with (4m-n)² ≤ (n·s)² this gives
    -- 4m - n ≤ n·s, hence 4m ≤ n + n·s = n(1+s).
    have hpos : 0 < 4 * m - n := by linarith
    have h4mn : 4 * m - n ≤ n * s := by nlinarith [hsq, hns, hpos]
    nlinarith [h4mn]

/-- **Explicit Reiman / Zarankiewicz bound for C₄-free graphs.**

A C₄-free simple graph on `n = |V| ≥ 1` vertices has at most
`¼ · n · (1 + √(4n - 3))` edges. This is the sharp closed-form extremal number
`ex(n ; C₄)` obtained by solving the parent's Kővári–Sós–Turán quadratic. -/
theorem c4free_edge_bound_explicit (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : IsC4Free G) (hV : 1 ≤ Fintype.card V) :
    (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) * (1 + Real.sqrt (4 * (Fintype.card V : ℝ) - 3)) / 4 := by
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  set m : ℝ := (G.edgeFinset.card : ℝ) with hm_def
  have hn1 : (1 : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hV
  have hrad : (0 : ℝ) ≤ 4 * n - 3 := by linarith
  set s : ℝ := Real.sqrt (4 * n - 3) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 4 * n - 3 := by rw [hs_def, Real.sq_sqrt hrad]
  have hkst := Erdos1008.kovari_sos_turan G hfree
  -- hkst : 4 * m ^ 2 ≤ n ^ 2 * (n - 1) + 2 * n * m
  have key : 4 * m ≤ n * (1 + s) :=
    reiman_quadratic_solve m n s hn1 hs0 hs2 hkst
  linarith

/-- Same bound in product form: `4·m ≤ n·(1 + √(4n-3))`. -/
theorem c4free_four_mul_edge_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : IsC4Free G) (hV : 1 ≤ Fintype.card V) :
    4 * (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) * (1 + Real.sqrt (4 * (Fintype.card V : ℝ) - 3)) := by
  have h := c4free_edge_bound_explicit G hfree hV
  linarith

/-- The roots `n(1 ± s)/4` of `4x² - 2nx - n²(n-1)` are genuine roots: with
`s² = 4n - 3` the upper root makes the KST quadratic vanish. This certifies that
the bound `reiman_quadratic_solve` extracts is *exact* (sharpness of the algebra,
independent of any extremal construction). -/
theorem reiman_root_exact (n s : ℝ) (hs2 : s ^ 2 = 4 * n - 3) :
    let R := n * (1 + s) / 4
    4 * R ^ 2 = n ^ 2 * (n - 1) + 2 * n * R := by
  intro R
  simp only [R]
  nlinarith [hs2]

end Erdos1008
