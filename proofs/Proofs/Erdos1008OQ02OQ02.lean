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

Status: 0 sorries, 0 axioms.  The algebraic core (`kst_quadratic_solve`,
`reiman_quadratic_solve_of_kst`, `kst_root_exact`) is docker-VERIFIED
(PR #36875); the algebraic-core additions `kst_lower_root_exact` (the lower root
`n(1-s)/4` also solves the quadratic) and `kst_quadratic_factor` (the full
factorization `4x² - 2nx - (t-1)n²(n-1) = 4(x - n(1+s)/4)(x - n(1-s)/4)`,
exhibiting *exactly* the two roots `n(1±s)/4`) are local-lean verified
(Lean v4.26.0 + pinned Mathlib oleans, 0 errors).  The graph-level section
(`kst_cherry_count_nat`,
`kst_graph_quadratic`, `kst_edge_bound`, `kst_edge_bound_of_free`) and the
leading-order closed form (`kst_radical_envelope`,
`kst_edge_bound_leading_order`, giving the recognisable
`ex(n ; K_{2,t}) ≤ ½(√(t-1)·n^{3/2}+n)`), together with the exact C₄
specialisations `reiman_edge_bound_of_free` (the graph-level Reiman bound
`4 m ≤ n(1+√(4n-3))`) and its forcing contrapositive `hasK2t_two_of_edge_bound_lt`,
were authored while the docker containerd backend was down; the *entire file* has
since been re-verified local-lean (Lean v4.26.0 + pinned Mathlib oleans, 0 errors,
every key theorem `#print axioms` = `[propext, Classical.choice, Quot.sound]`).
This session further adds the Vieta relations `kst_vieta_sum` / `kst_vieta_prod`
(pinning `R⁺+R⁻ = n/2` and `R⁺·R⁻ = -(t-1)n²(n-1)/4` to the quadratic's
coefficients) and the `K_{2,3}` closed form `k23_quadratic_solve_of_kst`
(discriminant `8n-7`, `m ≤ ¼ n(1+√(8n-7))`), also local-lean verified.

The final `GraphLevel` subsection generalises the whole graph-level development
from the `s = 2` (`K_{2,t}`) slice to the full **`K_{s,t}`** family, at the level
of the Kővári–Sós–Turán *combinatorial core* (the `s`-star double-count): `HasKst`
(the general `K_{s,t}` containment), the bridge `hasKst_two_iff_hasK2t`,
`codegree_lt_of_kstFree`, and the double-count `kst_star_count_nat` /
`kst_star_count_choose` / `kst_star_count_of_free` proving
`∑_v C(d_v, s) ≤ (t-1)·C(n, s)` for `K_{s,t}`-free graphs — the exact `s`-analogue
of `kst_cherry_count_nat`.  This session then carries out the remaining **convexity
(Jensen) step** and lands the closed-form edge bound: `kst_analytic_core` (the
abstract power-mean upgrade), `kst_general_power_bound`
(`(2m-(s-1)n)^s ≤ (t-1) n^{2s-1}`) and its `s`-th root
`kst_general_edge_bound_rpow` (`2m ≤ (t-1)^{1/s} n^{2-1/s} + (s-1)n`), the classical
Kővári–Sós–Turán bound for the full `K_{s,t}` family.  The convexity input is
Mathlib's power-mean inequality `pow_sum_le_card_mul_sum_pow` (Jensen for `x ↦ x^s`),
fed by the elementary casts `Nat.pow_sub_le_descFactorial` and
`Nat.descFactorial_le_pow`.  All additions are local-lean verified (Lean v4.26.0 +
pinned Mathlib oleans, 0 errors) and axiom-free
(`#print axioms kst_general_edge_bound_rpow = [propext, Classical.choice, Quot.sound]`).
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

/-- **The `K_{2,3}` case is `t = 3`.**  The next explicit instance of the family
above `C₄`: for a `K_{2,3}`-free graph the Kővári–Sós–Turán quadratic is
`4 m² ≤ 2 n²(n-1) + 2 n m` (coefficient `t-1 = 2`), whose discriminant collapses to
`1 + 4·2·(n-1) = 8n - 7`.  Solving it gives the explicit closed form
`m ≤ ¼ n(1 + √(8n-7))`, one rung of the Zarankiewicz ladder above the C₄ bound
`¼ n(1 + √(4n-3))`.  This is the direct analogue of `reiman_quadratic_solve_of_kst`
at `t = 3`, obtained by specialising `kst_quadratic_solve`. -/
theorem k23_quadratic_solve_of_kst (m n s : ℝ)
    (hn : 1 ≤ n) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = 8 * n - 7)
    (hkst : 4 * m ^ 2 ≤ 2 * n ^ 2 * (n - 1) + 2 * n * m) :
    4 * m ≤ n * (1 + s) := by
  refine kst_quadratic_solve 3 m n s hn hs ?_ ?_
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

/-- **Exactness of the *lower* extracted root.**  Companion to `kst_root_exact`:
the lower root `R⁻ = n(1 - s)/4`, with `s² = 1 + 4(t-1)(n-1)`, *also* makes the
generalised Kővári–Sós–Turán quadratic vanish,

      4 R⁻² = (t-1) n²(n-1) + 2 n R⁻.

Together with `kst_root_exact` this exhibits *both* roots `n(1 ± s)/4` of the
quadratic `4 x² - 2 n x - (t-1) n²(n-1)`.  Setting `t = 2` gives the C₄ lower
root `n(1 - √(4n-3))/4`. -/
theorem kst_lower_root_exact (t n s : ℝ) (hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1)) :
    let R := n * (1 - s) / 4
    4 * R ^ 2 = (t - 1) * n ^ 2 * (n - 1) + 2 * n * R := by
  intro R
  simp only [R]
  nlinarith [hs2]

/-- **Full factorization of the KST quadratic.**  With `s² = 1 + 4(t-1)(n-1)`, the
generalised Kővári–Sós–Turán quadratic factors completely over its two roots
`R^± = n(1 ± s)/4`:

      4 x² - 2 n x - (t-1) n²(n-1) = 4 · (x - n(1+s)/4) · (x - n(1-s)/4).

This is the definitive *"solving the quadratic"* statement underlying the whole
algebraic core: `kst_quadratic_solve` extracts the upper root `R⁺`, while
`kst_root_exact` / `kst_lower_root_exact` certify that `R⁺` and `R⁻` are roots —
this identity shows the quadratic has *exactly* those two roots and nothing more,
so the closed form loses no algebra.  Vieta's relations `R⁺ + R⁻ = n/2` and
`R⁺·R⁻ = -(t-1)n²(n-1)/4` are read off from the linear and constant coefficients
of the expanded right-hand side.  The proof is the polynomial identity closed by
`s² = 1 + 4(t-1)(n-1)`. -/
theorem kst_quadratic_factor (t n s x : ℝ)
    (hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1)) :
    4 * x ^ 2 - 2 * n * x - (t - 1) * n ^ 2 * (n - 1) =
      4 * (x - n * (1 + s) / 4) * (x - n * (1 - s) / 4) := by
  linear_combination (n ^ 2 / 4) * hs2

/-- **Vieta's sum relation.**  The two roots `R^± = n(1 ± s)/4` of the generalised
Kővári–Sós–Turán quadratic `4 x² - 2 n x - (t-1) n²(n-1)` sum to `n/2`, matching
`-b/a = 2n/4` read off from the leading coefficient `a = 4` and linear coefficient
`b = -2n`.  Note this holds for *any* `s` (the sum is discriminant-free), reflecting
that the axis of symmetry `n/4` of the parabola does not depend on `t`. -/
theorem kst_vieta_sum (n s : ℝ) :
    n * (1 + s) / 4 + n * (1 - s) / 4 = n / 2 := by
  ring

/-- **Vieta's product relation.**  The two roots `R^± = n(1 ± s)/4`, with
`s² = 1 + 4(t-1)(n-1)`, multiply to `-(t-1) n²(n-1) / 4`, matching `c/a` read off
from the leading coefficient `a = 4` and constant coefficient `c = -(t-1)n²(n-1)`.
Together with `kst_vieta_sum` these are the Vieta relations promised in the
`kst_quadratic_factor` docstring, pinning both symmetric functions of the roots to
the quadratic's coefficients; the product carries the whole discriminant dependence
via `1 - s² = -4(t-1)(n-1)`. -/
theorem kst_vieta_prod (t n s : ℝ) (hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1)) :
    (n * (1 + s) / 4) * (n * (1 - s) / 4) = -((t - 1) * n ^ 2 * (n - 1)) / 4 := by
  nlinarith [hs2]

/-- **Classical Kővári–Sós–Turán closed form.**  From the generalised KST quadratic
`4 m² ≤ (t-1)·n²(n-1) + 2 n m` (for `t ≥ 2`, `n ≥ 1`, `m ≥ 0`) the edge count obeys the
textbook bound

      m ≤ ½ · (√(t-1) · n^{3/2} + n).

This is the recognizable form `ex(n ; K_{2,t}) ≤ ½(√(t-1)·n^{3/2} + n)` of Kővári, Sós
and Turán (1954), obtained from the exact upper root `n(1+s)/4` of
`kst_quadratic_solve` by the elementary discriminant estimate
`s = √(1 + 4(t-1)(n-1)) ≤ 1 + 2√(t-1)·√n` (squaring reduces it to
`0 ≤ 4√(t-1)·√n + 4(t-1)`).  Here `n^{3/2}` is written `n · √n`. -/
theorem kst_bound_classical (t m n : ℝ) (ht : 2 ≤ t) (hn : 1 ≤ n) (_hm : 0 ≤ m)
    (hkst : 4 * m ^ 2 ≤ (t - 1) * n ^ 2 * (n - 1) + 2 * n * m) :
    m ≤ (Real.sqrt (t - 1) * (n * Real.sqrt n) + n) / 2 := by
  have ht1 : (0 : ℝ) ≤ t - 1 := by linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  set a := Real.sqrt (t - 1) with ha_def
  set b := Real.sqrt n with hb_def
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = t - 1 := Real.sq_sqrt ht1
  have hb2 : b ^ 2 = n := Real.sq_sqrt hn0
  have hdisc : (0 : ℝ) ≤ 1 + 4 * (t - 1) * (n - 1) := by nlinarith
  set s := Real.sqrt (1 + 4 * (t - 1) * (n - 1)) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1) := Real.sq_sqrt hdisc
  have hsolve : 4 * m ≤ n * (1 + s) := kst_quadratic_solve t m n s hn hs0 hs2 hkst
  have hYnn : (0 : ℝ) ≤ 1 + 2 * a * b := by nlinarith [mul_nonneg ha hb]
  have hsle : s ≤ 1 + 2 * a * b := by
    have hXY : 1 + 4 * (t - 1) * (n - 1) ≤ (1 + 2 * a * b) ^ 2 := by
      nlinarith [mul_nonneg ha hb, ha2, hb2, sq_nonneg a]
    calc s = Real.sqrt (1 + 4 * (t - 1) * (n - 1)) := hs_def
      _ ≤ Real.sqrt ((1 + 2 * a * b) ^ 2) := Real.sqrt_le_sqrt hXY
      _ = 1 + 2 * a * b := Real.sqrt_sq hYnn
  have hcomb : 4 * m ≤ n * (1 + (1 + 2 * a * b)) := by
    nlinarith [hsolve, mul_le_mul_of_nonneg_left hsle hn0]
  nlinarith [hcomb]

/-! ### Graph-level Kővári–Sós–Turán bound for K_{2,t}

The algebraic core above (`kst_quadratic_solve`) is fed by a genuinely
graph-theoretic input: the **cherry-count** inequality

      ∑_v C(d_v, 2) ≤ (t-1) · C(n, 2)

for K_{2,t}-free graphs.  We formalise it here directly from the defining property
of K_{2,t}-freeness — *any two distinct vertices have at most `t-1` common
neighbours* — via a double count of cherries `a — v — b`.  Combined with the
handshaking lemma `∑ d_v = 2m`, Cauchy–Schwarz `(∑ d_v)² ≤ n·∑ d_v²`, and the
algebraic solver `kst_quadratic_solve`, this yields the graph-level closed form

      ex(n ; K_{2,t}) ≤ ¼ · (1 + √(1 + 4(t-1)(n-1))) · n.

This closes the gap flagged in the sibling algebraic file: the parent
`Erdos1008Problem.lean` only proved the `t = 2` (C₄) graph-level bound
(`kovari_sos_turan`); here we obtain the full K_{2,t} family. -/

section GraphLevel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Common neighbours of two vertices `a`, `b`, as a `Finset`. -/
def commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : Finset V :=
  G.neighborFinset a ∩ G.neighborFinset b

/-- Membership in `commonNbrs`: `v` is a common neighbour of `a` and `b` iff it is
    adjacent to both. -/
theorem mem_commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] {a b v : V} :
    v ∈ commonNbrs G a b ↔ G.Adj a v ∧ G.Adj b v := by
  simp only [commonNbrs, Finset.mem_inter, SimpleGraph.mem_neighborFinset]

/-- **Symmetry of common neighbours.** `commonNbrs G a b = commonNbrs G b a`:
    the set of common neighbours does not depend on the order of the pair, since
    it is the (commutative) intersection of the two neighbour sets.  The `K_{2,t}`
    codegree hypothesis `(commonNbrs G a b).card ≤ κ` is therefore symmetric in
    `a, b`, matching the unordered nature of the `K_{2,t}` obstruction. -/
theorem commonNbrs_comm (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    commonNbrs G a b = commonNbrs G b a := by
  simp only [commonNbrs, Finset.inter_comm]

/-- The common-neighbour count is symmetric in the two vertices. -/
theorem commonNbrs_card_comm (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    (commonNbrs G a b).card = (commonNbrs G b a).card := by
  rw [commonNbrs_comm]

/-- A vertex's common neighbours with itself are exactly its neighbours:
    `commonNbrs G a a = G.neighborFinset a`. -/
theorem commonNbrs_self (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    commonNbrs G a a = G.neighborFinset a := by
  simp only [commonNbrs, Finset.inter_self]

/-- `s.offDiag.card = s.card·(s.card-1)` (self-contained port). -/
private theorem finset_card_offDiag {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  have hdiag : s.diag.card = s.card := by
    have heq : s.diag = s.image (fun a => (a, a)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_diag, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨ha, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨hc, rfl⟩
    rw [heq]
    exact Finset.card_image_of_injective _ (fun _ _ h => congr_arg Prod.fst h)
  have hdisj : Disjoint s.diag s.offDiag := Finset.disjoint_diag_offDiag s
  have hunion : s.diag ∪ s.offDiag = s ×ˢ s := Finset.diag_union_offDiag s
  have hprod : s.card + s.offDiag.card = s.card * s.card := by
    have hcu := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_product, hdiag] at hcu
    omega
  have hfact : s.card * (s.card - 1) + s.card = s.card * s.card := by
    cases s.card with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring
  omega

/-- Cast helper `↑(d·(d-1)) = ↑d·(↑d-1)` for `d : ℕ` (self-contained port). -/
private theorem nat_cast_mul_pred (d : ℕ) :
    (↑(d * (d - 1)) : ℝ) = (↑d : ℝ) * ((↑d : ℝ) - 1) := by
  cases d with
  | zero => simp
  | succ n => push_cast [Nat.succ_sub_one]; ring

/-- Cauchy–Schwarz for finite sums: `(∑ f)² ≤ |V|·∑ f²` (self-contained port). -/
private theorem sq_sum_le_card (f : V → ℝ) :
    (∑ v : V, f v) ^ 2 ≤ (Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 := by
  suffices h : (0 : ℝ) ≤ ∑ i : V, ∑ j : V, (f i - f j) ^ 2 by
    have hexp : ∑ i : V, ∑ j : V, (f i - f j) ^ 2 =
        (2 : ℝ) * ((Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 - (∑ v : V, f v) ^ 2) := by
      trans ∑ i : V, ((Fintype.card V : ℝ) * f i ^ 2 -
            2 * f i * ∑ j : V, f j + ∑ j : V, f j ^ 2)
      · congr 1; ext i
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      · have h1 : ∑ i : V, (Fintype.card V : ℝ) * f i ^ 2 =
            (Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 := by
          rw [← Finset.mul_sum]
        have h2 : ∑ i : V, 2 * f i * ∑ j : V, f j = 2 * (∑ v : V, f v) ^ 2 := by
          have hrearrange : ∀ i : V, 2 * f i * ∑ j : V, f j = (2 * ∑ j : V, f j) * f i :=
            fun i => by ring
          simp_rw [hrearrange, ← Finset.mul_sum]; ring
        have h3 : ∑ i : V, ∑ j : V, f j ^ 2 = (Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        linarith
    linarith
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Graph-level cherry count for K_{2,t} (ℕ form).**  If any two *distinct*
vertices of `G` have at most `κ` common neighbours (this is K_{2,κ+1}-freeness),
then `∑_v d_v(d_v-1) ≤ κ · n(n-1)`.

The proof double-counts ordered cherries `(a,b)` with `a, b ∈ N(v)`, `a ≠ b`:
summed over `v` this equals `∑_{a≠b} |N(a) ∩ N(b)|`, and each common-neighbour
count is bounded by `κ`. -/
theorem kst_cherry_count_nat (G : SimpleGraph V) [DecidableRel G.Adj] (κ : ℕ)
    (hfree : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ κ) :
    ∑ v : V, G.degree v * (G.degree v - 1) ≤
      κ * (Fintype.card V * (Fintype.card V - 1)) := by
  -- Each degree cherry count is the offDiag cardinality of the neighbourhood.
  have hoff : ∀ v : V, (G.neighborFinset v).offDiag.card = G.degree v * (G.degree v - 1) := by
    intro v; rw [finset_card_offDiag, SimpleGraph.card_neighborFinset_eq_degree]
  have hoffU : (Finset.univ : Finset V).offDiag.card =
      Fintype.card V * (Fintype.card V - 1) := by
    rw [finset_card_offDiag, Finset.card_univ]
  -- offDiag of each neighbourhood embeds into offDiag of the whole vertex set.
  have hsub : ∀ v : V, (G.neighborFinset v).offDiag ⊆ (Finset.univ : Finset V).offDiag := by
    intro v p hp
    rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, hp.2.2⟩
  -- The core double count.
  have key : ∑ v : V, (G.neighborFinset v).offDiag.card ≤
      (Finset.univ : Finset V).offDiag.card * κ := by
    -- Rewrite each cherry card as a sum of indicators over all ordered pairs.
    have expand : ∀ v : V, (G.neighborFinset v).offDiag.card =
        ∑ p ∈ (Finset.univ : Finset V).offDiag,
          (if p ∈ (G.neighborFinset v).offDiag then 1 else 0) := by
      intro v
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (hsub v)]
    calc ∑ v : V, (G.neighborFinset v).offDiag.card
        = ∑ v : V, ∑ p ∈ (Finset.univ : Finset V).offDiag,
            (if p ∈ (G.neighborFinset v).offDiag then 1 else 0) :=
          Finset.sum_congr rfl (fun v _ => expand v)
      _ = ∑ p ∈ (Finset.univ : Finset V).offDiag, ∑ v : V,
            (if p ∈ (G.neighborFinset v).offDiag then 1 else 0) := Finset.sum_comm
      _ ≤ ∑ _p ∈ (Finset.univ : Finset V).offDiag, κ := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_offDiag] at hp
          rw [← Finset.card_filter]
          -- the fibre over pair p is exactly the common-neighbour set of p.1, p.2
          have hset : (Finset.univ.filter
              (fun v => p ∈ (G.neighborFinset v).offDiag)) = commonNbrs G p.1 p.2 := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag,
              SimpleGraph.mem_neighborFinset, commonNbrs, Finset.mem_inter]
            constructor
            · rintro ⟨hv1, hv2, _⟩; exact ⟨hv1.symm, hv2.symm⟩
            · rintro ⟨hv1, hv2⟩; exact ⟨hv1.symm, hv2.symm, hp.2.2⟩
          rw [hset]; exact hfree p.1 p.2 hp.2.2
      _ = (Finset.univ : Finset V).offDiag.card * κ := by
          rw [Finset.sum_const, smul_eq_mul]
  -- Convert offDiag cardinalities back to degree cherry counts.
  calc ∑ v : V, G.degree v * (G.degree v - 1)
      = ∑ v : V, (G.neighborFinset v).offDiag.card :=
        Finset.sum_congr rfl (fun v _ => (hoff v).symm)
    _ ≤ (Finset.univ : Finset V).offDiag.card * κ := key
    _ = κ * (Fintype.card V * (Fintype.card V - 1)) := by rw [hoffU]; ring

/-- **Graph-level Kővári–Sós–Turán quadratic for K_{2,t}.**  For a graph `G` on
`n` vertices with `m` edges in which any two distinct vertices share at most `κ`
common neighbours (K_{2,κ+1}-freeness),

      4 m² ≤ κ · n²(n-1) + 2 n m.

This is the graph-theoretic input to `kst_quadratic_solve`; the `κ = 1` case is
the parent file's `kovari_sos_turan`. -/
theorem kst_graph_quadratic (G : SimpleGraph V) [DecidableRel G.Adj] (κ : ℕ)
    (hfree : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ κ) :
    (4 : ℝ) * (G.edgeFinset.card : ℝ) ^ 2 ≤
      (κ : ℝ) * (Fintype.card V : ℝ) ^ 2 * ((Fintype.card V : ℝ) - 1)
      + 2 * (Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ) := by
  -- Step 1: cherry count in ℝ.
  have hcherry_real : ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) ≤
      (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
    have hnat := kst_cherry_count_nat G κ hfree
    calc ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1)
        = ((∑ v : V, G.degree v * (G.degree v - 1) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl (fun v _ => (nat_cast_mul_pred (G.degree v)).symm)
      _ ≤ ((κ * (Fintype.card V * (Fintype.card V - 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
          rw [Nat.cast_mul, nat_cast_mul_pred]
  -- Step 2: handshaking ∑ d_v = 2m.
  have hhand : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  -- Step 3: ∑ d_v² ≤ κ·n(n-1) + 2m via d² = d(d-1) + d.
  have hsum_sq : ∑ v : V, (G.degree v : ℝ) ^ 2 ≤
      (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))
      + 2 * (G.edgeFinset.card : ℝ) := by
    have hid : ∀ v : V, (G.degree v : ℝ) ^ 2 =
        (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + (G.degree v : ℝ) := fun v => by ring
    calc ∑ v : V, (G.degree v : ℝ) ^ 2
        = ∑ v, ((G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + (G.degree v : ℝ)) :=
          Finset.sum_congr rfl (fun v _ => hid v)
      _ = ∑ v, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + ∑ v, (G.degree v : ℝ) :=
          Finset.sum_add_distrib
      _ ≤ (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))
          + 2 * (G.edgeFinset.card : ℝ) := by linarith [hcherry_real, hhand]
  -- Step 4: Cauchy–Schwarz and combination.
  have hcs := sq_sum_le_card (fun v : V => (G.degree v : ℝ))
  rw [hhand] at hcs
  have hn0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  calc (4 : ℝ) * (G.edgeFinset.card : ℝ) ^ 2
      = (2 * (G.edgeFinset.card : ℝ)) ^ 2 := by ring
    _ ≤ (Fintype.card V : ℝ) * ∑ v : V, (G.degree v : ℝ) ^ 2 := hcs
    _ ≤ (Fintype.card V : ℝ) *
          ((κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))
            + 2 * (G.edgeFinset.card : ℝ)) := mul_le_mul_of_nonneg_left hsum_sq hn0
    _ = (κ : ℝ) * (Fintype.card V : ℝ) ^ 2 * ((Fintype.card V : ℝ) - 1)
          + 2 * (Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ) := by ring

/-- **Graph-level closed-form edge bound for K_{2,t}.**  For a nonempty graph `G`
on `n ≥ 1` vertices with `m` edges in which any two distinct vertices share at
most `κ` common neighbours,

      4 m ≤ n · (1 + √(1 + 4κ(n-1))).

Combining `kst_graph_quadratic` with the algebraic root extraction
`kst_quadratic_solve` (taking `t = κ + 1`). -/
theorem kst_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (κ : ℕ)
    (hfree : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ κ) :
    4 * (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) *
        (1 + Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1))) := by
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    have : 1 ≤ Fintype.card V := Fintype.card_pos
    exact_mod_cast this
  have harg : (0 : ℝ) ≤ 1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    have : (0 : ℝ) ≤ (κ : ℝ) * ((Fintype.card V : ℝ) - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  have hs0 : 0 ≤ Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1)) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1)) ^ 2 =
      1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1) := Real.sq_sqrt harg
  have hquad := kst_graph_quadratic G κ hfree
  refine kst_quadratic_solve ((κ : ℝ) + 1) (G.edgeFinset.card : ℝ) (Fintype.card V : ℝ)
    (Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1))) hn1 hs0 ?_ ?_
  · rw [hs2]; ring
  · have e : ((κ : ℝ) + 1 - 1) = (κ : ℝ) := by ring
    rw [e]; linarith [hquad]

/-- A graph *contains* K_{2,t}: two distinct vertices with at least `t` common
neighbours (the common neighbours are automatically distinct from `a`, `b`). -/
def HasK2t (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ (a b : V) (T : Finset V), a ≠ b ∧ t ≤ T.card ∧ (∀ y ∈ T, G.Adj a y ∧ G.Adj b y)

/-- In a K_{2,t}-free graph, any two distinct vertices share fewer than `t`
common neighbours (else those neighbours witness a K_{2,t}). -/
theorem commonNbrs_card_lt_of_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (hfree : ¬ HasK2t G t) (a b : V) (hab : a ≠ b) :
    (commonNbrs G a b).card < t := by
  by_contra h
  push_neg at h
  exact hfree ⟨a, b, commonNbrs G a b, hab, h, fun y hy => by
    simp only [commonNbrs, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
    exact hy⟩

/-- **`K_{2,t}`-containment is antitone in `t`.**  If `G` contains a `K_{2,t}` then it
also contains a `K_{2,s}` for every `s ≤ t`: the very same pair of vertices, together
with its `≥ t ≥ s` common neighbours, already witnesses the smaller complete bipartite
graph.  (The witness `T` is reused verbatim; only its cardinality lower bound is
weakened `t ↦ s`.) -/
theorem hasK2t_mono (G : SimpleGraph V) {s t : ℕ} (hst : s ≤ t) (h : HasK2t G t) :
    HasK2t G s := by
  obtain ⟨a, b, T, hab, htc, hadj⟩ := h
  exact ⟨a, b, T, hab, le_trans hst htc, hadj⟩

/-- **`K_{2,t}`-freeness is monotone in `t`.**  Dual to `hasK2t_mono`: a graph with no
`K_{2,s}` also has no `K_{2,t}` for any `t ≥ s`, since a `K_{2,t}` would contain a
`K_{2,s}`.  So the forbidden-subgraph hypothesis only *strengthens* as `t` grows — the
`t`-indexed family of K_{2,t}-free classes is nested `⋯ ⊇ Free(s) ⊇ Free(t) ⊇ ⋯`. -/
theorem not_hasK2t_mono (G : SimpleGraph V) {s t : ℕ} (hst : s ≤ t)
    (h : ¬ HasK2t G s) : ¬ HasK2t G t :=
  fun hcon => h (hasK2t_mono G hst hcon)

/-- **`K_{2,t}`-containment is a monotone graph property.**  If `G ≤ H` (every edge of `G`
is an edge of `H`) and `G` already contains a `K_{2,t}`, then so does `H`: the very same
pair `a, b` and common-neighbour set `T` still works, since each adjacency `G.Adj a y`
promotes to `H.Adj a y` along `G ≤ H`.  Together with `hasK2t_mono` (antitone in `t`) this
places `HasK2t` in the standard monotone-property framework — containment only grows as the
graph gains edges. -/
theorem hasK2t_mono_graph {G H : SimpleGraph V} (hle : G ≤ H) {t : ℕ} (h : HasK2t G t) :
    HasK2t H t := by
  obtain ⟨a, b, T, hab, htc, hadj⟩ := h
  exact ⟨a, b, T, hab, htc, fun y hy => ⟨hle (hadj y hy).1, hle (hadj y hy).2⟩⟩

/-- **`K_{2,t}`-freeness is hereditary to subgraphs.**  Dual to `hasK2t_mono_graph`: if
`G ≤ H` and `H` is `K_{2,t}`-free, then so is its subgraph `G` — deleting edges cannot create
a `K_{2,t}`.  So the class of `K_{2,t}`-free graphs is closed under taking subgraphs, the
hypothesis under which the Kővári–Sós–Turán edge bound (`kst_edge_bound_of_free`) applies. -/
theorem not_hasK2t_mono_graph {G H : SimpleGraph V} (hle : G ≤ H) {t : ℕ}
    (h : ¬ HasK2t H t) : ¬ HasK2t G t :=
  fun hcon => h (hasK2t_mono_graph hle hcon)

/-- **Common neighbours grow with the graph.**  If `G ≤ H` then every common neighbour of a
pair `a, b` in `G` is one in `H`: `commonNbrs G a b ⊆ commonNbrs H a b`.  The `Finset`-level
witness behind `hasK2t_mono_graph`, and the reason the codegree `(commonNbrs · a b).card`
is monotone under edge addition. -/
theorem commonNbrs_subset_of_le {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (a b : V) : commonNbrs G a b ⊆ commonNbrs H a b := by
  intro v hv
  simp only [commonNbrs, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hv ⊢
  exact ⟨hle hv.1, hle hv.2⟩

/-- **`K_{2,t}`-containment via the codegree Finset.**  The forbidden-subgraph definition
`HasK2t` (a distinct pair with a witness set `T` of `≥ t` common neighbours) is equivalent
to the concrete codegree statement `∃ a ≠ b, t ≤ (commonNbrs G a b).card`.  Forward: any
witness `T` embeds into `commonNbrs G a b` (`mem_commonNbrs`), so `t ≤ |T| ≤ |commonNbrs|`;
backward: `commonNbrs G a b` *is* a valid witness set.  This is the bridge between the
abstract `HasK2t` used in the monotonicity API and the concrete `(commonNbrs · ·).card`
codegree quantity the Kővári–Sós–Turán counting bounds are stated in — it internalises the
ad-hoc packing done inside `commonNbrs_card_lt_of_free`. -/
theorem hasK2t_iff_exists_commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) :
    HasK2t G t ↔ ∃ a b : V, a ≠ b ∧ t ≤ (commonNbrs G a b).card := by
  constructor
  · rintro ⟨a, b, T, hab, htc, hadj⟩
    refine ⟨a, b, hab, le_trans htc (Finset.card_le_card ?_)⟩
    intro y hy
    rw [mem_commonNbrs]
    exact hadj y hy
  · rintro ⟨a, b, hab, hcard⟩
    refine ⟨a, b, commonNbrs G a b, hab, hcard, fun y hy => ?_⟩
    rw [mem_commonNbrs] at hy
    exact hy

/-- **The `t = 0` base case: `K_{2,0}` is contained iff the graph has ≥ 2 vertices.**
`HasK2t G 0` asks only for a distinct pair `a ≠ b` (the empty common-neighbour set `T = ∅`
vacuously satisfies the `0 ≤ |T|` and adjacency requirements), so it holds exactly when `V`
is `Nontrivial`.  This is the bottom of the antitone-in-`t` tower (`hasK2t_mono`): every
graph on two or more vertices contains `K_{2,0}`, and the content only begins at `t ≥ 1`
where actual common neighbours are required. -/
theorem hasK2t_zero_iff (G : SimpleGraph V) : HasK2t G 0 ↔ Nontrivial V := by
  rw [nontrivial_iff]
  constructor
  · rintro ⟨a, b, _, hab, -, -⟩
    exact ⟨a, b, hab⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, ∅, hab, Nat.zero_le _, by simp⟩

/-- **K_{2,t}-free edge bound.**  A genuinely K_{2,t}-free nonempty graph
(`t ≥ 1`) satisfies the classical Kővári–Sós–Turán bound

      4 m ≤ n · (1 + √(1 + 4(t-1)(n-1))).

This packages `kst_edge_bound` with `commonNbrs_card_lt_of_free`, using the
forbidden-subgraph definition of K_{2,t}-freeness directly. -/
theorem kst_edge_bound_of_free (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (t : ℕ) (ht : 1 ≤ t) (hfree : ¬ HasK2t G t) :
    4 * (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) *
        (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * ((Fintype.card V : ℝ) - 1))) := by
  have hbound : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ t - 1 := fun a b hab => by
    have := commonNbrs_card_lt_of_free G t hfree a b hab; omega
  have h := kst_edge_bound G (t - 1) hbound
  have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht, Nat.cast_one]
  rwa [hcast] at h

/-- **Monotonicity of the exact KST bound in `t`.**  For `t ≤ t'` and `n ≥ 1` the
Reiman/KST right-hand side is non-decreasing in the parameter `t`:

      n · (1 + √(1 + 4(t-1)(n-1)))  ≤  n · (1 + √(1 + 4(t'-1)(n-1))).

The radicand is monotone because `(n-1) ≥ 0`, so the larger `t' - 1 ≥ t - 1` only
increases `4(t-1)(n-1)`; `√` and the nonnegative factor `n` preserve the order.  This
is the algebraic reason the extremal count `ex(n ; K_{2,t})` is non-decreasing in `t`:
forbidding the *larger* complete bipartite graph `K_{2,t'}` is a *weaker* constraint. -/
theorem kst_exact_bound_mono_t (t t' : ℕ) (htt' : t ≤ t') (n : ℝ) (hn : 1 ≤ n) :
    n * (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * (n - 1))) ≤
      n * (1 + Real.sqrt (1 + 4 * ((t' : ℝ) - 1) * (n - 1))) := by
  have hcast : (t : ℝ) ≤ (t' : ℝ) := by exact_mod_cast htt'
  have hn1 : (0 : ℝ) ≤ n - 1 := by linarith
  have hdiff : (0 : ℝ) ≤ (((t' : ℝ) - 1) - ((t : ℝ) - 1)) * (n - 1) :=
    mul_nonneg (by linarith) hn1
  have harg : 1 + 4 * ((t : ℝ) - 1) * (n - 1) ≤ 1 + 4 * ((t' : ℝ) - 1) * (n - 1) := by
    nlinarith [hdiff]
  have hsqrt := Real.sqrt_le_sqrt harg
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- **Monotonicity of the exact KST bound in `n`.**  For fixed `t ≥ 1` and `1 ≤ n ≤ n'`
the Reiman/KST right-hand side is non-decreasing in the vertex count `n`:

      n · (1 + √(1 + 4(t-1)(n-1)))  ≤  n' · (1 + √(1 + 4(t-1)(n'-1))).

Both factors grow: the leading `n ≤ n'`, and the radicand `1 + 4(t-1)(n-1)` increases
with `n` because `(t-1) ≥ 0`, so its `√` increases; the product of two nonnegative
non-decreasing factors is non-decreasing.  This is the `n`-companion of
`kst_exact_bound_mono_t`, recording that the extremal count `ex(n ; K_{2,t})` grows with
the number of vertices. -/
theorem kst_exact_bound_mono_n (t : ℕ) (ht : 1 ≤ t) {n n' : ℝ} (hn : 1 ≤ n)
    (hnn' : n ≤ n') :
    n * (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * (n - 1))) ≤
      n' * (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * (n' - 1))) := by
  have htm1 : (0 : ℝ) ≤ (t : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hstep : (0 : ℝ) ≤ 4 * ((t : ℝ) - 1) * (n' - n) :=
    mul_nonneg (mul_nonneg (by norm_num) htm1) (by linarith)
  have harg : 1 + 4 * ((t : ℝ) - 1) * (n - 1) ≤ 1 + 4 * ((t : ℝ) - 1) * (n' - 1) := by
    nlinarith [hstep]
  have hsqrt := Real.sqrt_le_sqrt harg
  have hc : (0 : ℝ) ≤ 1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * (n - 1)) := by positivity
  exact mul_le_mul hnn' (by linarith) hc (by linarith)

/-- **Joint monotonicity of the exact KST bound.**  Combining the `t`- and `n`-directions:
for `t ≤ t'` (with `t ≥ 1`) and `1 ≤ n ≤ n'`, the Reiman/KST bound at `(t, n)` is dominated
by the one at `(t', n')`.  A single order statement folding `kst_exact_bound_mono_t` and
`kst_exact_bound_mono_n`: forbidding a larger `K_{2,t'}` on more vertices only loosens the
edge bound. -/
theorem kst_exact_bound_mono (t t' : ℕ) (ht : 1 ≤ t) (htt' : t ≤ t')
    {n n' : ℝ} (hn : 1 ≤ n) (hnn' : n ≤ n') :
    n * (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * (n - 1))) ≤
      n' * (1 + Real.sqrt (1 + 4 * ((t' : ℝ) - 1) * (n' - 1))) :=
  le_trans (kst_exact_bound_mono_n t ht hn hnn')
    (kst_exact_bound_mono_t t t' htt' n' (le_trans hn hnn'))

/-- **Monotone (weaker-forbidden) KST bound.**  A `K_{2,t}`-free nonempty graph
(`t ≥ 1`) also satisfies the KST edge bound for every *larger* forbidden parameter
`t' ≥ t`:

      4 m ≤ n · (1 + √(1 + 4(t'-1)(n-1))).

Immediate from `kst_edge_bound_of_free` at `t` composed with the parameter
monotonicity `kst_exact_bound_mono_t`.  It records that the `t`-bound is the sharpest
of the family: a graph avoiding `K_{2,t}` a fortiori respects every looser
`K_{2,t'}` estimate. -/
theorem kst_edge_bound_of_free_mono_t (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (t t' : ℕ) (ht : 1 ≤ t) (htt' : t ≤ t') (hfree : ¬ HasK2t G t) :
    4 * (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) *
        (1 + Real.sqrt (1 + 4 * ((t' : ℝ) - 1) * ((Fintype.card V : ℝ) - 1))) := by
  have hn : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    have : 1 ≤ Fintype.card V := Fintype.card_pos
    exact_mod_cast this
  exact le_trans (kst_edge_bound_of_free G t ht hfree)
    (kst_exact_bound_mono_t t t' htt' (Fintype.card V : ℝ) hn)

/-- **Nested-radical envelope.**  For `t ≥ 1` and any `n ≥ 0` the Reiman/KST radical
is dominated by a sum of *separated* radicals:

      √(1 + 4(t-1)(n-1)) ≤ 1 + 2·√(t-1)·√n.

This is the algebraic step that turns the exact nested-radical closed form into the
recognisable leading-order bound; it uses only `A² = t-1`, `B² = n`
(`A = √(t-1)`, `B = √n`) and `AB ≥ 0`, the squared comparison reducing to
`-4(t-1) ≤ 4·AB`. -/
theorem kst_radical_envelope (t : ℕ) (ht : 1 ≤ t) (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt (1 + 4 * ((t : ℝ) - 1) * (n - 1)) ≤
      1 + 2 * Real.sqrt ((t : ℝ) - 1) * Real.sqrt n := by
  have htm1 : (0 : ℝ) ≤ (t : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hA0 : 0 ≤ Real.sqrt ((t : ℝ) - 1) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hAB : 0 ≤ Real.sqrt ((t : ℝ) - 1) * Real.sqrt n := mul_nonneg hA0 hB0
  -- (A·B)² = (t-1)·n, obtained from A² = t-1, B² = n.
  have hab2 : (Real.sqrt ((t : ℝ) - 1) * Real.sqrt n) ^ 2 = ((t : ℝ) - 1) * n := by
    rw [mul_pow, Real.sq_sqrt htm1, Real.sq_sqrt hn]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [hab2, hAB, htm1]

/-- **Leading-order Kővári–Sós–Turán bound for K_{2,t}.**  The recognisable textbook
closed form: a K_{2,t}-free nonempty graph (`t ≥ 1`) on `n` vertices with `m` edges
satisfies

      m ≤ ½ · (√(t-1) · n^{3/2} + n),

with `n^{3/2}` written as `n · √n`.  This is the classical
`ex(n ; K_{2,t}) = O(√(t-1) · n^{3/2})` bound of Kővári–Sós–Turán, obtained from the
exact nested-radical form `kst_edge_bound_of_free` by dominating the radical via
`kst_radical_envelope`.  Setting `t = 2` gives the Reiman leading term
`ex(n ; C₄) ≤ ½(n^{3/2} + n)`. -/
theorem kst_edge_bound_leading_order (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (t : ℕ) (ht : 1 ≤ t) (hfree : ¬ HasK2t G t) :
    (G.edgeFinset.card : ℝ) ≤
      (Real.sqrt ((t : ℝ) - 1) * (Fintype.card V : ℝ) * Real.sqrt (Fintype.card V)
        + (Fintype.card V : ℝ)) / 2 := by
  have hn0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hbound := kst_edge_bound_of_free G t ht hfree
  have henv := kst_radical_envelope t ht (Fintype.card V : ℝ) hn0
  -- n·(1 + radical) ≤ n·(2 + 2·√(t-1)·√n), monotonicity in the nonnegative factor n.
  have hstep : (Fintype.card V : ℝ) *
      (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * ((Fintype.card V : ℝ) - 1))) ≤
      (Fintype.card V : ℝ) *
        (2 + 2 * Real.sqrt ((t : ℝ) - 1) * Real.sqrt (Fintype.card V)) :=
    mul_le_mul_of_nonneg_left (by nlinarith [henv]) hn0
  -- Chain: 4m ≤ n(1+rad) ≤ n(2 + 2√(t-1)√n) = 2n + 2·√(t-1)·n·√n.
  nlinarith [hbound, hstep, hn0]

/-- **Reiman's C₄ leading-order bound (graph-level `t = 2` specialisation).**
A `C₄`-free (`K_{2,2}`-free) graph on `n` vertices with `m` edges satisfies the
recognisable Reiman (1958) leading-order estimate

      m ≤ ½ · (n^{3/2} + n),

with `n^{3/2}` written as `n · √n`.  This is the `t = 2` case of
`kst_edge_bound_leading_order`, where the coefficient `√(t-1)` collapses to
`√1 = 1`, recovering `ex(n ; C₄) = O(n^{3/2})` and tying the `K_{2,t}` family back
to the parent `C₄` entry. -/
theorem reiman_edge_bound_leading_order (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hfree : ¬ HasK2t G 2) :
    (G.edgeFinset.card : ℝ) ≤
      ((Fintype.card V : ℝ) * Real.sqrt (Fintype.card V) + (Fintype.card V : ℝ)) / 2 := by
  have h := kst_edge_bound_leading_order G 2 (by norm_num) hfree
  have hsqrt : Real.sqrt (((2 : ℕ) : ℝ) - 1) = 1 := by
    rw [show (((2 : ℕ) : ℝ) - 1) = 1 by norm_num, Real.sqrt_one]
  rw [hsqrt, one_mul] at h
  exact h

/-- **Forcing direction (exact form).**  The extremal *existence* content of
Kővári–Sós–Turán: a nonempty graph (`t ≥ 1`) whose edge count *exceeds* the exact
Reiman/KST nested-radical threshold must actually *contain* a `K_{2,t}`, i.e.
some pair of distinct vertices with `t` common neighbours.  This is the
contrapositive of `kst_edge_bound_of_free` — the reason the bound is a genuine
Turán-type theorem (too many edges force the forbidden subgraph), not merely an
inequality on `K_{2,t}`-free graphs. -/
theorem hasK2t_of_edge_bound_lt (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (t : ℕ) (ht : 1 ≤ t)
    (hm : (Fintype.card V : ℝ) *
        (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * ((Fintype.card V : ℝ) - 1)))
        < 4 * (G.edgeFinset.card : ℝ)) :
    HasK2t G t := by
  by_contra hfree
  exact absurd (kst_edge_bound_of_free G t ht hfree) (not_le.2 hm)

/-- **Forcing direction (leading-order form).**  If a nonempty graph (`t ≥ 1`) has
more than `½·(√(t-1)·n^{3/2} + n)` edges then it contains `K_{2,t}`.  The
recognisable `ex(n ; K_{2,t}) = O(√(t-1)·n^{3/2})` existence threshold, obtained as
the contrapositive of `kst_edge_bound_leading_order`. -/
theorem hasK2t_of_edge_bound_leading_order_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (t : ℕ) (ht : 1 ≤ t)
    (hm : (Real.sqrt ((t : ℝ) - 1) * (Fintype.card V : ℝ) * Real.sqrt (Fintype.card V)
        + (Fintype.card V : ℝ)) / 2 < (G.edgeFinset.card : ℝ)) :
    HasK2t G t := by
  by_contra hfree
  exact absurd (kst_edge_bound_leading_order G t ht hfree) (not_le.2 hm)

/-- **Reiman C₄ forcing threshold (graph-level `t = 2`).**  A graph on `n` vertices
with more than `½·(n^{3/2} + n)` edges contains a `C₄` (`K_{2,2}`).  The `t = 2`
specialisation of `hasK2t_of_edge_bound_leading_order_lt`, tying the extremal
existence threshold back to the parent `C₄` entry. -/
theorem hasK2t_two_of_edge_bound_leading_order_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V]
    (hm : ((Fintype.card V : ℝ) * Real.sqrt (Fintype.card V) + (Fintype.card V : ℝ)) / 2
        < (G.edgeFinset.card : ℝ)) :
    HasK2t G 2 := by
  by_contra hfree
  exact absurd (reiman_edge_bound_leading_order G hfree) (not_le.2 hm)

/-- **Reiman's exact C₄ edge bound (graph-level `t = 2`).**  A `C₄`-free
(`K_{2,2}`-free) nonempty graph on `n` vertices with `m` edges satisfies Reiman's
(1958) *exact* nested-radical bound

      4 m ≤ n · (1 + √(4n - 3)).

This is the `t = 2` case of `kst_edge_bound_of_free`, where the general K_{2,t}
discriminant `1 + 4(t-1)(n-1)` collapses to `4n - 3`.  It is the graph-level
counterpart of the sibling file's algebraic `reiman_quadratic_solve` and the
*exact* (pre-leading-order) sharpening of `reiman_edge_bound_leading_order`,
tying the K_{2,t} family back to the parent `C₄` (`erdos-1008-oq-02`) entry at
full radical precision. -/
theorem reiman_edge_bound_of_free (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hfree : ¬ HasK2t G 2) :
    4 * (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) * (1 + Real.sqrt (4 * (Fintype.card V : ℝ) - 3)) := by
  have h := kst_edge_bound_of_free G 2 (by norm_num) hfree
  have hdisc : (1 + 4 * (((2 : ℕ) : ℝ) - 1) * ((Fintype.card V : ℝ) - 1)) =
      4 * (Fintype.card V : ℝ) - 3 := by push_cast; ring
  rwa [hdisc] at h

/-- **Reiman C₄ exact forcing threshold (graph-level `t = 2`).**  A nonempty graph
on `n` vertices with more than `¼·n·(1 + √(4n - 3))` edges contains a `C₄`
(`K_{2,2}`).  The `t = 2` *exact-form* specialisation of `hasK2t_of_edge_bound_lt`
and the contrapositive of `reiman_edge_bound_of_free`; it gives the sharp
nested-radical (pre-leading-order) existence threshold, refining
`hasK2t_two_of_edge_bound_leading_order_lt`. -/
theorem hasK2t_two_of_edge_bound_lt (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hm : (Fintype.card V : ℝ) * (1 + Real.sqrt (4 * (Fintype.card V : ℝ) - 3))
        < 4 * (G.edgeFinset.card : ℝ)) :
    HasK2t G 2 := by
  by_contra hfree
  exact absurd (reiman_edge_bound_of_free G hfree) (not_le.2 hm)

/-! ### Codegree basics: the common-neighbour count is bounded by the degree

The Kővári–Sós–Turán codegree hypothesis caps `(commonNbrs G a b).card` from above by
the forbidden-subgraph parameter (`< t` in a `K_{2,t}`-free graph, via
`commonNbrs_card_lt_of_free`).  Independently of any freeness hypothesis, the codegree
is bounded by the *degree* of either endpoint — every common neighbour of `a, b` is in
particular a neighbour of `a` (and of `b`).  These are the elementary set-inclusions
behind that bound, plus the observation (asserted in the `HasK2t` docstring) that a
vertex is never its own common neighbour: `a ∉ commonNbrs G a b`, since a simple graph
has no loops. -/

/-- **Common neighbours are neighbours of the first vertex:**
    `commonNbrs G a b ⊆ N(a)`.  Immediate from `commonNbrs = N(a) ∩ N(b)`. -/
theorem commonNbrs_subset_neighborFinset_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : commonNbrs G a b ⊆ G.neighborFinset a := by
  simp only [commonNbrs]; exact Finset.inter_subset_left

/-- **Common neighbours are neighbours of the second vertex:**
    `commonNbrs G a b ⊆ N(b)`.  The right-hand companion of
    `commonNbrs_subset_neighborFinset_left`. -/
theorem commonNbrs_subset_neighborFinset_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : commonNbrs G a b ⊆ G.neighborFinset b := by
  simp only [commonNbrs]; exact Finset.inter_subset_right

/-- **Codegree is bounded by the first degree:** `(commonNbrs G a b).card ≤ d(a)`.
    Every common neighbour of `a, b` is a neighbour of `a`, so the codegree cannot
    exceed `a`'s degree.  A freeness-free upper bound complementing
    `commonNbrs_card_lt_of_free` (`< t` in a `K_{2,t}`-free graph). -/
theorem commonNbrs_card_le_degree_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : (commonNbrs G a b).card ≤ G.degree a := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (commonNbrs_subset_neighborFinset_left G a b)

/-- **Codegree is bounded by the second degree:** `(commonNbrs G a b).card ≤ d(b)`.
    The right-hand companion of `commonNbrs_card_le_degree_left`; together they give
    `(commonNbrs G a b).card ≤ min (d a) (d b)`. -/
theorem commonNbrs_card_le_degree_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : (commonNbrs G a b).card ≤ G.degree b := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (commonNbrs_subset_neighborFinset_right G a b)

/-- **A vertex is not its own common neighbour:** `a ∉ commonNbrs G a b`.  Membership
    would require `G.Adj a a`, impossible in a loopless simple graph (`G.irrefl`).  This
    proves the parenthetical in the `HasK2t` definition — the common neighbours are
    automatically distinct from the pair `a, b`. -/
theorem notMem_commonNbrs_left (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    a ∉ commonNbrs G a b := by
  rw [mem_commonNbrs]
  rintro ⟨haa, -⟩
  exact G.irrefl haa

/-- **A vertex is not its own common neighbour (second slot):** `b ∉ commonNbrs G a b`.
    The companion of `notMem_commonNbrs_left`; membership would need `G.Adj b b`. -/
theorem notMem_commonNbrs_right (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    b ∉ commonNbrs G a b := by
  rw [mem_commonNbrs]
  rintro ⟨-, hbb⟩
  exact G.irrefl hbb

/-!
### General `K_{s,t}` codegree double-count (Kővári–Sós–Turán combinatorial core)

The graph-level bounds above are the `s = 2` slice of Kővári–Sós–Turán: two
vertices (`K_{2,t}`) and a codegree hypothesis on *pairs*.  The genuine
Kővári–Sós–Turán double-count is the `s`-general statement — count *`s`-stars*
`(S, v)` with `S` an `s`-subset of `N(v)`:

      ∑_v C(d_v, s) = ∑_{S : |S| = s} codeg(S) ≤ (t-1)·C(n, s),

valid in a `K_{s,t}`-free graph because every `s`-set of vertices then has at
most `t-1` common neighbours.  This is the exact `s`-generalisation of
`kst_cherry_count_nat` (which is the `s = 2` case, `∑ d(d-1) = ∑ 2·C(d,2)`).

The double-count itself needs no analysis and is proved here in full.  The
convexity step toward a closed-form `ex(n ; K_{s,t}) = O((t-1)^{1/s}·n^{2-1/s})`
edge bound — `∑_v C(d_v, s) ≥ n·C(2m/n, s)`, Jensen for the convex map
`x ↦ C(x, s)` — **is now carried out** below (`kst_analytic_core`,
`kst_general_power_bound`, `kst_general_edge_bound_rpow`).  Rather than proving
convexity of the descending factorial directly, we route through the sharp
elementary lower bound `C(d, s) ≥ (d-s+1)^s/s!` (each of the `s` descending factors
is `≥ d-s+1`, `Nat.pow_sub_le_descFactorial`) and Mathlib's power-mean inequality
`pow_sum_le_card_mul_sum_pow` (Jensen for the convex `x ↦ x^s`), which for `s = 2`
degenerates to the Cauchy–Schwarz `sq_sum_le_card` used above.
-/

/-- **General `K_{s,t}` containment.**  There is a set `S` of `s` vertices with at
least `t` common neighbours `T` (every vertex of `T` adjacent to every vertex of
`S`).  This is the bipartite `K_{s,t}` as a subgraph — no edges are required
*within* `S` or *within* `T`.  For `s = 2` it is equivalent to `HasK2t`
(`hasKst_two_iff_hasK2t`).  The common neighbours `T` are automatically disjoint
from `S` (a vertex adjacent to itself is excluded by `G.irrefl`), so no extra
disjointness hypothesis is needed.  `Fintype`/`DecidableEq` are carried by the
enclosing section but unused by this definition and the `s = 2` bridge. -/
def HasKst (G : SimpleGraph V) (s t : ℕ) : Prop :=
  ∃ (S T : Finset V), S.card = s ∧ t ≤ T.card ∧ (∀ a ∈ S, ∀ v ∈ T, G.Adj a v)

/-- **`HasKst` at `s = 2` is `HasK2t`.**  The general `s`-set formulation
specialises to the ordered-pair `K_{2,t}` definition used by the graph-level KST
API above: an `s = 2` witness set `{a, b}` (`a ≠ b` from `S.card = 2`) is exactly
a distinct pair, and "every vertex of `T` adjacent to every vertex of `S`" unpacks
to "adjacent to both `a` and `b`". -/
theorem hasKst_two_iff_hasK2t (G : SimpleGraph V) (t : ℕ) :
    HasKst G 2 t ↔ HasK2t G t := by
  constructor
  · rintro ⟨S, T, hScard, hTcard, hadj⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hScard
    refine ⟨a, b, T, hab, hTcard, fun y hy => ⟨?_, ?_⟩⟩
    · exact hadj a (by simp) y hy
    · exact hadj b (by simp) y hy
  · rintro ⟨a, b, T, hab, hTcard, hadj⟩
    refine ⟨{a, b}, T, Finset.card_pair hab, hTcard, ?_⟩
    intro x hx v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (hadj v hv).1
    · exact (hadj v hv).2

/-- **Codegree bound from `K_{s,t}`-freeness.**  In a `K_{s,t}`-free graph any
`s`-set `S` of vertices has fewer than `t` common neighbours: otherwise those
`≥ t` common neighbours would witness a `K_{s,t}`.  The `s`-general analogue of
`commonNbrs_card_lt_of_free` (the `s = 2` codegree-`< t` statement).  The common
neighbours of `S` are collected as `univ.filter (S ⊆ N(v))`. -/
theorem codegree_lt_of_kstFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (hfree : ¬ HasKst G s t) (S : Finset V) (hS : S.card = s) :
    (Finset.univ.filter (fun v => S ⊆ G.neighborFinset v)).card < t := by
  by_contra h
  push_neg at h
  refine hfree ⟨S, Finset.univ.filter (fun v => S ⊆ G.neighborFinset v), hS, h, ?_⟩
  intro a ha v hv
  rw [Finset.mem_filter] at hv
  have hav : a ∈ G.neighborFinset v := hv.2 ha
  rw [SimpleGraph.mem_neighborFinset] at hav
  exact hav.symm

/-- **General `s`-star double count (`ℕ`, powerset form).**  If every `s`-set of
vertices has at most `κ` common neighbours, then the total number of `s`-stars
`∑_v |{S ⊆ N(v) : |S| = s}|` is at most `κ · C(n, s)`.

The proof double-counts incidences `(S, v)` with `S ∈ (N(v)).powersetCard s`:
summed over `v` and swapped (`Finset.sum_comm`), the fibre over each `s`-set `S`
is exactly its common-neighbour set `univ.filter (S ⊆ N(v))`, bounded by `κ`; the
number of `s`-sets is `C(n, s)` (`Finset.card_powersetCard`).  This is the
`s`-generalisation of the cherry double-count `kst_cherry_count_nat`. -/
theorem kst_star_count_nat (G : SimpleGraph V) [DecidableRel G.Adj] (s κ : ℕ)
    (hfree : ∀ S : Finset V, S.card = s →
      (Finset.univ.filter (fun v => S ⊆ G.neighborFinset v)).card ≤ κ) :
    ∑ v : V, ((G.neighborFinset v).powersetCard s).card ≤
      κ * (Fintype.card V).choose s := by
  have hsub : ∀ v : V,
      (G.neighborFinset v).powersetCard s ⊆ (Finset.univ : Finset V).powersetCard s := by
    intro v S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨Finset.subset_univ _, hS.2⟩
  have expand : ∀ v : V, ((G.neighborFinset v).powersetCard s).card =
      ∑ S ∈ (Finset.univ : Finset V).powersetCard s,
        (if S ∈ (G.neighborFinset v).powersetCard s then 1 else 0) := by
    intro v
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (hsub v)]
  calc ∑ v : V, ((G.neighborFinset v).powersetCard s).card
      = ∑ v : V, ∑ S ∈ (Finset.univ : Finset V).powersetCard s,
          (if S ∈ (G.neighborFinset v).powersetCard s then 1 else 0) :=
        Finset.sum_congr rfl (fun v _ => expand v)
    _ = ∑ S ∈ (Finset.univ : Finset V).powersetCard s, ∑ v : V,
          (if S ∈ (G.neighborFinset v).powersetCard s then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ _S ∈ (Finset.univ : Finset V).powersetCard s, κ := by
        apply Finset.sum_le_sum
        intro S hS
        rw [Finset.mem_powersetCard] at hS
        rw [← Finset.card_filter]
        have hset : (Finset.univ.filter
            (fun v => S ∈ (G.neighborFinset v).powersetCard s)) =
            Finset.univ.filter (fun v => S ⊆ G.neighborFinset v) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
          constructor
          · rintro ⟨hsv, _⟩; exact hsv
          · intro hsv; exact ⟨hsv, hS.2⟩
        rw [hset]
        exact hfree S hS.2
    _ = ((Finset.univ : Finset V).powersetCard s).card * κ := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = κ * (Fintype.card V).choose s := by
        rw [Finset.card_powersetCard, Finset.card_univ]; ring

/-- **General `s`-star double count (`choose` form).**  The recognisable
Kővári–Sós–Turán inequality on binomial codegrees: if every `s`-set has at most
`κ` common neighbours then

      ∑_v C(d_v, s) ≤ κ · C(n, s).

Rewrites `kst_star_count_nat` via `|{S ⊆ N(v) : |S| = s}| = C(d_v, s)`
(`Finset.card_powersetCard` + `card_neighborFinset_eq_degree`).  Setting `s = 2`,
`κ = t-1` recovers the content of `kst_cherry_count_nat`
(`∑ d(d-1) = ∑ 2·C(d,2) ≤ (t-1)·2·C(n,2)`). -/
theorem kst_star_count_choose (G : SimpleGraph V) [DecidableRel G.Adj] (s κ : ℕ)
    (hfree : ∀ S : Finset V, S.card = s →
      (Finset.univ.filter (fun v => S ⊆ G.neighborFinset v)).card ≤ κ) :
    ∑ v : V, (G.degree v).choose s ≤ κ * (Fintype.card V).choose s := by
  have h := kst_star_count_nat G s κ hfree
  calc ∑ v : V, (G.degree v).choose s
      = ∑ v : V, ((G.neighborFinset v).powersetCard s).card := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ κ * (Fintype.card V).choose s := h

/-- **`K_{s,t}`-free binomial codegree bound.**  The genuine Kővári–Sós–Turán
double-count in its forbidden-subgraph form: a `K_{s,t}`-free graph (`t ≥ 1`)
satisfies

      ∑_v C(d_v, s) ≤ (t-1) · C(n, s).

Combines `kst_star_count_choose` with `codegree_lt_of_kstFree` (every `s`-set has
`< t`, i.e. `≤ t-1`, common neighbours).  This is the `s`-general combinatorial
core; the passage to a closed-form edge bound needs the convexity of
`x ↦ C(x, s)` (Jensen), the analytic step recorded in the section note above. -/
theorem kst_star_count_of_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (ht : 1 ≤ t) (hfree : ¬ HasKst G s t) :
    ∑ v : V, (G.degree v).choose s ≤ (t - 1) * (Fintype.card V).choose s := by
  apply kst_star_count_choose G s (t - 1)
  intro S hS
  have h := codegree_lt_of_kstFree G s t hfree S hS
  omega

/-! ### The convexity (Jensen) step: from codegrees to a closed-form power bound

The combinatorial core `kst_star_count_of_free` delivers `∑_v C(d_v, s) ≤ (t-1) C(n, s)`.
The section note above flagged the remaining passage to a closed-form edge bound as
"the convexity of `x ↦ C(x, s)` (Jensen)".  We now carry out exactly that step, in the
sharp elementary form used in the classical Kővári–Sós–Turán proof.

The convexity input is packaged by Mathlib's power-mean inequality
`pow_sum_le_card_mul_sum_pow` (`(∑ f)^s ≤ n^{s-1} ∑ f^s` for `f ≥ 0`), which is Jensen
for the convex map `x ↦ x^s`.  Two elementary casts feed it:

* `Nat.pow_sub_le_descFactorial` : `(d+1-s)^s ≤ d(d-1)⋯(d-s+1) = s! · C(d, s)`
  (each of the `s` descending factors is `≥ d-s+1`), giving `f_v := (d_v+1-s)` with
  `f_v^s ≤ s! · C(d_v, s)`;
* `Nat.descFactorial_le_pow` : `s! · C(n, s) ≤ n^s`.

Chaining `(2m - (s-1)n) ≤ ∑_v f_v`, the power mean, the codegree bound and `s!·C(n,s) ≤ n^s`
yields the sharp KST power bound `(2m - (s-1)n)^s ≤ (t-1) · n^{2s-1}`. -/

/-- **Abstract analytic core of general Kővári–Sós–Turán.**  For any degree sequence
`d : ι → ℕ` on a finite vertex set with `2M = ∑_v d_v` (handshake) satisfying the
codegree double-count `∑_v C(d_v, s) ≤ (t-1) · C(n, s)`, the power-mean inequality
(Jensen for `x ↦ x^s`) upgrades it to the closed-form power bound

      (2M - (s-1)·n)^s ≤ (t-1) · n^{2s-1}

whenever `2M ≥ (s-1)·n` (the meaningful regime; below it the graph is trivially sparse).
This is stated abstractly in the degree sequence so it can be instantiated on any graph
via `kst_general_power_bound`. -/
theorem kst_analytic_core {ι : Type*} [Fintype ι] (d : ι → ℕ) (s t : ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (M : ℝ)
    (hM : (2 : ℝ) * M = ∑ v, (d v : ℝ))
    (hcore : ∑ v, ((d v).choose s : ℝ) ≤ ((t : ℝ) - 1) * ((Fintype.card ι).choose s : ℝ))
    (hL : (0 : ℝ) ≤ 2 * M - ((s : ℝ) - 1) * (Fintype.card ι)) :
    (2 * M - ((s : ℝ) - 1) * (Fintype.card ι)) ^ s
      ≤ ((t : ℝ) - 1) * (Fintype.card ι : ℝ) ^ (2 * s - 1) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  set f : ι → ℝ := fun v => ((d v + 1 - s : ℕ) : ℝ) with hf_def
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hNnn : (0 : ℝ) ≤ N := by positivity
  have hfnn : ∀ v ∈ (Finset.univ : Finset ι), 0 ≤ f v := fun v _ => by positivity
  -- per-vertex factor bound: `f_v^s ≤ s! · C(d_v, s)`
  have per : ∀ v, f v ^ s ≤ (s.factorial : ℝ) * ((d v).choose s : ℝ) := by
    intro v
    have h : (d v + 1 - s) ^ s ≤ s.factorial * (d v).choose s := by
      calc (d v + 1 - s) ^ s ≤ (d v).descFactorial s := Nat.pow_sub_le_descFactorial _ _
        _ = s.factorial * (d v).choose s := Nat.descFactorial_eq_factorial_mul_choose _ _
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this ⊢
    simpa [hf_def] using this
  -- `s! · C(n, s) ≤ n^s`
  have facN : (s.factorial : ℝ) * ((Fintype.card ι).choose s : ℝ) ≤ N ^ s := by
    have h : s.factorial * (Fintype.card ι).choose s ≤ (Fintype.card ι) ^ s := by
      calc s.factorial * (Fintype.card ι).choose s = (Fintype.card ι).descFactorial s :=
            (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
        _ ≤ (Fintype.card ι) ^ s := Nat.descFactorial_le_pow _ _
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    simpa [hN] using this
  -- summed factor bound: `∑ f_v^s ≤ (t-1) n^s`
  have sumf_sq : ∑ v, f v ^ s ≤ ((t : ℝ) - 1) * N ^ s := by
    calc ∑ v, f v ^ s ≤ ∑ v, (s.factorial : ℝ) * ((d v).choose s : ℝ) :=
          Finset.sum_le_sum (fun v _ => per v)
      _ = (s.factorial : ℝ) * ∑ v, ((d v).choose s : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ (s.factorial : ℝ) * (((t : ℝ) - 1) * ((Fintype.card ι).choose s : ℝ)) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = ((t : ℝ) - 1) * ((s.factorial : ℝ) * ((Fintype.card ι).choose s : ℝ)) := by ring
      _ ≤ ((t : ℝ) - 1) * N ^ s := mul_le_mul_of_nonneg_left facN (by linarith)
  -- linear lower bound: `2M - (s-1)n ≤ ∑ f_v`
  have sumf_lin : 2 * M - ((s : ℝ) - 1) * N ≤ ∑ v, f v := by
    have hterm : ∀ v ∈ (Finset.univ : Finset ι), ((d v : ℝ) + 1 - s) ≤ f v := by
      intro v _
      have hsub : (↑(d v + 1) : ℝ) - s ≤ ((d v + 1 - s : ℕ) : ℝ) := by
        rcases le_total s (d v + 1) with h | h
        · rw [Nat.cast_sub h]
        · rw [Nat.sub_eq_zero_of_le h]
          simp only [Nat.cast_zero, sub_nonpos]
          exact_mod_cast h
      simpa [hf_def] using (by push_cast at hsub ⊢; linarith : ((d v : ℝ) + 1 - s) ≤ f v)
    calc 2 * M - ((s : ℝ) - 1) * N
        = ∑ v, ((d v : ℝ) + 1 - s) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hM]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
          ring
      _ ≤ ∑ v, f v := Finset.sum_le_sum hterm
  -- power mean (Jensen for `x ↦ x^s`)
  have hpm : (∑ v, f v) ^ s ≤ N ^ (s - 1) * ∑ v, f v ^ s := by
    have h := pow_sum_le_card_mul_sum_pow hfnn (s - 1)
    rw [Nat.sub_add_cancel hs] at h
    simpa [hN, Finset.card_univ] using h
  -- assemble
  have step1 : (2 * M - ((s : ℝ) - 1) * N) ^ s ≤ (∑ v, f v) ^ s :=
    pow_le_pow_left₀ hL sumf_lin s
  have step2 : (∑ v, f v) ^ s ≤ N ^ (s - 1) * (((t : ℝ) - 1) * N ^ s) :=
    hpm.trans (mul_le_mul_of_nonneg_left sumf_sq (by positivity))
  have hexp : N ^ (s - 1) * (((t : ℝ) - 1) * N ^ s) = ((t : ℝ) - 1) * N ^ (2 * s - 1) := by
    rw [show 2 * s - 1 = (s - 1) + s by omega, pow_add]; ring
  calc (2 * M - ((s : ℝ) - 1) * N) ^ s
      ≤ N ^ (s - 1) * (((t : ℝ) - 1) * N ^ s) := step1.trans step2
    _ = ((t : ℝ) - 1) * N ^ (2 * s - 1) := hexp

/-- **General Kővári–Sós–Turán closed-form power bound.**  A `K_{s,t}`-free graph on
`n` vertices with `m` edges (`s ≥ 1`, `t ≥ 1`) satisfies

      (2m - (s-1)·n)^s ≤ (t-1) · n^{2s-1}

whenever `2m ≥ (s-1)·n`.  This is the sharp closed form of the codegree double-count
`kst_star_count_of_free`: instantiating the abstract Jensen core `kst_analytic_core` at
`d = G.degree`, `2m = ∑_v d_v` (handshake), and the `K_{s,t}`-free codegree bound.

Taking `s`-th roots gives the classical leading-order edge bound
`2m ≤ (t-1)^{1/s} · n^{2-1/s} + (s-1)·n`, i.e.
`ex(n; K_{s,t}) ≤ ½ (t-1)^{1/s} n^{2-1/s} + ½(s-1) n` — see `kst_general_edge_bound_rpow`. -/
theorem kst_general_power_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hfree : ¬ HasKst G s t)
    (hL : ((s : ℝ) - 1) * (Fintype.card V) ≤ 2 * (G.edgeFinset.card : ℝ)) :
    (2 * (G.edgeFinset.card : ℝ) - ((s : ℝ) - 1) * (Fintype.card V)) ^ s
      ≤ ((t : ℝ) - 1) * (Fintype.card V : ℝ) ^ (2 * s - 1) := by
  refine kst_analytic_core (fun v => G.degree v) s t hs ht (G.edgeFinset.card : ℝ) ?_ ?_ ?_
  · rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]; push_cast; ring
  · have h := kst_star_count_of_free G s t ht hfree
    calc ∑ v, ((G.degree v).choose s : ℝ)
        = ((∑ v, (G.degree v).choose s : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (((t - 1) * (Fintype.card V).choose s : ℕ) : ℝ) := by exact_mod_cast h
      _ = ((t : ℝ) - 1) * ((Fintype.card V).choose s : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sub ht, Nat.cast_one]
  · linarith [hL]

/-- **General Kővári–Sós–Turán edge bound (classical closed form).**  Taking `s`-th
roots in `kst_general_power_bound` gives the recognisable Kővári–Sós–Turán bound: a
`K_{s,t}`-free graph on `n` vertices with `m` edges (`s ≥ 1`, `t ≥ 1`) satisfies

      2m ≤ (t-1)^{1/s} · n^{2 - 1/s} + (s-1)·n,

i.e. `ex(n; K_{s,t}) ≤ ½ (t-1)^{1/s} n^{2 - 1/s} + ½(s-1) n`.  Unconditional: in the
sparse regime `2m < (s-1)n` the bound is immediate from nonnegativity of the leading
term; otherwise `kst_general_power_bound` supplies `(2m-(s-1)n)^s ≤ (t-1) n^{2s-1}`
and the monotone `s`-th root (`Real.rpow`) extracts the stated inequality
(`((t-1) n^{2s-1})^{1/s} = (t-1)^{1/s} n^{(2s-1)/s} = (t-1)^{1/s} n^{2-1/s}`).

For `s = 2` this reads `2m ≤ (t-1)^{1/2} n^{3/2} + n`, the `√(t-1)·n^{3/2}` leading
order matched by the algebraic solve `kst_edge_bound_leading_order` in the `s = 2` core. -/
theorem kst_general_edge_bound_rpow (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hfree : ¬ HasKst G s t) :
    2 * (G.edgeFinset.card : ℝ)
      ≤ ((t : ℝ) - 1) ^ ((s : ℝ)⁻¹) * (Fintype.card V : ℝ) ^ (2 - (s : ℝ)⁻¹)
        + ((s : ℝ) - 1) * (Fintype.card V) := by
  have hNnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
  have hTnn : (0 : ℝ) ≤ (t : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hrhs : (0 : ℝ) ≤ ((t : ℝ) - 1) ^ ((s : ℝ)⁻¹) * (Fintype.card V : ℝ) ^ (2 - (s : ℝ)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg hTnn _) (Real.rpow_nonneg hNnn _)
  rcases le_or_gt (((s : ℝ) - 1) * (Fintype.card V : ℝ)) (2 * (G.edgeFinset.card : ℝ)) with hL | hL
  · -- main regime `2m ≥ (s-1)n`: take the `s`-th root of the power bound
    have hpow := kst_general_power_bound G s t hs ht hfree hL
    have hLnn : (0 : ℝ) ≤ 2 * (G.edgeFinset.card : ℝ) - ((s : ℝ) - 1) * (Fintype.card V : ℝ) := by
      linarith
    have hcast : ((2 * s - 1 : ℕ) : ℝ) = 2 * (s : ℝ) - 1 := by
      have h2 : 1 ≤ 2 * s := by omega
      rw [Nat.cast_sub h2]; push_cast; ring
    have key : ((Fintype.card V : ℝ) ^ (2 * s - 1)) ^ ((s : ℝ)⁻¹)
        = (Fintype.card V : ℝ) ^ (2 - (s : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast (Fintype.card V : ℝ) (2 * s - 1), ← Real.rpow_mul hNnn]
      congr 1
      rw [hcast]; field_simp
    have hroot : 2 * (G.edgeFinset.card : ℝ) - ((s : ℝ) - 1) * (Fintype.card V : ℝ)
        = ((2 * (G.edgeFinset.card : ℝ) - ((s : ℝ) - 1) * (Fintype.card V : ℝ)) ^ s) ^ ((s : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast hLnn (by omega)).symm
    have hLle : 2 * (G.edgeFinset.card : ℝ) - ((s : ℝ) - 1) * (Fintype.card V : ℝ)
        ≤ ((t : ℝ) - 1) ^ ((s : ℝ)⁻¹) * (Fintype.card V : ℝ) ^ (2 - (s : ℝ)⁻¹) := by
      rw [hroot]
      refine (Real.rpow_le_rpow (by positivity) hpow (by positivity)).trans ?_
      rw [Real.mul_rpow hTnn (by positivity), key]
    linarith [hLle]
  · -- sparse regime `2m < (s-1)n`: bound is immediate
    linarith [hrhs, hL]

/-- **General `K_{s,t}` edge-count bound (`ex` form).**  The `÷2` restatement of
`kst_general_edge_bound_rpow`: a `K_{s,t}`-free graph (`s, t ≥ 1`) on `n` vertices has

      m ≤ ½ (t-1)^{1/s} · n^{2 - 1/s} + ½ (s-1)·n,

the standard `ex(n; K_{s,t}) ≤ …` form of the Kővári–Sós–Turán theorem. -/
theorem kst_general_edge_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hfree : ¬ HasKst G s t) :
    (G.edgeFinset.card : ℝ)
      ≤ ((t : ℝ) - 1) ^ ((s : ℝ)⁻¹) * (Fintype.card V : ℝ) ^ (2 - (s : ℝ)⁻¹) / 2
        + ((s : ℝ) - 1) * (Fintype.card V) / 2 := by
  have h := kst_general_edge_bound_rpow G s t hs ht hfree
  linarith

/-- **Forcing form (general `K_{s,t}`).**  The contrapositive of
`kst_general_edge_bound_rpow`: a graph whose edge count *exceeds* the Kővári–Sós–Turán
bound must contain a `K_{s,t}`.  Concretely, if

      (t-1)^{1/s} · n^{2 - 1/s} + (s-1)·n  <  2m       (`s, t ≥ 1`),

then `HasKst G s t`.  The general-`s` companion of `hasK2t_of_edge_bound_lt` (the `s = 2`
forcing form), making the KST bound a genuine extremal threshold for every `s`. -/
theorem hasKst_of_edge_bound_rpow_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hm : ((t : ℝ) - 1) ^ ((s : ℝ)⁻¹) * (Fintype.card V : ℝ) ^ (2 - (s : ℝ)⁻¹)
        + ((s : ℝ) - 1) * (Fintype.card V) < 2 * (G.edgeFinset.card : ℝ)) :
    HasKst G s t := by
  by_contra hfree
  exact absurd (kst_general_edge_bound_rpow G s t hs ht hfree) (not_le.2 hm)

end GraphLevel

end Erdos1008
