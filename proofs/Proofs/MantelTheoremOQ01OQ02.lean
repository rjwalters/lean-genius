/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A handshake-counting bridge: near-extremal triangle-free graphs have few low-degree vertices

This file formalizes a *stability* step used in the Andrásfai–Erdős–Sós circle of ideas:
if a triangle-free graph on `n` vertices is within `ε n²` edges of the Mantel maximum `n²/4`,
then only `O(ε n)` of its vertices have degree `≤ 2n/5`.

The Andrásfai–Erdős–Sós theorem states that a triangle-free graph with minimum degree
`> 2n/5` is bipartite. Turán-stability arguments frequently need to *pass from an edge-count
hypothesis to a min-degree hypothesis*: a graph with almost `n²/4` edges cannot have many
vertices far below the average degree `n/2`. This file makes that passage precise and fully
machine-checked.

## Proof outline

The argument is a second-moment (Chebyshev) estimate on the degree sequence `d(v)`:

1. **Handshake identity** (`SimpleGraph.sum_degrees_eq_twice_card_edges`):
   `∑ d(v) = 2e`, so the average degree is `2e/n`.

2. **Triangle-free second-moment bound** (`sum_sq_degree_le_card_mul_card_edge`):
   for a triangle-free graph, `∑ d(v)² ≤ n · e`. This is where triangle-freeness enters: for
   an edge `uv` the neighbourhoods `N(u), N(v)` are disjoint, so `d(u) + d(v) ≤ n`; summing
   this over all darts gives `2 ∑ d(v)² ≤ 2 n e`.

3. **Variance bound**: combining (1) and (2), `∑ (d(v) − 2e/n)² ≤ n e − 4e²/n`, and when
   `e ≥ n²/4 − ε n²` the right-hand side is `≤ ε n³`.

4. **Chebyshev counting** (`abstract_low_value_count_le`): any value that is a fixed distance
   below the mean contributes at least that squared distance to the variance, so the number of
   `v` with `d(v) ≤ 2n/5` is `≤ (ε n³) / (n/20)² = 400 ε n`.

The abstract counting step is isolated as a self-contained real-analysis lemma so it can be
reused; the graph-theoretic input is the triangle-free second-moment bound.
-/

open Finset

namespace MantelBridge

/-! ### Step 4 as a standalone lemma: a Chebyshev / second-moment counting bound -/

/-- **Second-moment counting bound.** Let `d : ι → ℝ` be any real-valued function on a finite
index type with `n` elements and total `T = ∑ d i`, hence mean `T / n`. Suppose the sum of
squares is bounded, `∑ (d i)² ≤ Q`. Then for any threshold `m` strictly below the mean, the
number of indices with `d i ≤ m` is controlled by the "variance budget" `Q − T²/n`:

`#{i | d i ≤ m} · (T/n − m)² ≤ Q − T²/n`.

This is Chebyshev's inequality in counting form: values sitting a fixed distance `T/n − m`
below the mean each spend at least `(T/n − m)²` of the total variance, so there cannot be too
many of them. -/
theorem abstract_low_value_count_le {ι : Type*} [Fintype ι] (d : ι → ℝ) (Q : ℝ) (m : ℝ)
    (hn : 0 < Fintype.card ι)
    (hm : m ≤ (∑ i, d i) / Fintype.card ι)
    (hQ : ∑ i, (d i) ^ 2 ≤ Q) :
    (((univ.filter fun i => d i ≤ m).card : ℝ)) * ((∑ i, d i) / Fintype.card ι - m) ^ 2
      ≤ Q - (∑ i, d i) ^ 2 / Fintype.card ι := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn0 : (0 : ℝ) < n := by rw [hn_def]; exact_mod_cast hn
  have hn0' : n ≠ 0 := ne_of_gt hn0
  set T : ℝ := ∑ i, d i with hT_def
  set μ : ℝ := T / n with hμ_def
  set L : Finset ι := univ.filter fun i => d i ≤ m with hL_def
  -- General variance identity for any constant `c`.
  have hgen : ∀ c : ℝ, ∑ i, (d i - c) ^ 2
      = (∑ i, (d i) ^ 2) - 2 * c * T + n * c ^ 2 := by
    intro c
    rw [Finset.sum_congr rfl (fun i _ => (by ring :
      (d i - c) ^ 2 = (d i) ^ 2 - 2 * c * d i + c ^ 2))]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← hn_def, ← hT_def]
  -- Specialize to the mean `μ = T/n`: variance = ∑ d² − T²/n.
  have hvar : ∑ i, (d i - μ) ^ 2 = (∑ i, (d i) ^ 2) - T ^ 2 / n := by
    rw [hgen μ, hμ_def]; field_simp; ring
  -- Variance is bounded by Q − T²/n.
  have hvar_le : ∑ i, (d i - μ) ^ 2 ≤ Q - T ^ 2 / n := by
    rw [hvar]; linarith [hQ]
  -- `m ≤ μ` in the local names.
  have hmμ : m ≤ μ := hm
  -- Each low index contributes at least (μ − m)² to the variance.
  have hlow : (L.card : ℝ) * (μ - m) ^ 2 ≤ ∑ i ∈ L, (d i - μ) ^ 2 := by
    have hterm : ∀ i ∈ L, (μ - m) ^ 2 ≤ (d i - μ) ^ 2 := by
      intro i hi
      have hdi : d i ≤ m := by
        rw [hL_def, mem_filter] at hi; exact hi.2
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - d i)
        (by linarith : (0 : ℝ) ≤ 2 * μ - m - d i)]
    calc (L.card : ℝ) * (μ - m) ^ 2
        = ∑ _i ∈ L, (μ - m) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ L, (d i - μ) ^ 2 := Finset.sum_le_sum hterm
  -- The variance over L is at most the variance over everything.
  have hsub : ∑ i ∈ L, (d i - μ) ^ 2 ≤ ∑ i, (d i - μ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
    intro i _ _; positivity
  -- Chain everything together.
  calc (L.card : ℝ) * (μ - m) ^ 2
      ≤ ∑ i ∈ L, (d i - μ) ^ 2 := hlow
    _ ≤ ∑ i, (d i - μ) ^ 2 := hsub
    _ ≤ Q - T ^ 2 / n := hvar_le

/-! ### Step 2: the triangle-free second-moment bound `∑ d(v)² ≤ n·e` -/

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Adjacent degrees add to at most `n` in a triangle-free graph.** If `u v` are adjacent and
`G` is triangle-free (`K₃`-free), their neighbourhoods are disjoint (a common neighbour would
complete a triangle), so `d(u) + d(v) = #(N(u) ∪ N(v)) ≤ n`. -/
theorem adjacent_degree_add_le (h : G.CliqueFree 3) {u v : V} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card V := by
  classical
  have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [mem_neighborFinset] at hw hw'
    exact h {u, v, w} (by rw [is3Clique_triple_iff]; exact ⟨huv, hw, hw'⟩)
  have hcard : G.degree u + G.degree v = (G.neighborFinset u ∪ G.neighborFinset v).card := by
    rw [Finset.card_union_of_disjoint hdisj, G.card_neighborFinset_eq_degree,
      G.card_neighborFinset_eq_degree]
  rw [hcard]
  exact Finset.card_le_univ _

/-- Summing `d(v)²` over vertices equals summing `d(dart.fst)` over darts, because each vertex
`v` is the tail of exactly `d(v)` darts. -/
theorem sum_degree_fst_eq_sum_sq :
    ∑ x : G.Dart, G.degree x.fst = ∑ v : V, (G.degree v) ^ 2 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
        (t := (Finset.univ : Finset V)) (g := fun x : G.Dart => x.fst)
        (fun x _ => Finset.mem_univ x.fst) (fun x => G.degree x.fst)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have hfib : ∀ x ∈ Finset.univ.filter (fun x : G.Dart => x.fst = v),
      G.degree x.fst = G.degree v := by
    intro x hx; rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    G.dart_fst_fiber_card_eq_degree v, pow_two]

/-- **Triangle-free second-moment bound.** For a triangle-free graph on `n` vertices with `e`
edges, `∑ d(v)² ≤ n · e`. Combined with `∑ d(v) = 2e`, this is the arithmetic engine behind the
`O(εn)` stability estimate. -/
theorem sum_sq_degree_le_card_mul_card_edge (h : G.CliqueFree 3) :
    ∑ v : V, (G.degree v) ^ 2 ≤ Fintype.card V * G.edgeFinset.card := by
  classical
  -- ∑ d(snd) = ∑ d(fst) via the dart-reversal involution.
  have hsnd : ∑ x : G.Dart, G.degree x.snd = ∑ x : G.Dart, G.degree x.fst :=
    Fintype.sum_bijective (SimpleGraph.Dart.symm) (Dart.symm_involutive.bijective)
      (fun x => G.degree x.snd) (fun x => G.degree x.fst) (fun x => by rfl)
  -- 2 ∑ d(v)² = ∑_dart (d(fst) + d(snd)).
  have hdouble : 2 * ∑ v : V, (G.degree v) ^ 2
      = ∑ x : G.Dart, (G.degree x.fst + G.degree x.snd) := by
    rw [Finset.sum_add_distrib, hsnd, sum_degree_fst_eq_sum_sq]; ring
  -- Each dart obeys d(fst) + d(snd) ≤ n.
  have hbound : ∑ x : G.Dart, (G.degree x.fst + G.degree x.snd)
      ≤ ∑ _x : G.Dart, Fintype.card V :=
    Finset.sum_le_sum (fun x _ => adjacent_degree_add_le G h x.adj)
  have hconst : ∑ _x : G.Dart, Fintype.card V
      = 2 * G.edgeFinset.card * Fintype.card V := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, G.dart_card_eq_twice_card_edges]
  -- Combine: 2 ∑ d² ≤ 2 (n e), then cancel the factor of two.
  have hfinal : 2 * ∑ v : V, (G.degree v) ^ 2
      ≤ 2 * (Fintype.card V * G.edgeFinset.card) := by
    rw [hdouble]
    calc ∑ x : G.Dart, (G.degree x.fst + G.degree x.snd)
        ≤ 2 * G.edgeFinset.card * Fintype.card V := hbound.trans_eq hconst
      _ = 2 * (Fintype.card V * G.edgeFinset.card) := by ring
  exact Nat.le_of_mul_le_mul_left hfinal (by norm_num)

/-! ### Main result: near-extremal triangle-free graphs have few low-degree vertices -/

/-- **Handshake-counting bridge (edge count → few low-degree vertices).**

Let `G` be a triangle-free simple graph on `n ≥ 1` vertices, and let `0 ≤ ε ≤ 1/40`. If `G` has
almost the Mantel-maximal number of edges,

`#E(G) ≥ n²/4 − ε n²`,

then only `O(ε n)` vertices can have degree at most `2n/5`:

`#{v | d(v) ≤ 2n/5} ≤ 400 · ε · n`.

In particular, if `ε` is small the graph is "almost min-degree `2n/5`", which is exactly the
hypothesis of the Andrásfai–Erdős–Sós theorem (a triangle-free graph with minimum degree
`> 2n/5` is bipartite). This lemma is the quantitative bridge letting a Turán-stability argument
pass from an *edge-count* hypothesis to a *minimum-degree* hypothesis.

The proof is a second-moment estimate: `∑ d(v) = 2e` (handshake) and, since `G` is triangle-free,
`∑ d(v)² ≤ n e`; hence the degree variance is at most `ε n³`, and any vertex with degree
`≤ 2n/5 = mean − Ω(n)` spends `Ω(n²)` of that variance. -/
theorem low_degree_count_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 40)
    (hn : 0 < Fintype.card V)
    (hedge : (Fintype.card V : ℝ) ^ 2 / 4 - ε * (Fintype.card V : ℝ) ^ 2
      ≤ (G.edgeFinset.card : ℝ)) :
    ((univ.filter fun v => (G.degree v : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 5).card : ℝ)
      ≤ 400 * ε * (Fintype.card V : ℝ) := by
  classical
  set nR : ℝ := (Fintype.card V : ℝ) with hnR
  set eR : ℝ := (G.edgeFinset.card : ℝ) with heR
  have hn0 : (0 : ℝ) < nR := by rw [hnR]; exact_mod_cast hn
  have heR0 : (0 : ℝ) ≤ eR := by rw [heR]; positivity
  -- Handshake identity as reals.
  have hT : ∑ v, (G.degree v : ℝ) = 2 * eR := by
    rw [heR, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]; push_cast; ring
  -- Triangle-free second moment as reals.
  have hQ : ∑ v, (G.degree v : ℝ) ^ 2 ≤ nR * eR := by
    have hnat := sum_sq_degree_le_card_mul_card_edge G h
    have hcast : ∑ v, (G.degree v : ℝ) ^ 2 = ((∑ v, (G.degree v) ^ 2 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast, hnR, heR]; exact_mod_cast hnat
  -- Cauchy–Schwarz gives Mantel's bound `4e ≤ n²`.
  have hCS : (∑ v, (G.degree v : ℝ)) ^ 2 ≤ nR * ∑ v, (G.degree v : ℝ) ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V))
      (f := fun v => (G.degree v : ℝ))
    rw [Finset.card_univ] at hcs
    rw [hnR]; exact_mod_cast hcs
  have hchain : 4 * eR ^ 2 ≤ nR ^ 2 * eR := by
    have h1 : (∑ v, (G.degree v : ℝ)) ^ 2 = 4 * eR ^ 2 := by rw [hT]; ring
    nlinarith [hCS, hQ, hn0, heR0, h1]
  have hMantel : 4 * eR ≤ nR ^ 2 := by
    rcases eq_or_lt_of_le heR0 with h0 | hpos
    · nlinarith [hn0, h0]
    · nlinarith [hchain, hpos]
  -- `m = 2n/5` sits at or below the mean `2e/n`.
  have h2e : nR / 2 - 2 * ε * nR ≤ 2 * eR / nR := by
    rw [le_div_iff₀ hn0]; nlinarith [hedge, hn0]
  have hgap1 : nR / 20 ≤ 2 * eR / nR - 2 * nR / 5 := by
    nlinarith [h2e, mul_le_mul_of_nonneg_right hε hn0.le, hε0, hn0]
  have hmμ : 2 * nR / 5 ≤ (∑ v, (G.degree v : ℝ)) / nR := by rw [hT]; linarith [hgap1]
  -- Apply the abstract Chebyshev counting bound.
  have habs := abstract_low_value_count_le (fun v => (G.degree v : ℝ)) (nR * eR) (2 * nR / 5)
    hn hmμ hQ
  rw [hT, ← hnR] at habs
  set C : ℝ := ((univ.filter fun v => (G.degree v : ℝ) ≤ 2 * nR / 5).card : ℝ) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  -- Lower-bound the squared gap.
  have hgapsq : (nR / 20) ^ 2 ≤ (2 * eR / nR - 2 * nR / 5) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hgap1 2
  -- Upper-bound the variance budget by `ε n³`.
  have hii : nR * eR - (2 * eR) ^ 2 / nR ≤ ε * nR ^ 3 := by
    have hLHS : nR * eR - (2 * eR) ^ 2 / nR = (nR ^ 2 * eR - 4 * eR ^ 2) / nR := by
      field_simp; ring
    rw [hLHS, div_le_iff₀ hn0]
    nlinarith [mul_nonneg heR0 (by linarith [hedge, hMantel] :
        (0 : ℝ) ≤ 4 * ε * nR ^ 2 - (nR ^ 2 - 4 * eR)),
      mul_nonneg (mul_nonneg hε0 (sq_nonneg nR)) (by linarith [hMantel] :
        (0 : ℝ) ≤ nR ^ 2 - 4 * eR)]
  -- Chain: C · (n/20)² ≤ C · gap² ≤ variance ≤ ε n³.
  have hchain2 : C * (nR / 20) ^ 2 ≤ ε * nR ^ 3 :=
    le_trans (mul_le_mul_of_nonneg_left hgapsq hC0) (le_trans habs hii)
  -- Cancel `n²` to conclude `C ≤ 400 ε n`.
  have hfinal : C * nR ^ 2 ≤ (400 * ε * nR) * nR ^ 2 := by nlinarith [hchain2, hn0]
  exact le_of_mul_le_mul_right hfinal (by positivity)

end MantelBridge
