/-
  Erdős Problem #1020: The Erdős Matching Conjecture

  Source: https://erdosproblems.com/1020
  Status: OPEN

  Statement:
  Let f(n; r, k) be the maximum number of edges in an r-uniform hypergraph
  which contains no set of k independent (pairwise disjoint) edges.

  Conjecture: For all r ≥ 3,
    f(n; r, k) = max(C(rk-1, r), C(n, r) - C(n-k+1, r))

  Background:
  This is one of the most important open problems in extremal hypergraph theory.
  The conjecture predicts the exact threshold for avoiding a matching of size k.
  Two constructions achieve the conjectured bound:
  - All r-edges on rk-1 vertices (too few vertices for k disjoint edges)
  - All edges meeting a fixed (k-1)-set (any k edges share a vertex)

  Known results:
  • r = 2: Solved by Erdős-Gallai (1959)
  • r = 3: Solved by Łuczak-Mieczkowska (2014)
  • Small n: Kleitman (n = kr), Frankl (n ≤ kr + kr/(2r^{2r+1}))
  • Large n: Huang-Loh-Sudakov (n ≥ 3kr²)
  • Upper bound: f(n; r, k) ≤ (k-1)·C(n-1, r-1) (Frankl 1987)

  References:
  [ErGa59] Erdős-Gallai, "On maximal paths and circuits" (1959)
  [Fr87] Frankl, "The shifting technique in extremal set theory" (1987)
  [HLS12] Huang-Loh-Sudakov, "The size of a hypergraph and its matching number" (2012)
  [LM14] Łuczak-Mieczkowska, "On Erdős' matching conjecture" (2014)

  Tags: hypergraph-theory, matching, extremal-combinatorics, open-problem
-/

import Mathlib

open Finset Nat

/-
## Hypergraph Basics

r-uniform hypergraphs and matchings.
-/

/-- An r-uniform hypergraph on vertex set V -/
structure Hypergraph (V : Type*) (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Two edges are disjoint (independent) -/
def EdgesDisjoint (e₁ e₂ : Finset V) : Prop := Disjoint e₁ e₂

/-- A matching is a set of pairwise disjoint edges -/
def IsMatching {r : ℕ} (H : Hypergraph V r) (M : Finset (Finset V)) : Prop :=
  M ⊆ H.edges ∧ ∀ e₁ e₂ : Finset V, e₁ ∈ M → e₂ ∈ M → e₁ ≠ e₂ → EdgesDisjoint e₁ e₂

/-- The matching number: size of largest matching -/
noncomputable def matchingNumber {r : ℕ} (H : Hypergraph V r) : ℕ :=
  sSup {k : ℕ | ∃ M : Finset (Finset V), IsMatching H M ∧ M.card = k}

/-- Hypergraph has no k-matching -/
def HasNoKMatching {r : ℕ} (H : Hypergraph V r) (k : ℕ) : Prop :=
  matchingNumber H < k

/-
## The Function f(n; r, k)

Maximum edges in r-uniform hypergraph on n vertices with no k-matching.
-/

/-- f(n; r, k): maximum edges avoiding k independent edges -/
noncomputable def f (n r k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n ∧
    ∃ H : Hypergraph V r, H.edges.card = m ∧ HasNoKMatching H k}

/-
## The Conjectured Formula

Two extremal constructions give the conjectured value.
-/

/-- Construction 1: All r-edges on rk-1 vertices -/
def construction1 (r k : ℕ) : ℕ := Nat.choose (r * k - 1) r

/-- Construction 2: All edges meeting a fixed (k-1)-set -/
def construction2 (n r k : ℕ) : ℕ := Nat.choose n r - Nat.choose (n - k + 1) r

/-- The conjectured value of f(n; r, k) -/
def conjecturedValue (n r k : ℕ) : ℕ := max (construction1 r k) (construction2 n r k)

/-- The Erdős Matching Conjecture -/
def erdosMatchingConjecture : Prop :=
  ∀ r ≥ 3, ∀ n k : ℕ, k ≥ 1 → n ≥ r * k →
    f n r k = conjecturedValue n r k

/-
## The Case r = 2 (Graphs)

Erdős-Gallai solved this completely.
-/

/-- For graphs (r = 2), f(n; 2, k) is known -/
axiom erdos_gallai_graphs :
  ∀ n k : ℕ, k ≥ 1 → n ≥ 2 * k →
    f n 2 k = max (Nat.choose (2 * k - 1) 2) (Nat.choose n 2 - Nat.choose (n - k + 1) 2)

/-- Explicit formula for r = 2: C(2k-1,2) = (k-1)(2k-1) and
    C(n,2) - C(n-k+1,2) = (k-1)(2n-k)/2. -/
theorem f_2_explicit (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 2 * k) :
    f n 2 k = max ((k - 1) * (2 * k - 1)) ((k - 1) * (2 * n - k) / 2) := by
  have h := erdos_gallai_graphs n k hk hn
  rw [h]
  congr 1
  · -- C(2k-1, 2) = (k-1)(2k-1) = (2k-1)(2k-2)/2
    rw [Nat.choose_two_right]
    omega
  · -- C(n,2) - C(n-k+1,2) = (k-1)(2n-k)/2
    rw [Nat.choose_two_right, Nat.choose_two_right]
    omega

/-
## The Case r = 3 (3-uniform Hypergraphs)

Łuczak-Mieczkowska (2014) proved the conjecture for r = 3.
-/

/-- The conjecture holds for r = 3 (Łuczak-Mieczkowska 2014) -/
axiom luczak_mieczkowska :
  ∀ n k : ℕ, k ≥ 1 → n ≥ 3 * k →
    f n 3 k = conjecturedValue n 3 k

/-
## Partial Results

Known cases where the conjecture is verified.
-/

/-- Kleitman's result: conjecture holds when n = rk -/
axiom kleitman_exact :
  ∀ r k : ℕ, r ≥ 2 → k ≥ 1 →
    f (r * k) r k = construction1 r k

/-- Huang-Loh-Sudakov: conjecture holds for n ≥ 3kr² -/
axiom huang_loh_sudakov :
  ∀ r k : ℕ, r ≥ 3 → k ≥ 1 →
    ∀ n ≥ 3 * k * r^2, f n r k = conjecturedValue n r k

/-- Frankl's small n result -/
axiom frankl_small_n :
  ∀ r k : ℕ, r ≥ 3 → k ≥ 1 →
    ∀ n : ℕ, r * k ≤ n → n ≤ r * k + k / (2 * r^(2*r + 1)) →
    f n r k = construction1 r k

/-
## Upper Bounds

Frankl's celebrated upper bound.
-/

/-- Frankl's upper bound (1987): f(n; r, k) ≤ (k-1)·C(n-1, r-1) -/
axiom frankl_upper_bound :
  ∀ n r k : ℕ, r ≥ 2 → k ≥ 1 → n ≥ r →
    f n r k ≤ (k - 1) * Nat.choose (n - 1) (r - 1)

/-- The upper bound is sometimes tight.
    Proof: By induction on k. Base k=1: both sides are 0.
    Step k→k+1: decompose C(n,r)-C(n-k,r) = [C(n,r)-C(n-k+1,r)] + [C(n-k+1,r)-C(n-k,r)].
    First part ≤ (k-1)·C(n-1,r-1) by IH. Second part = C(n-k,r-1) by Pascal ≤ C(n-1,r-1). -/
theorem upper_bound_tight_construction2 (n r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 1) (hn : n ≥ r * k) :
    construction2 n r k ≤ (k - 1) * Nat.choose (n - 1) (r - 1) := by
  unfold construction2
  revert hk hn
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _ hn
    cases k with
    | zero =>
      -- k+1 = 1: C(n,r) - C(n,r) = 0 ≤ 0
      have h : n - (0 + 1) + 1 = n := by omega
      rw [h]; simp
    | succ k' =>
      -- k+1 = k'+2; IH for k'+1
      have hk'1 : k' + 1 ≥ 1 := by omega
      have hn' : n ≥ r * (k' + 1) := by nlinarith
      specialize ih hk'1 hn'
      -- Simplify index expressions
      have h1 : n - (k' + 1) + 1 = n - k' := by omega
      have h2 : n - (k' + 1 + 1) + 1 = n - k' - 1 := by omega
      rw [h1] at ih; rw [h2]
      -- ih: C(n,r) - C(n-k',r) ≤ k' * C(n-1,r-1)
      -- Goal: C(n,r) - C(n-k'-1,r) ≤ (k'+1) * C(n-1,r-1)
      -- Decompose: a - c = (a - b) + (b - c) for c ≤ b ≤ a
      have hle1 : Nat.choose (n - k' - 1) r ≤ Nat.choose (n - k') r :=
        Nat.choose_le_choose r (by omega)
      have hle2 : Nat.choose (n - k') r ≤ Nat.choose n r :=
        Nat.choose_le_choose r (by omega)
      have h_split : Nat.choose n r - Nat.choose (n - k' - 1) r =
          (Nat.choose n r - Nat.choose (n - k') r) +
          (Nat.choose (n - k') r - Nat.choose (n - k' - 1) r) := by omega
      rw [h_split]
      -- Pascal: C(m+1,r) - C(m,r) = C(m,r-1)  where m = n-k'-1
      have h_pascal : Nat.choose (n - k') r - Nat.choose (n - k' - 1) r =
          Nat.choose (n - k' - 1) (r - 1) := by
        have hCSS := Nat.choose_succ_succ (n - k' - 1) (r - 1)
        rw [show (n - k' - 1) + 1 = n - k' from by omega,
            show (r - 1) + 1 = r from by omega] at hCSS
        omega
      rw [h_pascal]
      -- Monotonicity: C(n-k'-1, r-1) ≤ C(n-1, r-1)
      have h_mono : Nat.choose (n - k' - 1) (r - 1) ≤ Nat.choose (n - 1) (r - 1) :=
        Nat.choose_le_choose (r - 1) (by omega)
      -- Combine: IH + monotonicity
      calc (Nat.choose n r - Nat.choose (n - k') r) + Nat.choose (n - k' - 1) (r - 1)
          ≤ k' * Nat.choose (n - 1) (r - 1) + Nat.choose (n - 1) (r - 1) := by linarith
        _ = (k' + 1) * Nat.choose (n - 1) (r - 1) := by ring

/-
## Lower Bounds

The constructions give lower bounds.
-/

/-- Construction 1 gives a lower bound -/
axiom construction1_lower :
  ∀ n r k : ℕ, r ≥ 2 → k ≥ 1 → n ≥ r * k - 1 →
    f n r k ≥ construction1 r k

/-- Construction 2 gives a lower bound -/
axiom construction2_lower :
  ∀ n r k : ℕ, r ≥ 2 → k ≥ 1 → n ≥ r →
    f n r k ≥ construction2 n r k

/-- Combined lower bound -/
theorem combined_lower_bound (n r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 1) (hn : n ≥ r * k) :
    f n r k ≥ conjecturedValue n r k := by
  unfold conjecturedValue
  have h1 := construction1_lower n r k hr hk (by omega)
  have h2 := construction2_lower n r k hr hk (by omega)
  exact le_max_iff.mpr (Or.inl h1)

/-
## Monotonicity
-/

/-- f is increasing in n -/
axiom f_mono_n :
  ∀ n₁ n₂ r k : ℕ, n₁ ≤ n₂ → f n₁ r k ≤ f n₂ r k

/-- f is increasing in k -/
axiom f_mono_k :
  ∀ n r k₁ k₂ : ℕ, k₁ ≤ k₂ → f n r k₁ ≤ f n r k₂

/-
## Asymptotic Behavior

For large n, the second construction dominates.
-/

/-- For large n, construction2 > construction1 -/
theorem large_n_construction2_dominates (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 1) :
    ∃ N : ℕ, ∀ n ≥ N, construction2 n r k > construction1 r k := by
  -- construction2 n r k = C(n,r) - C(n-k+1,r) grows without bound
  -- construction1 r k = C(rk-1, r) is a fixed constant
  -- For k=1: c1 = C(r-1,r) = 0, so any n with C(n,r) > C(n,r) = 0 works trivially
  -- For k≥2: by Pascal telescoping, construction2 n r k ≥ C(n-1,r-1) ≥ n-1 → ∞
  set c1 := construction1 r k
  -- Use N = c1 + k + r as threshold
  refine ⟨c1 + k + r, fun n hn => ?_⟩
  unfold construction2
  by_cases hk1 : k = 1
  · -- k = 1: c1 = C(r*1-1, r) = C(r-1, r) = 0
    subst hk1
    simp only [construction1, Nat.mul_one] at c1 hn ⊢
    have : c1 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [this] at hn ⊢
    simp only [Nat.zero_add] at hn
    rw [show n - 1 + 1 = n from by omega, Nat.sub_self]
    exact Nat.choose_pos (by omega)
  · -- k ≥ 2
    have hk2 : k ≥ 2 := by omega
    -- By Pascal: C(n,r) = C(n-1,r) + C(n-1,r-1)
    -- So C(n,r) - C(n-1,r) = C(n-1,r-1)
    -- And C(n-k+1,r) ≤ C(n-1,r) since n-k+1 ≤ n-1
    have h1 : Nat.choose (n - k + 1) r ≤ Nat.choose (n - 1) r :=
      Nat.choose_le_choose r (by omega)
    have h2 : Nat.choose n r = Nat.choose (n - 1) r + Nat.choose (n - 1) (r - 1) := by
      have := Nat.choose_succ_succ (n - 1) (r - 1)
      rw [show n - 1 + 1 = n from by omega, show r - 1 + 1 = r from by omega] at this
      omega
    -- So construction2 n r k ≥ C(n-1,r-1)
    have h3 : Nat.choose n r - Nat.choose (n - k + 1) r ≥ Nat.choose (n - 1) (r - 1) := by omega
    -- C(n-1, r-1) ≥ n-1 when r-1 ≥ 1 (since C(m,s) ≥ C(m,1) = m for 1 ≤ s ≤ m-1)
    -- Actually: C(m, 1) = m and C(m, s) ≥ C(m, 1) when s ≤ m/2 or by direct bound
    -- Simpler: C(n-1, r-1) ≥ (n-1) since r-1 ≥ 1 and for s=1, C(m,1)=m, and C(m,s)≥C(m,1)
    -- for s ≤ m-s, i.e., 2s ≤ m. We have r-1 ≥ 1, n-1 ≥ c1+k+r-1 ≥ 2(r-1) for large enough.
    -- But we just need C(n-1, r-1) > c1, and n-1 ≥ c1 + k + r - 1 ≥ c1 + 2 + 2 - 1 = c1+3.
    -- Use: C(m, s) ≥ m for m ≥ 2s-1 and s ≥ 1 (since C(m,s) ≥ C(m,1)=m when s ≤ m/2+1)
    -- Here m = n-1 ≥ c1+k+r-1, s = r-1 ≥ 1.
    -- For m ≥ 2(r-1): C(m, r-1) ≥ C(m, 1) = m ≥ c1+k+r-1 > c1.
    suffices Nat.choose (n - 1) (r - 1) > c1 by omega
    have hm : n - 1 ≥ c1 + k + r - 1 := by omega
    -- We need: n-1 ≥ 2*(r-1) for C(n-1,r-1) ≥ C(n-1,1) = n-1 > c1
    -- n-1 ≥ c1+k+r-1 ≥ 0+2+2-1 = 3 ≥ 2*(2-1) = 2 when r=2
    -- n-1 ≥ c1+k+r-1 ≥ 2(r-1) when c1+k ≥ r-1, which holds since k ≥ 2 and r ≥ 2.
    have hm2 : n - 1 ≥ 2 * (r - 1) := by omega
    -- For m ≥ 2s where s ≥ 1: C(m, s) ≥ m
    -- Proof: C(m, s) ≥ C(m, 1) = m when 1 ≤ s ≤ m-1 and s ≤ (m+1)/2
    -- Since m ≥ 2s, we have s ≤ m/2, so C(m,s) ≥ C(m,1) = m
    calc Nat.choose (n - 1) (r - 1)
        ≥ n - 1 := by
          rw [show n - 1 = Nat.choose (n - 1) 1 from (Nat.choose_one_right (n - 1)).symm]
          exact Nat.choose_anti (n - 1) (by omega) (by omega)
      _ > c1 := by omega

/-- Asymptotic: f(n; r, k) ~ (k-1)·n^{r-1}/(r-1)! as n → ∞ -/
axiom f_asymptotic :
  ∀ r k : ℕ, r ≥ 2 → k ≥ 1 →
    Filter.Tendsto (fun n => (f n r k : ℝ) / ((k - 1 : ℝ) * n^(r - 1) / (r - 1).factorial))
      Filter.atTop (nhds 1)

/-
## The Open Problem

The conjecture remains open for r ≥ 4.
-/

/-- The main open question: is the conjecture true for all r? -/
def erdos1020OpenProblem : Prop := erdosMatchingConjecture

/-- Specific open case: r = 4 -/
def r4Conjecture : Prop :=
  ∀ n k : ℕ, k ≥ 1 → n ≥ 4 * k →
    f n 4 k = conjecturedValue n 4 k

#check f
#check conjecturedValue
#check erdosMatchingConjecture
#check frankl_upper_bound
#check luczak_mieczkowska
#check huang_loh_sudakov
