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

/-- Pascal's rule as subtraction: C(m+1, s+1) - C(m, s+1) = C(m, s). -/
private theorem choose_succ_sub (m s : ℕ) :
    Nat.choose (m + 1) (s + 1) - Nat.choose m (s + 1) = Nat.choose m s := by
  have h := Nat.choose_succ_succ m s; omega

/-- Telescoping bound: C(n, r+1) - C(n-j, r+1) ≤ j * C(n-1, r) for j ≤ n.
    Proof by induction on j, using Pascal's rule and monotonicity. -/
private theorem choose_diff_le_mul (n r : ℕ) :
    ∀ j, j ≤ n →
      Nat.choose n (r + 1) - Nat.choose (n - j) (r + 1) ≤ j * Nat.choose (n - 1) r := by
  intro j
  induction j with
  | zero => simp
  | succ m ih =>
    intro hj
    have hm : m ≤ n := by omega
    -- Split: C(n,r+1) - C(n-(m+1),r+1) = [C(n,r+1) - C(n-m,r+1)] + [C(n-m,r+1) - C(n-(m+1),r+1)]
    have hle1 : Nat.choose (n - (m + 1)) (r + 1) ≤ Nat.choose (n - m) (r + 1) :=
      Nat.choose_le_choose (r + 1) (by omega)
    have hle2 : Nat.choose (n - m) (r + 1) ≤ Nat.choose n (r + 1) :=
      Nat.choose_le_choose (r + 1) (by omega)
    have h_split : Nat.choose n (r + 1) - Nat.choose (n - (m + 1)) (r + 1) =
        (Nat.choose n (r + 1) - Nat.choose (n - m) (r + 1)) +
        (Nat.choose (n - m) (r + 1) - Nat.choose (n - (m + 1)) (r + 1)) := by omega
    rw [h_split]
    -- Bound the second part by Pascal: C(n-m, r+1) - C(n-m-1, r+1) = C(n-m-1, r)
    have h_eq : n - (m + 1) = n - m - 1 := by omega
    have h_nm_pos : n - m ≥ 1 := by omega
    have h_rewrite : n - m = (n - m - 1) + 1 := by omega
    have h_pascal : Nat.choose (n - m) (r + 1) - Nat.choose (n - (m + 1)) (r + 1) =
        Nat.choose (n - m - 1) r := by
      rw [h_eq]; conv_lhs => rw [h_rewrite]; exact choose_succ_sub (n - m - 1) r
    rw [h_pascal]
    -- Bound: C(n-m-1, r) ≤ C(n-1, r) by monotonicity
    have h_mono : Nat.choose (n - m - 1) r ≤ Nat.choose (n - 1) r :=
      Nat.choose_le_choose r (by omega)
    -- Combine: ≤ m * C(n-1, r) + C(n-1, r) = (m+1) * C(n-1, r)
    calc (Nat.choose n (r + 1) - Nat.choose (n - m) (r + 1)) + Nat.choose (n - m - 1) r
        ≤ m * Nat.choose (n - 1) r + Nat.choose (n - 1) r :=
          Nat.add_le_add (ih hm) h_mono
      _ = (m + 1) * Nat.choose (n - 1) r := by ring

/-- The upper bound is sometimes tight.
    By telescoping, C(n,r) - C(n-k+1,r) = Σ_{i=1}^{k-1} C(n-i,r-1)
    via Pascal's rule. Each term ≤ C(n-1,r-1) by monotonicity, giving ≤ (k-1)·C(n-1,r-1). -/
theorem upper_bound_tight_construction2 (n r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 1) (hn : n ≥ r * k) :
    construction2 n r k ≤ (k - 1) * Nat.choose (n - 1) (r - 1) := by
  unfold construction2
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [show k' + 1 - 1 = k' from rfl, show r' + 1 - 1 = r' from rfl]
  have : n - (k' + 1) + 1 = n - k' := by omega
  rw [this]
  exact choose_diff_le_mul n r' k' (by omega)

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
  sorry

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
