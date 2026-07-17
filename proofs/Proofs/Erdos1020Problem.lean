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

/-- An r-uniform hypergraph on vertex set V.
    (Named `RUniformHypergraph` to avoid clashing with Mathlib's
    `Hypergraph` structure introduced in Mathlib.Combinatorics.Hypergraph.Basic.) -/
structure RUniformHypergraph (V : Type*) (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Two edges are disjoint (independent) -/
def EdgesDisjoint (e₁ e₂ : Finset V) : Prop := Disjoint e₁ e₂

/-- A matching is a set of pairwise disjoint edges -/
def IsMatching {r : ℕ} (H : RUniformHypergraph V r) (M : Finset (Finset V)) : Prop :=
  M ⊆ H.edges ∧ ∀ e₁ e₂ : Finset V, e₁ ∈ M → e₂ ∈ M → e₁ ≠ e₂ → EdgesDisjoint e₁ e₂

/-- The matching number: size of largest matching -/
noncomputable def matchingNumber {r : ℕ} (H : RUniformHypergraph V r) : ℕ :=
  sSup {k : ℕ | ∃ M : Finset (Finset V), IsMatching H M ∧ M.card = k}

/-- Hypergraph has no k-matching -/
def HasNoKMatching {r : ℕ} (H : RUniformHypergraph V r) (k : ℕ) : Prop :=
  matchingNumber H < k

/-
## The Function f(n; r, k)

Maximum edges in r-uniform hypergraph on n vertices with no k-matching.
-/

/-- f(n; r, k): maximum edges avoiding k independent edges -/
noncomputable def f (n r k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (_ : DecidableEq V) (_ : Fintype V),
    Fintype.card V = n ∧
    ∃ H : RUniformHypergraph V r, H.edges.card = m ∧ HasNoKMatching H k}

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
  -- `n.choose 2` doubles to the exact product `n * (n - 1)`; this lets `omega`
  -- reason about the `/2` terms below as exact (not floor) division.
  have key : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1) := fun m => by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
  congr 1
  · -- C(2k-1, 2) = (k-1)(2k-1) = (2k-1)(2k-2)/2
    rw [Nat.choose_two_right, show 2 * k - 1 - 1 = 2 * (k - 1) from by omega,
        show (2 * k - 1) * (2 * (k - 1)) = 2 * ((k - 1) * (2 * k - 1)) from by ring,
        Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
  · -- C(n,2) - C(n-k+1,2) = (k-1)(2n-k)/2
    obtain ⟨a, rfl⟩ : ∃ a, n = a + k := ⟨n - k, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e1 : a + (k' + 1) - (k' + 1) + 1 = a + 1 := by omega
    have e2 : a + (k' + 1) - 1 = a + k' := by omega
    have e3 : 2 * (a + (k' + 1)) - (k' + 1) = a + (a + (k' + 1)) := by omega
    have e4 : k' + 1 - 1 = k' := by omega
    have e5 : a + 1 - 1 = a := by omega
    have hka := key (a + (k' + 1))
    have ha1 := key (a + 1)
    rw [e2] at hka
    rw [e5] at ha1
    have hpoly : (a + (k' + 1)) * (a + k') = (a + 1) * a + k' * (a + (a + (k' + 1))) := by ring
    rw [e1, e4, e3]
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

/-  Kleitman's result: conjecture holds when n = rk -/
/-- Huang-Loh-Sudakov: conjecture holds for n ≥ 3kr² -/
axiom huang_loh_sudakov :
  ∀ r k : ℕ, r ≥ 3 → k ≥ 1 →
    ∀ n ≥ 3 * k * r^2, f n r k = conjecturedValue n r k

/-  Frankl's small n result -/
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
      -- (k'+1-1) is definitionally k', but not syntactically -- normalize `ih` so later
      -- arithmetic tactics see matching atoms.
      have e0 : k' + 1 - 1 = k' := by omega
      rw [e0] at ih
      -- n ≥ k'+2 (from n ≥ r*(k'+2) and r ≥ 2), needed for the subtraction identities below.
      have hnk : n ≥ k' + 1 + 1 := by nlinarith
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
        have hCSS := Nat.choose_succ_succ' (n - k' - 1) (r - 1)
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
  have h2 := construction2_lower n r k hr hk (by nlinarith)
  exact max_le h1 h2

/-
## Monotonicity
-/

/-  f is increasing in n -/
/-  f is increasing in k -/
/-
## Asymptotic Behavior

For large n, the second construction dominates.
-/

/-- For large n, construction2 > construction1.
    NOTE (migration v4.31, epic #37508 / #38611 candidate): the original statement quantified
    over `k ≥ 1`, but at `k = 1` BOTH sides are identically `0` for every `n`
    (`construction2 n r 1 = C(n,r) - C(n,r) = 0` and `construction1 r 1 = C(r-1,r) = 0`), so the
    strict-dominance claim `0 > 0` is false there -- it is not "trivial", it is unprovable. The
    old (v4.26) proof's `k = 1` branch reduced to exactly this false goal; restricting to `k ≥ 2`
    (the case Pascal-telescoping genuinely proves) is the honest fix. -/
theorem large_n_construction2_dominates (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∃ N : ℕ, ∀ n ≥ N, construction2 n r k > construction1 r k := by
  -- construction2 n r k = C(n,r) - C(n-k+1,r) grows without bound
  -- construction1 r k = C(rk-1, r) is a fixed constant
  -- By Pascal telescoping, construction2 n r k ≥ C(n-1,r-1) ≥ n-1 → ∞
  set c1 := construction1 r k
  -- Use N = c1 + 2r + k as threshold (large enough that r-1 ≤ (n-1)/2 too)
  refine ⟨c1 + 2 * r + k, fun n hn => ?_⟩
  unfold construction2
  -- By Pascal: C(n,r) = C(n-1,r) + C(n-1,r-1)
  -- So C(n,r) - C(n-1,r) = C(n-1,r-1)
  -- And C(n-k+1,r) ≤ C(n-1,r) since n-k+1 ≤ n-1
  have h1 : Nat.choose (n - k + 1) r ≤ Nat.choose (n - 1) r :=
    Nat.choose_le_choose r (by omega)
  have h2 : Nat.choose n r = Nat.choose (n - 1) r + Nat.choose (n - 1) (r - 1) := by
    have hCSS := Nat.choose_succ_succ' (n - 1) (r - 1)
    rw [show n - 1 + 1 = n from by omega, show r - 1 + 1 = r from by omega] at hCSS
    omega
  -- So construction2 n r k ≥ C(n-1,r-1)
  have h3 : Nat.choose n r - Nat.choose (n - k + 1) r ≥ Nat.choose (n - 1) (r - 1) := by omega
  suffices Nat.choose (n - 1) (r - 1) > c1 by omega
  -- C(n-1, r-1) ≥ C(n-1, 1) = n-1, since binomial coefficients are increasing in the bottom
  -- argument up through the midpoint, and r-1 ≤ (n-1)/2 here.
  have step : ∀ j, 1 ≤ j → j ≤ (n - 1) / 2 → Nat.choose (n - 1) 1 ≤ Nat.choose (n - 1) j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ j hj ih =>
      intro hjm
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  have hmid : Nat.choose (n - 1) 1 ≤ Nat.choose (n - 1) (r - 1) :=
    step (r - 1) (by omega) (by omega)
  rw [Nat.choose_one_right] at hmid
  omega

/-  Asymptotic: f(n; r, k) ~ (k-1)·n^{r-1}/(r-1)! as n → ∞ -/
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
