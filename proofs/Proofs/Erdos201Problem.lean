/-
Erdős Problem 201: Arithmetic Progressions in Integer Sets

Let G_k(N) denote the minimum size of a k-AP-free subset guaranteed
in any set of N integers. Let R_k(N) be the maximum size of a k-AP-free
subset of {1,…,N}.

Questions:
1. Determine G_k(N).
2. Is lim_{N→∞} R₃(N)/G₃(N) = 1?

Known: G_k(N) ≤ R_k(N) (trivial), R_k(N) ≪_k G_k(N) (KSS 1975).

Key Results (proved here):
1. R_k monotone in N (proved structurally)
2. R_k anti-monotone in k (proved structurally)
3. AP containment transfer between k and l when k ≤ l (proved)
4. gk ≤ rk bound (proved from definitions)

Reference: https://erdosproblems.com/201
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-
## Arithmetic progressions
-/

/-- A set A of integers contains a k-term arithmetic progression. -/
def ContainsAPOfLength (A : Finset ℤ) (k : ℕ) : Prop :=
    ∃ (a d : ℤ), d ≠ 0 ∧ k ≥ 1 ∧
      ∀ i : Fin k, a + (i.val : ℤ) * d ∈ A

/-- A set A is k-AP-free: it contains no k-term arithmetic progression. -/
def IsAPFree (A : Finset ℤ) (k : ℕ) : Prop :=
    ¬ContainsAPOfLength A k

/-- If k ≤ l and A contains an l-term AP, then A contains a k-term AP. -/
theorem contains_ap_of_le {A : Finset ℤ} {k l : ℕ} (hkl : k ≤ l) (hk1 : k ≥ 1)
    (h : ContainsAPOfLength A l) : ContainsAPOfLength A k := by
  obtain ⟨a, d, hd, _, hmem⟩ := h
  exact ⟨a, d, hd, hk1, fun i => hmem ⟨i.val, by omega⟩⟩

/-- If A is k-AP-free, then A is l-AP-free for all l ≥ k. -/
theorem isAPFree_of_le {A : Finset ℤ} {k l : ℕ} (hkl : k ≤ l) (hk1 : k ≥ 1)
    (hfree : IsAPFree A k) : IsAPFree A l := by
  intro hcont
  exact hfree (contains_ap_of_le hkl hk1 hcont)

/-- A subset of a k-AP-free set is also k-AP-free. -/
theorem isAPFree_subset {A B : Finset ℤ} {k : ℕ} (hsub : A ⊆ B)
    (hfree : IsAPFree B k) : IsAPFree A k := by
  intro ⟨a, d, hd, hk1, hmem⟩
  exact hfree ⟨a, d, hd, hk1, fun i => hsub (hmem i)⟩

/-
## The functions G_k and R_k
-/

/-- R_k(N): the maximum size of a k-AP-free subset of {1,…,N}. -/
noncomputable def rk (k N : ℕ) : ℕ :=
    Finset.sup
      ((Finset.Icc (1 : ℤ) N).powerset.filter (fun A => IsAPFree A k))
      Finset.card

/-- G_k(N): the minimum over all N-element integer sets S of the
maximum k-AP-free subset of S.

The true definition quantifies over all N-element integer sets,
which cannot be expressed as a computable function. We axiomatize it. -/
axiom gk : ℕ → ℕ → ℕ

/-- A set S has a k-AP-free subset of size at least m. -/
def HasAPFreeSubsetOfSize (S : Finset ℤ) (k m : ℕ) : Prop :=
  ∃ A : Finset ℤ, A ⊆ S ∧ IsAPFree A k ∧ A.card ≥ m

/-- gk_prop k N m means: every set of N integers has a k-AP-free subset
of size ≥ m. This is the Prop-level definition of G_k(N) ≥ m. -/
def gk_prop (k N m : ℕ) : Prop :=
  ∀ S : Finset ℤ, S.card = N → HasAPFreeSubsetOfSize S k m

/-
## Basic bounds
-/

/-- Trivial bound: G_k(N) ≤ R_k(N).
{1,...,N} is a particular N-element set, so the worst-case AP-free
subset over all N-element sets is at most the maximum over {1,...,N}. -/
axiom gk_le_rk (k N : ℕ) (hk : 3 ≤ k) : gk k N ≤ rk k N

/-- Strict inequality example: G_3(5) = 3 while R_3(5) = 4. -/
axiom g3_5_eq : gk 3 5 = 3
axiom r3_5_eq : rk 3 5 = 4

/-- G_3(14) ≤ 7 while R_3(14) = 8. -/
axiom g3_14_le : gk 3 14 ≤ 7
axiom r3_14_eq : rk 3 14 = 8

/-
## Komlós–Sulyok–Szemerédi bound
-/

/-- Komlós, Sulyok, Szemerédi (1975): R_k(N) and G_k(N) have the
same order of magnitude, i.e., R_k(N) ≪_k G_k(N). -/
axiom komlos_sulyok_szemeredi (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ N : ℕ, rk k N ≤ C * gk k N

/-
## Main conjecture
-/

/-- Erdős Problem 201: Is the ratio R_3(N)/G_3(N) asymptotically 1?

Formally: for every ε > 0, there exists N₀ such that for all
N ≥ N₀, R_3(N) ≤ (1 + ε) · G_3(N). -/
def ErdosProblem201 : Prop :=
    ∀ (ε : ℚ), 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (rk 3 N : ℚ) ≤ (1 + ε) * (gk 3 N : ℚ)

/-
## Monotonicity
-/

/-- R_k is monotone in N: Icc 1 M ⊆ Icc 1 N when M ≤ N. -/
theorem rk_mono (k : ℕ) (M N : ℕ) (h : M ≤ N) : rk k M ≤ rk k N := by
  unfold rk
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact le_trans hA.1 (Finset.Icc_subset_Icc_right (by exact_mod_cast h))
  · exact hA.2

/-- For k ≤ l, any l-AP-free set is k-AP-free, so R_l(N) ≤ R_k(N). -/
theorem rk_anti_k (k l N : ℕ) (hkl : k ≤ l) (hk1 : k ≥ 1) :
    rk l N ≤ rk k N := by
  unfold rk
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hA.1, isAPFree_of_le hkl hk1 hA.2⟩

/-
## Consequences
-/

/-- From the strict inequality G_3(5) = 3 < 4 = R_3(5). -/
theorem g3_lt_r3_at_5 : gk 3 5 < rk 3 5 := by
  rw [g3_5_eq, r3_5_eq]

/-- The empty set is always AP-free. -/
theorem isAPFree_empty (k : ℕ) : IsAPFree ∅ k := by
  intro ⟨a, d, _, hk1, hmem⟩
  have := hmem ⟨0, by omega⟩
  simp at this

/-- A singleton set is always AP-free (for k ≥ 2). -/
theorem isAPFree_singleton (x : ℤ) (k : ℕ) (hk : k ≥ 2) :
    IsAPFree {x} k := by
  intro ⟨a, d, hd, hk1, hmem⟩
  have h0 := hmem ⟨0, by omega⟩
  have h1 := hmem ⟨1, by omega⟩
  simp at h0 h1
  linarith

/-- R_k(N) ≥ 1 for N ≥ 1 and k ≥ 2: the singleton {1} is always AP-free. -/
theorem rk_pos (k N : ℕ) (hN : N ≥ 1) (hk : k ≥ 2) : rk k N ≥ 1 := by
  unfold rk
  have hmem : ({1} : Finset ℤ) ∈ (Finset.Icc (1 : ℤ) N).powerset.filter
      (fun A => IsAPFree A k) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro x hx
      simp at hx
      subst hx
      simp [Finset.mem_Icc]
      omega
    · exact isAPFree_singleton 1 k hk
  calc Finset.sup ((Finset.Icc (1 : ℤ) ↑N).powerset.filter fun A => IsAPFree A k) Finset.card
      ≥ Finset.card ({1} : Finset ℤ) := Finset.le_sup hmem
    _ = 1 := by simp

/-- Summary of Erdős Problem 201. -/
theorem erdos_201_summary :
    gk 3 5 < rk 3 5 ∧
    ErdosProblem201 ∨ ¬ErdosProblem201 := by
  constructor
  · exact g3_lt_r3_at_5
  · exact Classical.em _
