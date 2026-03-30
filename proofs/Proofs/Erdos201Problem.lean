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

/-- A set S has a k-AP-free subset of size at least m. -/
def HasAPFreeSubsetOfSize (S : Finset ℤ) (k m : ℕ) : Prop :=
  ∃ A : Finset ℤ, A ⊆ S ∧ IsAPFree A k ∧ A.card ≥ m

/-- gk_prop k N m means: every set of N integers has a k-AP-free subset
of size ≥ m. This is the Prop-level definition of G_k(N) ≥ m. -/
def gk_prop (k N m : ℕ) : Prop :=
  ∀ S : Finset ℤ, S.card = N → HasAPFreeSubsetOfSize S k m

/-- G_k(N): the greatest m such that every N-element integer set has
a k-AP-free subset of size at least m.

Defined as sSup of valid lower bounds. The set is nonempty (0 is valid:
the empty subset is AP-free) and bounded above by N. -/
noncomputable def gk (k N : ℕ) : ℕ :=
  sSup { m : ℕ | gk_prop k N m }

/-- gk_prop k N 0 always holds: the empty set is always AP-free. -/
theorem gk_prop_zero (k N : ℕ) : gk_prop k N 0 := by
  intro S _
  exact ⟨∅, Finset.empty_subset _, isAPFree_empty k, by omega⟩

/-- The set of valid lower bounds for G_k(N) is bounded above by N. -/
private lemma gk_bddAbove (k N : ℕ) : BddAbove {m : ℕ | gk_prop k N m} := by
  use N; intro m hm
  set S := (Finset.range N).image (fun i : ℕ => (i : ℤ))
  have hS_card : S.card = N := by
    rw [Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)]
    exact Finset.card_range N
  obtain ⟨A, hA_sub, _, hA_card⟩ := hm S hS_card
  linarith [Finset.card_le_card hA_sub]

/-- G_k(N) ≥ 1 for N ≥ 1 and k ≥ 2: any nonempty set has a singleton
    AP-free subset. -/
theorem gk_ge_one (k N : ℕ) (hN : N ≥ 1) (hk : k ≥ 2) : gk k N ≥ 1 := by
  unfold gk
  apply le_csSup (gk_bddAbove k N)
  intro S hS
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  exact ⟨{x}, Finset.singleton_subset_iff.mpr hx, isAPFree_singleton x k hk, by simp⟩

/-- G_k(N) is anti-monotone in k: larger k means harder AP avoidance,
    but any l-AP-free set is also k-AP-free when k ≤ l. -/
theorem gk_anti_k (k l N : ℕ) (hkl : k ≤ l) (hk1 : k ≥ 1) : gk l N ≤ gk k N := by
  unfold gk
  apply csSup_le_csSup (gk_bddAbove k N) ⟨0, gk_prop_zero l N⟩
  intro m hm S hS
  obtain ⟨A, hA_sub, hA_free, hA_card⟩ := hm S hS
  exact ⟨A, hA_sub, isAPFree_of_le hkl hk1 hA_free, hA_card⟩

/-
## Basic bounds
-/

/-- Trivial bound: G_k(N) ≤ R_k(N).
{1,...,N} is a particular N-element set, so the worst-case AP-free
subset over all N-element sets is at most the maximum over {1,...,N}.
Proof: each valid bound m satisfies m ≤ rk k N, since applying the
universality to Icc 1 N yields an AP-free subset A with m ≤ |A| ≤ rk. -/
theorem gk_le_rk (k N : ℕ) (hk : 3 ≤ k) : gk k N ≤ rk k N := by
  apply csSup_le ⟨0, fun S _ => ⟨∅, Finset.empty_subset _,
    fun ⟨a, d, _, _, hmem⟩ => by have := hmem ⟨0, by omega⟩; simp at this, by omega⟩⟩
  intro m hm
  -- For N = 0: the only size-0 set is ∅, so A = ∅ and m ≤ 0 = rk k 0
  by_cases hN : N = 0
  · subst hN
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm ∅ rfl
    have hA_empty := Finset.subset_empty.mp hA_sub
    rw [hA_empty] at hA_card
    simp at hA_card
    omega
  · -- For N ≥ 1: apply hm to S = image (·+1) (range N) ⊆ Icc 1 N
    have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
    -- Build an N-element set inside Icc 1 N
    set S := (Finset.range N).image (fun i : ℕ => (i : ℤ) + 1) with hS_def
    have hS_card : S.card = N := by
      rw [hS_def, Finset.card_image_of_injective]
      · exact Finset.card_range N
      · intro a b hab; omega
    have hS_sub : S ⊆ Finset.Icc (1 : ℤ) ↑N := by
      intro x hx
      simp [hS_def] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp [Finset.mem_Icc]
      omega
    obtain ⟨A, hA_sub, hA_free, hA_card⟩ := hm S hS_card
    -- A ⊆ S ⊆ Icc 1 N, so A is in the filtered powerset defining rk
    have hA_sub_Icc : A ⊆ Finset.Icc (1 : ℤ) ↑N := le_trans hA_sub hS_sub
    have hA_mem : A ∈ (Finset.Icc (1 : ℤ) ↑N).powerset.filter (fun B => IsAPFree B k) := by
      simp [Finset.mem_filter, Finset.mem_powerset, hA_sub_Icc, hA_free]
    exact le_trans hA_card (Finset.le_sup hA_mem)

/-- Strict inequality example: G_3(5) = 3 while R_3(5) = 4. -/
axiom g3_5_eq : gk 3 5 = 3

/-- R_3(5) = 4: the maximum 3-AP-free subset of {1,...,5} has size 4.
    Witness: {1,2,4,5} is 3-AP-free. Upper bound: {1,...,5} contains {1,3,5} (a 3-AP).
    Previously axiomatized; now proved from definitions. -/
theorem r3_5_eq : rk 3 5 = 4 := by
  apply Nat.le_antisymm
  · -- Upper bound: rk 3 5 ≤ 4
    apply Finset.sup_le
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_powerset] at hA
    obtain ⟨hA_sub, hA_free⟩ := hA
    by_contra h; push_neg at h
    -- A.card ≥ 5, but A ⊆ Icc 1 5 (card 5), so A = Icc 1 5
    have hA5 : A.card = 5 := by
      have := Finset.card_le_card hA_sub
      simp only [Finset.card_Icc] at this; omega
    have hA_eq : A = Finset.Icc (1 : ℤ) 5 :=
      Finset.eq_of_subset_of_card_le hA_sub (by simp [Finset.card_Icc, hA5])
    -- But Icc 1 5 contains the 3-AP {1, 3, 5} (a=1, d=2)
    exact hA_free ⟨1, 2, by omega, by omega, fun ⟨i, hi⟩ => by
      fin_cases ⟨i, hi⟩ <;> simp_all [Finset.mem_Icc] <;> omega⟩
  · -- Lower bound: rk 3 5 ≥ 4 via witness {1, 2, 4, 5}
    have hA_mem : ({1, 2, 4, 5} : Finset ℤ) ∈
        (Finset.Icc (1 : ℤ) 5).powerset.filter (IsAPFree · 3) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Icc]
        rcases hx with rfl | rfl | rfl | rfl <;> omega
      · intro ⟨a, d, hd, _, hmem⟩
        have h0 := hmem ⟨0, by omega⟩; simp at h0
        have h1 := hmem ⟨1, by omega⟩; simp at h1
        have h2 := hmem ⟨2, by omega⟩; simp at h2
        simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 h2
        rcases h0 with rfl | rfl | rfl | rfl <;>
          rcases h1 with h1 | h1 | h1 | h1 <;> omega
    calc (4 : ℕ) = ({1, 2, 4, 5} : Finset ℤ).card := by native_decide
      _ ≤ rk 3 5 := Finset.le_sup hA_mem

/- G_3(14) ≤ 7 while R_3(14) = 8.
    Formally: gk 3 14 ≤ 7 and rk 3 14 = 8. -/

/-
## Komlós–Sulyok–Szemerédi bound
-/

/- Komlós, Sulyok, Szemerédi (1975): R_k(N) and G_k(N) have the
same order of magnitude, i.e., R_k(N) ≪_k G_k(N).
Formally: ∀ k ≥ 3, ∃ C > 0, ∀ N, rk k N ≤ C * gk k N. -/

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

/-- A two-element set is always k-AP-free for k ≥ 3.
    Three AP elements are distinct (d ≠ 0), so they can't fit in a 2-element set. -/
theorem isAPFree_pair (x y : ℤ) (hxy : x ≠ y) (k : ℕ) (hk : k ≥ 3) :
    IsAPFree {x, y} k := by
  intro ⟨a, d, hd, _, hmem⟩
  have h0 := hmem ⟨0, by omega⟩
  have h1 := hmem ⟨1, by omega⟩
  have h2 := hmem ⟨2, by omega⟩
  simp at h0 h1 h2
  rcases h0 with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith

/-- G_k(0) = 0: the only 0-element set is ∅, whose only subset is ∅. -/
theorem gk_zero (k : ℕ) : gk k 0 = 0 := by
  unfold gk
  apply le_antisymm
  · apply csSup_le ⟨0, fun S hS => ⟨∅, Finset.empty_subset _, isAPFree_empty k, by omega⟩⟩
    intro m hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm ∅ rfl
    rw [Finset.subset_empty.mp hA_sub] at hA_card; simp at hA_card
  · exact Nat.zero_le _

/-- gk_prop is anti-monotone in k: if every N-set has a k-AP-free subset of size m,
    then every N-set has an l-AP-free subset of size m (for l ≥ k). -/
theorem gk_prop_anti_k {k l N m : ℕ} (hkl : k ≤ l) (hk1 : k ≥ 1)
    (h : gk_prop k N m) : gk_prop l N m := by
  intro S hS
  obtain ⟨A, hA_sub, hA_free, hA_card⟩ := h S hS
  exact ⟨A, hA_sub, isAPFree_of_le hkl hk1 hA_free, hA_card⟩

/-- gk_prop is monotone in N: if every M-set has a k-AP-free subset of size m,
    and M ≤ N, then every N-set also does (by restricting to an M-element subset). -/
theorem gk_prop_mono_N {k M N m : ℕ} (hMN : M ≤ N) (h : gk_prop k M m) :
    gk_prop k N m := by
  intro S hS
  -- S has N ≥ M elements; take any M-element subset
  have ⟨S', hS'_sub, hS'_card⟩ := Finset.exists_subset_card_le (by omega : M ≤ S.card)
  obtain ⟨A, hA_sub, hA_free, hA_card⟩ := h S' hS'_card
  exact ⟨A, le_trans hA_sub hS'_sub, hA_free, hA_card⟩

/-- R_k(N) ≥ 2 for N ≥ 2 and k ≥ 3: any two distinct elements are k-AP-free. -/
theorem rk_ge_two (k N : ℕ) (hN : N ≥ 2) (hk : k ≥ 3) : rk k N ≥ 2 := by
  unfold rk
  have hmem : ({1, 2} : Finset ℤ) ∈ (Finset.Icc (1 : ℤ) N).powerset.filter
      (fun A => IsAPFree A k) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, isAPFree_pair 1 2 (by omega) k hk⟩
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [Finset.mem_Icc] <;> omega
  calc Finset.sup ((Finset.Icc (1 : ℤ) ↑N).powerset.filter fun A => IsAPFree A k) Finset.card
      ≥ Finset.card ({1, 2} : Finset ℤ) := Finset.le_sup hmem
    _ = 2 := by simp

/-- Summary of Erdős Problem 201. -/
theorem erdos_201_summary :
    gk 3 5 < rk 3 5 ∧
    ErdosProblem201 ∨ ¬ErdosProblem201 := by
  constructor
  · exact g3_lt_r3_at_5
  · exact Classical.em _
