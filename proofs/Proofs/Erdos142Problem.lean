/-
# Erdős Problem #142: Asymptotic Formula for r_k(N)

Erdős Problem #142 asks for an asymptotic formula for r_k(N), the size of the
largest subset of {1, ..., N} containing no non-trivial k-term arithmetic
progression. This is one of the most fundamental open problems in additive
combinatorics, with a $10,000 reward from Erdős.

Even the case k = 3 (Roth's theorem and its quantitative improvements) remains
far from an asymptotic formula. The best known bounds are:
- Upper: r_3(N) ≤ N · exp(-c(log N)^{1/12}) by Kelley–Meka (2023)
- Lower: r_3(N) ≥ N · exp(-C√(log N)) by Behrend (1946)

For general k, Szemerédi's theorem (1975) gives r_k(N) = o(N), and
Leng–Sah–Sawhney (2024) provide the best upper bounds for k ≥ 5.

Reference: https://erdosproblems.com/142
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic

open scoped Classical

/- ## Definitions -/

/-- An arithmetic progression of length k starting at a with common difference d. -/
def arithProg (a d : ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/-- A set S ⊆ {1, ..., N} is AP-k-free if it contains no k-term arithmetic
    progression with common difference d > 0. -/
def IsAPFree (S : Finset ℕ) (k : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → arithProg a d k ⊆ S → k ≤ 1

/-- r_k(N): the maximum size of an AP-k-free subset of {1, ..., N}. -/
noncomputable def rk (k N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.powerset (Finset.range N)).filter (fun S => IsAPFree S k))
    Finset.card

/- ## Foundational Lemmas (axiom-free)

These lemmas develop the basic API of `arithProg`, `IsAPFree`, and `rk`.  They are
all fully machine-checked with no `sorry` and no `axiom` (host-verified on Lean
v4.31.0).  The deep content of Erdős #142 — the asymptotic formula for `r_k(N)`,
Szemerédi's theorem, Roth/Kelley–Meka and Behrend's bounds — remains
documented-only below; it needs additive-combinatorial machinery beyond Mathlib. -/

/-- The empty progression: a length-`0` arithmetic progression is empty. -/
theorem arithProg_zero (a d : ℕ) : arithProg a d 0 = ∅ := by
  simp [arithProg]

/-- Membership in an arithmetic progression: `x` is one of the `k` terms
`a, a+d, …, a+(k-1)d`. -/
theorem mem_arithProg {a d k x : ℕ} :
    x ∈ arithProg a d k ↔ ∃ i < k, a + i * d = x := by
  simp only [arithProg, Finset.mem_image, Finset.mem_range]

/-- An arithmetic progression of length `k` has at most `k` elements (the map
`i ↦ a + i·d` need not be injective when `d = 0`). -/
theorem arithProg_card_le (a d k : ℕ) : (arithProg a d k).card ≤ k := by
  rw [arithProg]
  exact Finset.card_image_le.trans_eq (Finset.card_range k)

/-- The base point `a` lies in every nonempty progression (it is the term `i = 0`). -/
theorem self_mem_arithProg {a d k : ℕ} (hk : 0 < k) : a ∈ arithProg a d k := by
  rw [mem_arithProg]
  exact ⟨0, hk, by simp⟩

/-- A length-`1` progression is the singleton `{a}`. -/
theorem arithProg_one (a d : ℕ) : arithProg a d 1 = {a} := by
  ext x
  rw [mem_arithProg, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i = 0 := by omega
    subst this; simp
  · rintro rfl
    exact ⟨0, one_pos, by simp⟩

/-- With a genuine common difference `d > 0` the map `i ↦ a + i·d` is injective, so
a length-`k` progression has exactly `k` elements. -/
theorem arithProg_card {a d : ℕ} (hd : 0 < d) (k : ℕ) :
    (arithProg a d k).card = k := by
  have hinj : Function.Injective (fun i => a + i * d) := by
    intro i j h
    simp only [add_right_inj] at h
    exact Nat.eq_of_mul_eq_mul_right hd h
  rw [arithProg, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- Any set is trivially AP-`k`-free once `k ≤ 1`: there is no nontrivial
progression to avoid. -/
theorem IsAPFree_of_k_le_one {S : Finset ℕ} {k : ℕ} (h : k ≤ 1) : IsAPFree S k := by
  intro a d _ _; exact h

/-- The empty set is AP-`k`-free for every `k` (it contains no progression of any
positive length, and length `0`/`1` are trivially allowed). -/
theorem IsAPFree_empty (k : ℕ) : IsAPFree (∅ : Finset ℕ) k := by
  intro a d _ hsub
  rcases Nat.lt_or_ge k 1 with hk | hk
  · omega
  · exact absurd (hsub (self_mem_arithProg hk)) (by simp)

/-- AP-freeness is inherited by subsets: a subset of an AP-`k`-free set is
AP-`k`-free. -/
theorem IsAPFree.subset {S T : Finset ℕ} {k : ℕ} (hST : S ⊆ T)
    (hT : IsAPFree T k) : IsAPFree S k := by
  intro a d hd hsub
  exact hT a d hd (hsub.trans hST)

/-- `r_k(N)` never exceeds `N`, the size of the ambient window `{0, …, N-1}`. -/
theorem rk_le (k N : ℕ) : rk k N ≤ N := by
  unfold rk
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact (Finset.card_le_card hS.1).trans_eq (Finset.card_range N)

/-- `r_k(N)` is monotone in the window size `N`. -/
theorem rk_mono_N {k N M : ℕ} (h : N ≤ M) : rk k N ≤ rk k M := by
  unfold rk
  apply Finset.sup_mono
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  have hr : Finset.range N ⊆ Finset.range M := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  exact ⟨hS.1.trans hr, hS.2⟩

/-- The empty window forces `r_k(0) = 0`. -/
theorem rk_zero (k : ℕ) : rk k 0 = 0 :=
  Nat.le_zero.mp (rk_le k 0)

/-- For `k ≤ 1` there is no progression to forbid, so the whole window is
AP-`k`-free and `r_k(N) = N`. -/
theorem rk_eq_of_k_le_one {k : ℕ} (h : k ≤ 1) (N : ℕ) : rk k N = N := by
  apply le_antisymm (rk_le k N)
  have hmem : Finset.range N ∈
      (Finset.powerset (Finset.range N)).filter (fun S => IsAPFree S k) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_rfl, IsAPFree_of_k_le_one h⟩
  calc N = (Finset.range N).card := (Finset.card_range N).symm
    _ ≤ _ := Finset.le_sup hmem

/- ## Szemerédi's Theorem (qualitative) -/

/- ## Roth's Theorem (k = 3) -/

/- ## Lower Bound: Behrend's Construction -/

/- ## Upper Bound: Kelley–Meka (2023) -/

/- ## Erdős's $5,000 Question -/

/- ## Main Open Problem -/

/- ## For k = 4: Green–Tao -/
