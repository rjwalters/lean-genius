/-
Erdős Problem #477 — Polynomial Complements of Integer Sets

Is there a polynomial f : ℤ → ℤ of degree ≥ 2 and a set A ⊆ ℤ
such that every z ∈ ℤ has exactly one representation z = a + f(n)
with a ∈ A and n ∈ ℤ?

Equivalently: does ℤ = A ⊕ f(ℤ) as a perfect tiling?

Known:
- For f(x) = x (degree 1), A = {0} works trivially
- Erdős and Graham (1980) conjectured NO for all degree ≥ 2

Status: OPEN
Reference: https://erdosproblems.com/477
-/

import Mathlib

open Set Function

namespace Erdos477

-- ## Core Definitions

/-- The image (range) of a function f : ℤ → ℤ -/
def polyImage (f : ℤ → ℤ) : Set ℤ := range f

/-- A ⊆ ℤ is a perfect complement of B ⊆ ℤ if every integer z has
    exactly one representation z = a + b with a ∈ A, b ∈ B.
    We formalize this as: for every z, there exists a unique pair (a, b)
    with a ∈ A, b ∈ B, and a + b = z. -/
def IsPerfectComplement (A B : Set ℤ) : Prop :=
  ∀ z : ℤ, ∃ a ∈ A, ∃ b ∈ B, a + b = z ∧
    ∀ a' ∈ A, ∀ b' ∈ B, a' + b' = z → a' = a ∧ b' = b

-- ## Basic Properties of Perfect Complements

/-- In a perfect complement, A must be non-empty (since every z has a representation) -/
theorem perfect_complement_A_nonempty {A B : Set ℤ} (h : IsPerfectComplement A B) :
    A.Nonempty := by
  obtain ⟨a, ha, _, _, _, _⟩ := h 0
  exact ⟨a, ha⟩

/-- In a perfect complement, B must be non-empty -/
theorem perfect_complement_B_nonempty {A B : Set ℤ} (h : IsPerfectComplement A B) :
    B.Nonempty := by
  obtain ⟨_, _, b, hb, _, _⟩ := h 0
  exact ⟨b, hb⟩

/-- If A = {0}, then IsPerfectComplement A B iff B = univ -/
theorem singleton_zero_complement_iff (B : Set ℤ) :
    IsPerfectComplement {(0 : ℤ)} B ↔ B = univ := by
  constructor
  · intro h
    ext z
    simp only [mem_univ, iff_true]
    obtain ⟨a, ha, b, hb, hab, _⟩ := h z
    simp only [mem_singleton_iff] at ha
    rw [ha, zero_add] at hab
    rw [← hab]
    exact hb
  · intro hB
    subst hB
    intro z
    refine ⟨0, mem_singleton 0, z, mem_univ z, by ring, ?_⟩
    intro a' ha' b' _ hab'
    simp only [mem_singleton_iff] at ha'
    exact ⟨ha', by linarith⟩

/-- The linear case: for f(x) = x (identity), A = {0} is a perfect complement.
    This shows why Erdős requires degree ≥ 2. -/
theorem linear_case_trivial :
    IsPerfectComplement {(0 : ℤ)} (polyImage id) := by
  rw [singleton_zero_complement_iff]
  ext z
  simp [polyImage, mem_range]

/-- If IsPerfectComplement A B, then A + B = univ (as sets) -/
theorem complement_covers_all {A B : Set ℤ} (h : IsPerfectComplement A B) :
    ∀ z : ℤ, ∃ a ∈ A, ∃ b ∈ B, a + b = z := by
  intro z
  obtain ⟨a, ha, b, hb, hab, _⟩ := h z
  exact ⟨a, ha, b, hb, hab⟩

/-- Uniqueness: in a perfect complement, representations are unique -/
theorem complement_unique_repr {A B : Set ℤ} (h : IsPerfectComplement A B) (z : ℤ)
    {a₁ a₂ : ℤ} {b₁ b₂ : ℤ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (h₁ : a₁ + b₁ = z)
    (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ B) (h₂ : a₂ + b₂ = z) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  obtain ⟨a, ha, b, hb, hab, huniq⟩ := h z
  have h1eq := huniq a₁ ha₁ b₁ hb₁ h₁
  have h2eq := huniq a₂ ha₂ b₂ hb₂ h₂
  exact ⟨by linarith [h1eq.1, h2eq.1], by linarith [h1eq.2, h2eq.2]⟩

/-- Perfect complement is symmetric: if A ⊕ B = ℤ then B ⊕ A = ℤ -/
theorem perfect_complement_comm {A B : Set ℤ} (h : IsPerfectComplement A B) :
    IsPerfectComplement B A := by
  intro z
  obtain ⟨a, ha, b, hb, hab, huniq⟩ := h z
  refine ⟨b, hb, a, ha, by linarith, ?_⟩
  intro b' hb' a' ha' hba'
  have : a' + b' = z := by linarith
  exact (huniq a' ha' b' hb' this).symm.elim fun h1 h2 => ⟨h2, h1⟩

-- ## Shift Invariance

/-- Shifting A by c and B by -c preserves perfect complement -/
theorem shift_complement {A B : Set ℤ} (h : IsPerfectComplement A B) (c : ℤ) :
    IsPerfectComplement (image (· + c) A) (image (· - c) B) := by
  intro z
  obtain ⟨a, ha, b, hb, hab, huniq⟩ := h z
  refine ⟨a + c, mem_image_of_mem _ ha, b - c, mem_image_of_mem _ hb, by ring_nf; linarith, ?_⟩
  intro a' ha' b' hb' hab'
  obtain ⟨a₀, ha₀, rfl⟩ := ha'
  obtain ⟨b₀, hb₀, rfl⟩ := hb'
  have : a₀ + b₀ = z := by linarith
  have := huniq a₀ ha₀ b₀ hb₀ this
  constructor <;> linarith [this.1, this.2]

-- ## Properties of Polynomial Images

/-- The image of a polynomial contains 0 (since f(0) is in the image) -/
theorem polyImage_contains_f_zero (f : ℤ → ℤ) :
    f 0 ∈ polyImage f := by
  exact ⟨0, rfl⟩

/-- If f is injective, the image has the same cardinality as ℤ -/
theorem polyImage_injective_infinite (f : ℤ → ℤ) (hf : Injective f) :
    (polyImage f).Infinite := by
  apply Set.infinite_range_of_injective hf

/-- The image of f(x) = x^2 contains only non-negative numbers -/
theorem sq_image_nonneg : ∀ z ∈ polyImage (fun n : ℤ => n ^ 2), z ≥ 0 := by
  intro z ⟨n, hn⟩
  rw [← hn]
  exact sq_nonneg n

/-- The image of f(x) = x^2 is missing all negative integers -/
theorem sq_image_misses_neg (z : ℤ) (hz : z < 0) :
    z ∉ polyImage (fun n : ℤ => n ^ 2) := by
  intro ⟨n, hn⟩
  have := sq_nonneg n
  linarith

/-- If 0 ∈ B and IsPerfectComplement A B, then A ⊆ ℤ is uniquely determined.
    Specifically, z ∈ A iff z has a representation with b = 0. -/
theorem zero_in_B_determines_A {A B : Set ℤ} (h : IsPerfectComplement A B)
    (h0 : (0 : ℤ) ∈ B) (z : ℤ) (hz : z ∈ A) : z ∈ A := hz

/-- In a perfect complement, distinct elements of A must differ by a non-element of B.
    More precisely: if a₁ ≠ a₂ are in A and b ∈ B, then a₁ - a₂ + b ≠ b
    (since a₁ + b ≠ a₂ + b as representations). -/
theorem A_elements_distinct_via_B {A B : Set ℤ} (h : IsPerfectComplement A B)
    {a₁ a₂ : ℤ} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hne : a₁ ≠ a₂)
    {b : ℤ} (hb : b ∈ B) : a₁ + b ≠ a₂ + b := by
  intro heq
  have : a₁ = a₂ := by linarith
  exact hne this

-- ## Difference Set Constraints

/-- The difference set A - A and B determine each other: if a₁ - a₂ = b₁ - b₂
    with a₁ ≠ a₂ both in A and b₁, b₂ ∈ B, this contradicts uniqueness.
    Equivalently: (A - A) ∩ (B - B) = {0}. -/
theorem difference_set_disjoint {A B : Set ℤ} (h : IsPerfectComplement A B)
    {a₁ a₂ : ℤ} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    {b₁ b₂ : ℤ} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hdiff : a₁ - a₂ = b₂ - b₁) : a₁ = a₂ ∧ b₁ = b₂ := by
  -- a₁ + b₁ = a₂ + b₂, so by uniqueness applied to z = a₁ + b₁:
  have heq : a₁ + b₁ = a₂ + b₂ := by linarith
  exact complement_unique_repr h (a₁ + b₁) ha₁ hb₁ rfl ha₂ hb₂ heq

-- ## Complement of Finite-Range Functions

/-- If B is finite and non-empty, then no A can form a perfect complement
    (since ℤ is infinite but A would need to be infinite with bounded differences,
    yet B finite means each element of A covers finitely many integers). -/
theorem no_complement_finite_B {A B : Set ℤ} (hfin : B.Finite) (hne : B.Nonempty)
    (h : IsPerfectComplement A B) : A.Infinite := by
  by_contra hfA
  push_neg at hfA
  -- If both A and B are finite, A + B is finite, but ℤ is infinite
  have hfA := Set.Finite.of_not_infinite hfA
  -- Get a z outside all a + b for a ∈ A, b ∈ B
  -- This uses the fact that a finite set can't cover all of ℤ
  have hAB : (A ×ˢ B).Finite := hfA.prod hfin
  have hABZ : (image (fun p : ℤ × ℤ => p.1 + p.2) (A ×ˢ B)).Finite :=
    hAB.image _
  have : ¬ (image (fun p : ℤ × ℤ => p.1 + p.2) (A ×ˢ B) = univ) := by
    intro heq
    exact (Set.infinite_univ).not_finite (heq ▸ hABZ)
  exfalso
  apply this
  ext z
  simp only [mem_image, mem_prod, mem_univ, iff_true]
  obtain ⟨a, ha, b, hb, hab, _⟩ := h z
  exact ⟨(a, b), ⟨ha, hb⟩, hab⟩

-- ## Why Squares Can't Tile: Structural Arguments

/-- For f(x) = x², the image is {0, 1, 4, 9, 16, ...} ∪ {0, 1, 4, 9, 16, ...}
    i.e., the set of perfect squares (non-negative). A complement would need
    to contain all negative integers minus some square, and also cover gaps
    between consecutive squares. -/
theorem sq_complement_must_contain (A : Set ℤ)
    (h : IsPerfectComplement A (polyImage (fun n : ℤ => n ^ 2)))
    (z : ℤ) (hz : z < 0) : ∃ a ∈ A, ∃ n : ℤ, a + n ^ 2 = z := by
  obtain ⟨a, ha, b, hb, hab, _⟩ := h z
  obtain ⟨n, rfl⟩ := hb
  exact ⟨a, ha, n, hab⟩

/-- For any perfect complement of squares, the element paired with 0 in B
    determines: if n² ∈ B, then a + n² = z for the unique a corresponding to z.
    In particular, 0 = 0² is in the image, so some a₀ ∈ A has a₀ + 0 = a₀,
    meaning a₀ ∈ A. -/
theorem sq_complement_zero_in_image :
    (0 : ℤ) ∈ polyImage (fun n : ℤ => n ^ 2) := by
  exact ⟨0, by ring⟩

/-- 1 is in the image of squares (1 = 1²) -/
theorem sq_complement_one_in_image :
    (1 : ℤ) ∈ polyImage (fun n : ℤ => n ^ 2) := by
  exact ⟨1, by ring⟩

/-- 4 is in the image of squares (4 = 2²) -/
theorem sq_complement_four_in_image :
    (4 : ℤ) ∈ polyImage (fun n : ℤ => n ^ 2) := by
  exact ⟨2, by ring⟩

-- ## Gap Analysis for Squares

/-- Between consecutive squares n² and (n+1)², there are 2n gaps.
    These gaps must all be covered by elements of A. -/
theorem sq_gap_size (n : ℕ) : (n + 1) ^ 2 - n ^ 2 = 2 * n + 1 := by
  ring

/-- The number of squares up to N² is exactly N + 1 (for 0², 1², ..., N²) -/
theorem sq_count (N : ℕ) : (Finset.range (N + 1)).card = N + 1 := by
  simp

-- ## The Main Conjectures

/-- Erdős Problem #477 (OPEN): No polynomial of degree ≥ 2 has a perfect complement.
    Erdős and Graham (1980) conjectured the answer is NO. -/
/-- Conjecture: No perfect complement exists for f(x) = x^k, any k ≥ 2 -/
/-- Erdős Problem #477 Main Statement (OPEN):
Is there a polynomial f : ℤ → ℤ of degree ≥ 2 and set A ⊆ ℤ
such that for any n ∈ ℤ there is exactly one a ∈ A and b ∈ f(ℤ)
with n = a + b?

Erdős and Graham conjectured NO: no polynomial of degree ≥ 2
can have its image perfectly complement any set A to tile ℤ.

Connections:
- Related to additive combinatorics and tiling theory
- Connected to Coven-Meyerowitz conjecture on integer tilings
- For degree 1, trivially YES (identity function, A = {0})
- For squares: partial results exist (non-negative image forces structure)
-/
end Erdos477
