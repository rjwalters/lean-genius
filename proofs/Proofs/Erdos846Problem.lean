/-
Erdős Problem #846 — Non-Trilinear Subsets of the Plane

Let A ⊂ ℝ² be an infinite set such that for some ε > 0, every finite
subset B ⊆ A of size n contains at least εn points with no three collinear.
Must A be the union of finitely many sets, each with no three points collinear?

This is a problem of Erdős, Nešetřil, and Rödl from [Er92b].

**RESOLUTION (2026-05-21, AlphaProof Nexus, arXiv:2605.22763v1)**: NO.
DeepMind's AlphaProof Nexus produced an explicit counterexample (the
Elekes-style parametric construction `A_set` in `Proofs/Erdos846ProblemAPN.lean`)
that is infinite, (1/2)-non-trilinear, but not weakly non-trilinear. The
formal proof of the negation is `Erdos846APN.target_false`. Consequently,
the open conjecture is now **disproved**.

This gallery file retains the elementary definitions and proved easy
directions (converse, finite case, ε bounds) using a cross-product
characterisation of collinearity. The hard direction has been removed
(it was previously stated as `axiom ErdosProblem846`; that axiom is
mathematically false and is dropped). For the refutation, see
`Proofs/Erdos846ProblemAPN.lean`.

Related: Erdős Problem 774, 847.

Reference: https://erdosproblems.com/846
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Set Finset

-- ## Collinearity and Non-Trilinear Sets

/-- Three points in ℝ² are collinear if one is an affine combination of the others.
    We use a simplified characterization via the cross product being zero. -/
def AreCollinear (p q r : Fin 2 → ℝ) : Prop :=
  (q 0 - p 0) * (r 1 - p 1) = (r 0 - p 0) * (q 1 - p 1)

/-- A set is non-trilinear if no three distinct points are collinear -/
def NonTrilinear (S : Set (Fin 2 → ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    p ≠ q → q ≠ r → p ≠ r → ¬AreCollinear p q r

-- ## The ε-Non-Trilinear Property

/-- A set A is ε-non-trilinear if every finite subset B of A contains
    a non-trilinear subset C of size at least ε|B| -/
def IsEpsNonTrilinear (A : Set (Fin 2 → ℝ)) (ε : ℝ) : Prop :=
  ∀ B : Finset (Fin 2 → ℝ), (↑B : Set (Fin 2 → ℝ)) ⊆ A →
    ∃ C : Finset (Fin 2 → ℝ), (↑C : Set (Fin 2 → ℝ)) ⊆ ↑B ∧
      ε * B.card ≤ C.card ∧ NonTrilinear (↑C : Set (Fin 2 → ℝ))

/-- A set is weakly non-trilinear if it is a finite union of
    sets with no three points collinear -/
def IsWeaklyNonTrilinear (A : Set (Fin 2 → ℝ)) : Prop :=
  ∃ n : ℕ, ∃ S : Fin n → Set (Fin 2 → ℝ),
    (∀ i, NonTrilinear (S i)) ∧
    A ⊆ ⋃ i, S i

-- ## Basic Properties of Non-Trilinear Sets

/-- NonTrilinear is monotone: subsets of non-trilinear sets are non-trilinear -/
theorem nonTrilinear_mono {S T : Set (Fin 2 → ℝ)} (hST : S ⊆ T)
    (hT : NonTrilinear T) : NonTrilinear S :=
  fun p hp q hq r hr hpq hqr hpr =>
    hT p (hST hp) q (hST hq) r (hST hr) hpq hqr hpr

/-- The empty set is non-trilinear -/
theorem nonTrilinear_empty : NonTrilinear (∅ : Set (Fin 2 → ℝ)) :=
  fun _ hp => absurd hp (Set.not_mem_empty _)

/-- A singleton set is non-trilinear -/
theorem nonTrilinear_singleton (p : Fin 2 → ℝ) :
    NonTrilinear ({p} : Set (Fin 2 → ℝ)) :=
  fun a ha b hb _ _ hqr _ =>
    hqr (by rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])

/-- A two-element set is non-trilinear: three pairwise distinct elements
    cannot be drawn from a set of two -/
theorem nonTrilinear_pair (p q : Fin 2 → ℝ) (hpq : p ≠ q) :
    NonTrilinear ({p, q} : Set (Fin 2 → ℝ)) := by
  intro a ha b hb c hc hab hbc hac
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    -- In each of 8 cases, at least one of hab/hbc/hac becomes x ≠ x
    contradiction

-- ## Properties of Collinearity

/-- Collinearity is symmetric in the first two arguments -/
theorem areCollinear_symm12 {p q r : Fin 2 → ℝ} (h : AreCollinear p q r) :
    AreCollinear q p r := by
  unfold AreCollinear at *; linarith

/-- Collinearity is cyclically symmetric: (p,q,r) collinear implies (q,r,p) collinear -/
theorem areCollinear_cycle {p q r : Fin 2 → ℝ} (h : AreCollinear p q r) :
    AreCollinear q r p := by
  unfold AreCollinear at *; linarith

/-- Any point is collinear with itself and any other point (degenerate case) -/
theorem areCollinear_self_left (p r : Fin 2 → ℝ) : AreCollinear p p r := by
  unfold AreCollinear; ring

-- ## Proved: Non-trilinear implies ε-non-trilinear with ε = 1

/-- Any non-trilinear set is ε-non-trilinear with ε = 1.
    Proof: Take C = B. Since B ⊆ A and A is non-trilinear, B is also
    non-trilinear by monotonicity. And |C| = |B| = 1 · |B|. -/
theorem nonTrilinear_is_eps_one (A : Set (Fin 2 → ℝ)) (h : NonTrilinear A) :
    IsEpsNonTrilinear A 1 := by
  intro B hB
  refine ⟨B, le_refl _, ?_, nonTrilinear_mono hB h⟩
  simp

-- ## ε-non-trilinear monotonicity in ε

/-- If A is ε-non-trilinear and ε' ≤ ε, then A is ε'-non-trilinear -/
theorem isEpsNonTrilinear_mono {A : Set (Fin 2 → ℝ)} {ε ε' : ℝ}
    (hε : IsEpsNonTrilinear A ε) (hle : ε' ≤ ε) :
    IsEpsNonTrilinear A ε' := by
  intro B hB
  obtain ⟨C, hCB, hcard, hNT⟩ := hε B hB
  refine ⟨C, hCB, ?_, hNT⟩
  calc ε' * ↑B.card ≤ ε * ↑B.card := by
        apply mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
    _ ≤ ↑C.card := hcard

-- ## Auxiliary pigeonhole lemma

/-- Finitary pigeonhole principle: if we map a finite set B into Fin k,
    some fiber has cardinality at least B.card / k (in the sense that
    B.card ≤ k * fiber_size). -/
theorem finset_pigeonhole_exists {α : Type*} [DecidableEq α] (B : Finset α)
    (k : ℕ) (hk : 0 < k) (f : α → Fin k) :
    ∃ i : Fin k, B.card ≤ k * (B.filter (fun x => f x = i)).card := by
  by_contra hall
  push_neg at hall
  have hsum : ∑ i : Fin k, (B.filter (fun x => f x = i)).card = B.card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext x; simp [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun hx => ⟨f x, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
    · intro i _ j _ hij x
      simp [Finset.mem_filter]
      intro _ hi hj; exact absurd (hi ▸ hj) fun h => hij (Fin.ext h)
  have hlt : ∑ i : Fin k, k * (B.filter (fun x => f x = i)).card < k * B.card := by
    apply Finset.sum_lt_sum
    · intro i _; exact le_of_lt (hall i)
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _, hall ⟨0, hk⟩⟩
  rw [← Finset.mul_sum] at hlt
  omega

-- ## Easy direction: weakly non-trilinear → ε-non-trilinear

/-- The easy direction of the Erdős–Nešetřil–Rödl problem:
    Every weakly non-trilinear set has the ε-non-trilinear property for some ε > 0.

    Proof: If A ⊆ ⋃ᵢ₌₁ᵏ Sᵢ with each Sᵢ non-trilinear, then for any
    finite B ⊆ A of size n, by pigeonhole some B ∩ Sᵢ has at least n/k elements.
    That intersection is non-trilinear (subset of Sᵢ), giving ε = 1/k. -/
theorem weaklyNonTrilinear_implies_eps (A : Set (Fin 2 → ℝ))
    (h : IsWeaklyNonTrilinear A) :
    ∃ ε : ℝ, ε > 0 ∧ IsEpsNonTrilinear A ε := by
  obtain ⟨k, S, hS, hA⟩ := h
  by_cases hk : k = 0
  · -- If k = 0, then A ⊆ ⋃ (i : Fin 0), S i = ∅
    subst hk
    refine ⟨1, one_pos, fun B hB => ?_⟩
    have hBe : B = ∅ := by
      ext x; constructor
      · intro hx
        exact absurd (hA (hB (Finset.mem_coe.mpr hx))) (by simp [Set.iUnion_of_empty])
      · exact fun hx => absurd hx (Finset.not_mem_empty _)
    exact ⟨∅, by simp, by simp [hBe], nonTrilinear_empty⟩
  · -- If k > 0, apply pigeonhole to get ε = 1/k
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
    refine ⟨1 / k, div_pos one_pos hkR, ?_⟩
    intro B hB
    -- Assign each point of B to some Sᵢ containing it
    have hmem : ∀ x ∈ B, ∃ i : Fin k, x ∈ S i := fun x hx =>
      Set.mem_iUnion.mp (hA (hB (Finset.mem_coe.mpr hx)))
    classical
    -- Total assignment function (arbitrary outside B)
    let assign : (Fin 2 → ℝ) → Fin k :=
      fun x => if h : x ∈ B then (hmem x h).choose else ⟨0, hkpos⟩
    have hassign : ∀ x ∈ B, x ∈ S (assign x) := by
      intro x hx; simp only [assign, dif_pos hx]; exact (hmem x hx).choose_spec
    -- By pigeonhole, some partition class has ≥ |B|/k elements
    obtain ⟨i, hi⟩ := finset_pigeonhole_exists B k hkpos assign
    -- The fiber assigned to index i
    let C := B.filter (fun x => assign x = i)
    -- C ⊆ B
    have hCsub : (↑C : Set (Fin 2 → ℝ)) ⊆ ↑B := by
      intro x hx; exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter x (Finset.mem_coe.mp hx))
    -- C ⊆ S i
    have hCinS : (↑C : Set (Fin 2 → ℝ)) ⊆ S i := by
      intro x hx
      have hxf := Finset.mem_coe.mp hx
      have hxB := Finset.mem_of_mem_filter x hxf
      have hxa := (Finset.mem_filter.mp hxf).2
      rw [← hxa]; exact hassign x hxB
    refine ⟨C, hCsub, ?_, nonTrilinear_mono hCinS (hS i)⟩
    -- Show (1/k) * |B| ≤ |C|
    rw [div_mul_eq_mul_div, one_mul]
    rw [le_div_iff hkR]
    exact_mod_cast hi

-- ## Finite sets are always weakly non-trilinear

/-- Every finite set is weakly non-trilinear (as a union of singletons).
    This shows the "infinite" condition in Erdős Problem 846 is essential:
    the conjecture is trivially true for finite sets. -/
theorem finite_weaklyNonTrilinear (A : Set (Fin 2 → ℝ)) (hA : Set.Finite A) :
    IsWeaklyNonTrilinear A := by
  classical
  haveI : Fintype ↑A := hA.fintype
  exact ⟨Fintype.card ↑A,
    fun i => {((Fintype.equivFin ↑A).symm i).val},
    fun i => nonTrilinear_singleton _,
    fun x hx => Set.mem_iUnion.mpr
      ⟨Fintype.equivFin ↑A ⟨x, hx⟩, by simp [Equiv.symm_apply_apply]⟩⟩

-- ## Bounds on ε for ε-non-trilinear sets

/-- For any nonempty A, if A is ε-non-trilinear then ε ≤ 1.
    Proof: take B = {a} for a ∈ A. Then C ⊆ B forces |C| ≤ 1, so ε ≤ 1. -/
theorem isEpsNonTrilinear_eps_le_one {A : Set (Fin 2 → ℝ)} {ε : ℝ}
    (hA : A.Nonempty) (heps : IsEpsNonTrilinear A ε) : ε ≤ 1 := by
  obtain ⟨a, ha⟩ := hA
  -- Apply definition with singleton B = {a}
  have hB : (↑({a} : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) ⊆ A := by
    intro x hx; rw [Finset.mem_coe, Finset.mem_singleton] at hx; rw [hx]; exact ha
  obtain ⟨C, hCB, hcard, _⟩ := heps {a} hB
  -- C ⊆ {a} so |C| ≤ 1
  have hCsub : C ⊆ {a} := fun x hx =>
    Finset.mem_coe.mp (hCB (Finset.mem_coe.mpr hx))
  have hCle : C.card ≤ 1 :=
    (Finset.card_le_card hCsub).trans (by simp [Finset.card_singleton])
  -- ε * 1 ≤ |C| ≤ 1
  rw [Finset.card_singleton] at hcard
  linarith [Nat.cast_le.mpr hCle, mul_one ε]

/-- For ε > 1, the only ε-non-trilinear set is the empty set.
    This gives a tight characterization of the valid range ε ∈ (0, 1]. -/
theorem isEpsNonTrilinear_empty_of_eps_gt_one {A : Set (Fin 2 → ℝ)} {ε : ℝ}
    (hε : 1 < ε) (heps : IsEpsNonTrilinear A ε) : A = ∅ := by
  by_contra hne
  have hA : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  exact absurd (isEpsNonTrilinear_eps_le_one hA heps) (not_le.mpr hε)

/-- The Erdős–Nešetřil–Rödl conjecture holds trivially for finite sets.
    This is an immediate corollary of `finite_weaklyNonTrilinear` and shows
    the "infinite" hypothesis in Problem 846 is the essential difficulty. -/
theorem erdos846_finite (A : Set (Fin 2 → ℝ)) (hA : Set.Finite A)
    (ε : ℝ) (_ : ε > 0) (_ : IsEpsNonTrilinear A ε) :
    IsWeaklyNonTrilinear A :=
  finite_weaklyNonTrilinear A hA

-- ## The Erdős–Nešetřil–Rödl Conjecture (DISPROVED, 2026-05-21)

/- **Erdős Problem 846** (Erdős–Nešetřil–Rödl, 1992; DISPROVED 2026-05-21):
    Is every infinite ε-non-trilinear subset of ℝ² weakly non-trilinear (a
    finite union of sets with no three collinear)?

    **Answer**: NO. DeepMind's AlphaProof Nexus produced an explicit
    counterexample on 2026-05-21 (arXiv:2605.22763v1). The Elekes-style
    parametric construction `A_set q` (built from `q (i, j) = (t i + t j,
    t i^2 + t i * t j + t j^2)` with `t_seq n = 100^(4^n)`) is:

    * **infinite** (`Erdos846APN.A_set_infinite`),
    * **(1/2)-non-trilinear** via a bipartite max-cut argument
      (`Erdos846APN.A_set_nontrilinear`), and
    * **not weakly non-trilinear** via a Ramsey-for-triangles argument
      (`Erdos846APN.A_set_not_weakly`).

    The formal refutation is `Erdos846APN.target_false`; see the companion
    file `Proofs/Erdos846ProblemAPN.lean`. Note that the APN file uses
    Mathlib's `Collinear ℝ {x, y, z}` predicate rather than the
    `AreCollinear` cross-product characterisation used in this file
    (they agree on `EuclideanSpace ℝ (Fin 2)`, but unifying the two
    definitions is left as future work).

    The converse (weakly non-trilinear → ε-non-trilinear) is proved above
    as `weaklyNonTrilinear_implies_eps`. The finite case is proved as
    `erdos846_finite`. The valid range is ε ∈ (0, 1] by
    `isEpsNonTrilinear_eps_le_one`. -/
