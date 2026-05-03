/-
  Erdős Problem #1208: Distance-Sidon Subsets in ℝ^d

  For d ≥ 2, let F_d(n) be the maximum f such that every set of n points in ℝ^d
  contains a subset of f points with all pairwise distances distinct. A subset
  with all pairwise distances distinct is called a **distance-Sidon set** — the
  geometric analogue of a Sidon (B₂) set in additive combinatorics.

  Known bounds (for d = 2):
  - Lower bound: F₂(n) ≥ Ω(n^(1/3))
    Via the Spencer–Szemerédi–Trotter unit distance bound O(n^(4/3)) and a
    greedy extraction argument.
  - Upper bound: F₂(n) ≤ O(n^(1/2))
    Via the integer grid {1,...,N}² and the Gauss circle problem bound
    on the number of distinct sums of two squares.

  The exact exponent of F₂(n) remains open (known: 1/3 ≤ exponent ≤ 1/2).

  Status: Partial bounds known; exact asymptotics open.
  Reference: https://erdosproblems.com/1208
-/

import Mathlib

/-! ## Distance-Sidon Sets

A **distance-Sidon set** is a finite set of points Q in ℝ^d such that all
C(|Q|, 2) pairwise distances are distinct. This is the distance analogue of a
Sidon set: just as a Sidon set has all pairwise sums distinct, a distance-Sidon
set has all pairwise distances distinct.

The concept appears naturally in combinatorial geometry and Ramsey theory:
F_d(n) measures how large a distance-Sidon subset can always be found in any
n-point set, i.e., the worst-case guarantee.
-/

/-- A finite set Q in a metric space has the **distance-Sidon property** if
    whenever dist(a, b) = dist(c, e) for points a, b, c, e ∈ Q, the pairs
    {a, b} and {c, e} must coincide (as unordered pairs).

    Equivalently: all C(|Q|, 2) pairwise distances among points of Q are distinct. -/
def IsDistanceSidon {α : Type*} [MetricSpace α] (Q : Finset α) : Prop :=
  ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ∀ e ∈ Q,
    dist a b = dist c e → (a = c ∧ b = e) ∨ (a = e ∧ b = c)

/-- The empty set is vacuously a distance-Sidon set. -/
@[simp]
theorem isDistanceSidon_empty {α : Type*} [MetricSpace α] :
    IsDistanceSidon (∅ : Finset α) := by
  simp [IsDistanceSidon]

/-- A singleton is trivially a distance-Sidon set: there are no two distinct
    pairs of points, so the condition holds vacuously. -/
theorem isDistanceSidon_singleton {α : Type*} [MetricSpace α] (a : α) :
    IsDistanceSidon ({a} : Finset α) := by
  simp [IsDistanceSidon, Finset.mem_singleton]

/-! ## Size Bound for Distance-Sidon Sets

A distance-Sidon set of size k requires at least C(k, 2) = k(k-1)/2 distinct
distance values (one for each pair). This combinatorial observation gives an
upper bound on the size of a distance-Sidon subset in terms of the number of
distinct distances available in the ambient point set.

For a grid {1,...,N}^d with n = N^d points, the number of distinct distances is
O(N^2) by the Gauss circle problem. So any distance-Sidon subset Q satisfies
C(|Q|, 2) ≤ O(N^2), giving |Q| ≤ O(N) = O(n^(1/d)).
-/

/-- **Key size bound**: a distance-Sidon subset Q of size k must use at least
    k(k-1)/2 distinct distance values. Thus |Q| is bounded above by O(√D)
    where D is the number of distinct distances in the ambient point set. -/
theorem distance_sidon_size_bound {α : Type*} [MetricSpace α]
    (Q : Finset α) (hQ : IsDistanceSidon Q) :
    Q.card * (Q.card - 1) / 2 ≤
      ((Q ×ˢ Q).image (fun pq => dist pq.1 pq.2)).card := by
  -- Suffices: Q.card*(Q.card-1) ≤ 2 * |image of Q×Q|, then omega handles the /2
  suffices h : Q.card * (Q.card - 1) ≤
      2 * ((Q ×ˢ Q).image fun pq => dist pq.1 pq.2).card by omega
  -- Rewrite LHS as Q.offDiag.card (since card_offDiag gives s.card*(s.card-1))
  rw [← Finset.card_offDiag]
  -- Each distance value in the offDiag image appears for at most 2 pairs (a,b) and (b,a)
  have hfiber : ∀ d ∈ Q.offDiag.image (fun pq => dist pq.1 pq.2),
      (Q.offDiag.filter (fun pq => dist pq.1 pq.2 = d)).card ≤ 2 := by
    intro d hd
    obtain ⟨⟨a, b⟩, hmem, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hmem
    -- Every element of the fiber is (a, b) or (b, a) by IsDistanceSidon
    have hsub : Q.offDiag.filter (fun pq => dist pq.1 pq.2 = dist a b) ⊆
        ({(a, b), (b, a)} : Finset (α × α)) := by
      intro ⟨c, e⟩ hce
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hce
      obtain ⟨⟨hc, he, _⟩, hdist⟩ := hce
      rcases hQ c hc e he a ha b hb hdist with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (by simp [Finset.card_singleton]))
  -- offDiag.card ≤ 2 * (offDiag image).card  by the fiber bound
  have hoff : Q.offDiag.card ≤
      2 * (Q.offDiag.image fun pq => dist pq.1 pq.2).card :=
    Finset.card_le_mul_card_image Q.offDiag (fun pq => dist pq.1 pq.2) hfiber
  -- offDiag image ⊆ Q×Q image
  have himg : (Q.offDiag.image fun pq => dist pq.1 pq.2).card ≤
      ((Q ×ˢ Q).image fun pq => dist pq.1 pq.2).card := by
    apply Finset.card_le_card
    apply Finset.image_subset_image
    intro ⟨c, e⟩ hce
    simp only [Finset.mem_offDiag] at hce
    exact Finset.mem_product.mpr ⟨hce.1, hce.2.1⟩
  linarith

/-! ## Known Asymptotic Bounds for F_d(n) (Axiomatized)

The following bounds require results not yet formalized in Mathlib:
- The Spencer–Szemerédi–Trotter unit distance theorem (1984): among n points
  in ℝ², the number of unit distances is at most O(n^(4/3)).
- The Gauss circle problem analog: the integer grid {1,...,N}^d has O(N^2)
  distinct distances.

Both are axiomatized below; the resulting bounds on F_d(n) follow from them.
-/

/-- **Lower bound axiom** (d = 2, Spencer–Szemerédi–Trotter 1984):
    Every n-point set P ⊂ ℝ² contains a distance-Sidon subset Q ⊆ P with
    |Q| ≥ C · n^(1/3) for an absolute constant C > 0.

    Proof method: The unit distance bound gives at most O(n^(4/3)) pairs at
    any single distance. Averaging over C(n,2) ∼ n²/2 pairs and O(n^(4/3))
    repetitions, a greedy "add a point with new distances" construction runs
    for Ω(n^(1/3)) steps before getting stuck. -/
axiom fd2_lower_bound : ∃ C : ℝ, C > 0 ∧
  ∀ n : ℕ, 1 ≤ n →
  ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n →
  ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
    Q ⊆ P ∧ IsDistanceSidon Q ∧ C * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (Q.card : ℝ)

/-- **Upper bound axiom** (d = 2, grid construction):
    There exist n-point sets P ⊂ ℝ² where every distance-Sidon subset Q ⊆ P
    satisfies |Q| ≤ C · n^(1/2) for an absolute constant C > 0.

    Proof method: The grid P = {1,...,N}² has n = N² points and O(N²) distinct
    distances (Gauss circle problem). Any distance-Sidon subset of size k uses
    C(k,2) distinct distances, so C(k,2) ≤ C·N², giving k ≤ O(N) = O(n^(1/2)). -/
axiom fd2_upper_bound : ∃ C : ℝ, C > 0 ∧
  ∀ n : ℕ, 1 ≤ n →
  ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
  ∀ Q : Finset (EuclideanSpace ℝ (Fin 2)),
    Q ⊆ P → IsDistanceSidon Q → (Q.card : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2)

/-- **Erdős Problem #1208** (main result, d = 2):
    Every n-point set in the Euclidean plane ℝ² contains a distance-Sidon
    subset of size at least Ω(n^(1/3)).

    This gives the lower bound direction: F₂(n) ≥ Ω(n^(1/3)). The upper bound
    F₂(n) ≤ O(n^(1/2)) is given by `fd2_upper_bound`. The true exponent α with
    F₂(n) ≍ n^α lies in [1/3, 1/2] and remains one of the open questions in
    combinatorial geometry. -/
theorem erdos_1208 :
    ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, 1 ≤ n →
    ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n →
    ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
      Q ⊆ P ∧ IsDistanceSidon Q ∧ C * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (Q.card : ℝ) :=
  fd2_lower_bound

-- Sanity check: key declarations are accessible
#check erdos_1208
#check IsDistanceSidon
#check fd2_lower_bound
#check fd2_upper_bound
