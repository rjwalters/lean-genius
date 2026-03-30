import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-
Erdős Problem 959: Distance Frequency Gaps in Planar Point Sets

Let A ⊂ ℝ² be a set of n points with distinct distances d₁, ..., dₖ.
Order by frequency: f(d₁) ≥ f(d₂) ≥ ⋯ ≥ f(dₖ).

Estimate max(f(d₁) - f(d₂)) over all n-point sets.

Clemen, Dumitrescu, and Liu (2025) showed:
- max(f(d₁) - f(d₂)) ≫ n log n
- For 1 ≤ r ≤ log n, max(f(dᵣ) - f(dᵣ₊₁)) ≫ n log n / r

They conjecture max(f(d₁) - f(d₂)) ≫ n^{1 + c / log log n}.

Reference: erdosproblems.com/959
-/

open Finset

-- ## Distance frequency

/-- The distance multiset for a finite point set: count of pairs at each distance. -/
noncomputable def distFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
    ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/-- The set of distinct distances realized by a point set. -/
noncomputable def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
    (A ×ˢ A).image (fun p => dist p.1 p.2) |>.filter (· > 0)

/-- The maximum distance frequency for a point set. -/
noncomputable def maxFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
    (distinctDistances A).sup (distFrequency A)

/-- The second-largest distance frequency. -/
noncomputable def secondFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
    ((distinctDistances A).image (distFrequency A) |>.erase (maxFrequency A)).sup id

/-- The frequency gap: difference between top two frequencies. -/
noncomputable def frequencyGap (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
    maxFrequency A - secondFrequency A

-- ## Main conjecture

/-- Erdős Problem 959: For some constant C > 0, every sufficiently large n admits
an n-point set whose frequency gap is at least C · n · log n. -/
def ErdosProblem959 : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧ C * n * Real.log n ≤ (frequencyGap A : ℝ)

-- ## Known lower bound

/-- Clemen-Dumitrescu-Liu (2025): there exists a universal constant C > 0 such that
    for all n ≥ 2, some n-point set achieves frequency gap ≥ C·n·log n.
    The ≫ notation means C is independent of n. -/
axiom clemen_dumitrescu_liu :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧ C * n * Real.log n ≤ (frequencyGap A : ℝ)

/-- Erdős Problem 959 is resolved by the Clemen-Dumitrescu-Liu result. -/
theorem erdos_959_resolved : ErdosProblem959 := clemen_dumitrescu_liu

-- ## Stronger conjecture

/-- Conjectured: max gap grows as n^{1 + c/log log n} for some c > 0. -/
def ErdosProblem959_strong : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 3 ≤ n →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧
          (n : ℝ) ^ (1 + c / Real.log (Real.log n)) ≤ (frequencyGap A : ℝ)

-- ## Structural properties

/-- Distance frequency is always non-negative (trivially true for ℕ). -/
theorem distFrequency_nonneg (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) :
    0 ≤ distFrequency A d :=
  Nat.zero_le _

/-- The maximum frequency is at least the second frequency. -/
theorem maxFreq_ge_second (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    secondFrequency A ≤ maxFrequency A := by
  -- Proved by Aristotle (Harmonic)
  unfold secondFrequency maxFrequency
  simp +zetaDelta at *
  exact fun b hb x hx hx' => hx'.symm ▸ Finset.le_sup (f := distFrequency A) hx

/-- Zero distance has frequency 0: dist(p,q) = 0 forces p = q, contradicting p ≠ q. -/
theorem distFrequency_zero (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    distFrequency A 0 = 0 := by
  unfold distFrequency
  suffices h : ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 0)) = ∅ by
    simp [h]
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.not_mem_empty, iff_false, not_and]
  intro _ hne hdist
  exact hne (dist_eq_zero.mp hdist)

/-- The frequency gap for the empty set is zero. -/
theorem frequencyGap_empty : frequencyGap ∅ = 0 := by
  unfold frequencyGap maxFrequency secondFrequency distinctDistances
  simp [Finset.product_empty]

-- ## Generalized frequency gap

/-- The r-th frequency gap: difference between the r-th and (r+1)-th most
    frequent distances. -/
noncomputable def frequencyGapR (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : ℕ) : ℕ :=
  let freqs := ((distinctDistances A).image (distFrequency A)).sort (· ≥ ·)
  if hr : r < freqs.length ∧ r + 1 < freqs.length then
    freqs.get ⟨r, hr.1⟩ - freqs.get ⟨r + 1, hr.2⟩
  else 0

-- ## Total pair count

/-- The sum of all distance frequencies is at most n choose 2. -/
theorem total_pairs (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    (distinctDistances A).sum (distFrequency A) ≤ A.card.choose 2 := by
  -- Proved by Aristotle (Harmonic): sum of frequencies ≤ number of pairs ≤ n choose 2
  have h_sum : ((distinctDistances A).sum (distFrequency A)) * 2 ≤
      ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).card := by
    have h_sub : ((distinctDistances A).sum (fun d =>
        ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card)) ≤
        ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).card := by
      rw [← Finset.card_biUnion]
      · exact Finset.card_le_card fun x hx => by aesop
      · exact fun x hx y hy hxy =>
          Finset.disjoint_left.mpr fun p hp hp' => hxy (by aesop)
    refine' le_trans _ h_sub
    rw [Finset.sum_mul _ _ _]
    exact Finset.sum_le_sum fun x hx => Nat.div_mul_le_self _ _
  have h_pairs : ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).card = A.card * (A.card - 1) := by
    rw [show { p ∈ A ×ˢ A | ¬p.1 = p.2 } = Finset.offDiag A by ext; aesop]
    simp +decide [Finset.offDiag_card]
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [Nat.choose_two_right]
  grind

/-- If there are k distinct distances, the average frequency is at most n(n-1)/(2k). -/
theorem avg_frequency_bound (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (_hk : (distinctDistances A).card ≠ 0) :
    (distinctDistances A).sum (distFrequency A) / (distinctDistances A).card ≤
      A.card.choose 2 / (distinctDistances A).card := by
  exact Nat.div_le_div_right (total_pairs A)
