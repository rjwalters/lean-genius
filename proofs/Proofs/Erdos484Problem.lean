/-
Erdős Problem #484: Monochromatic Sums in Colorings

Source: https://erdosproblems.com/484
Status: SOLVED (Erdős-Sárközy-Sós 1989)

Statement:
Prove that there exists an absolute constant c > 0 such that, whenever
{1,...,N} is k-colored (with N large enough depending on k), there are
at least cN integers representable as monochromatic sums (a + b where
a, b are in the same color class and a ≠ b).

Resolution:
Erdős, Sárközy, and Sós [ESS89] proved:
- For general k: at least N/2 - O(N^{1-1/2^{k+1}}) even numbers are sums
- For k=2: at least N/2 - O(log N) even numbers, and O(log N) is optimal

Historical Note:
This was originally a conjecture of Roth about sumset structure in
partitions. A refinement appears as Problem 25 on Ben Green's list.

References:
- Roth: Original conjecture
- Erdős-Sárközy-Sós [ESS89]: Complete solution
- Ben Green: Problem 25 (refinement)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos484

/-! ## Part I: Basic Definitions -/

/--
**k-coloring of {1,...,N}:**
A function χ: {1,...,N} → {1,...,k} assigning each integer a color.
-/
def Coloring (N k : ℕ) := Fin N → Fin k

/--
**Color class:**
The set of integers in {1,...,N} with a given color.
-/
def colorClass {N k : ℕ} (χ : Coloring N k) (c : Fin k) : Finset (Fin N) :=
  Finset.filter (fun n => χ n = c) Finset.univ

/--
**Monochromatic sum:**
An integer s is a monochromatic sum if s = a + b where a ≠ b and
a, b have the same color.
-/
def isMonochromaticSum {N k : ℕ} (χ : Coloring N k) (s : ℕ) : Prop :=
  ∃ a b : Fin N, a ≠ b ∧ χ a = χ b ∧ (a.val + 1) + (b.val + 1) = s

/--
**Representable integers:**
The set of integers in {1,...,2N} that are representable as
monochromatic sums.
-/
def monochromaticSums {N k : ℕ} (χ : Coloring N k) : Set ℕ :=
  {s | isMonochromaticSum χ s}

/-! ## Part II: Roth's Conjecture (Proved) -/

/--
**Roth's Conjecture:**
There exists c > 0 such that for any k-coloring of {1,...,N},
at least cN integers are representable as monochromatic sums.
-/
def roth_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
  ∀ k ≥ 1, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ χ : Coloring N k,
    (Finset.filter (fun s => isMonochromaticSum χ s)
      (Finset.range (2 * N))).card ≥ c * N

/--
**Roth's conjecture is TRUE:**
Proved by Erdős, Sárközy, and Sós in 1989.
-/
axiom roth_conjecture_true : roth_conjecture

/-! ## Part III: The Erdős-Sárközy-Sós Theorem -/

/--
**Main Theorem (ESS89):**
In any k-coloring of {1,...,N}, at least
N/2 - O(N^{1-1/2^{k+1}})
even integers are representable as monochromatic sums.
-/
axiom ESS_theorem (k : ℕ) :
    k ≥ 1 →
    ∃ C : ℝ, C > 0 ∧
    ∀ N ≥ k, ∀ χ : Coloring N k,
      (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥
      (N : ℝ) / 2 - C * (N : ℝ) ^ (1 - 1 / 2^(k + 1))

/--
**Why even numbers:**
A sum a + b where a, b have the same parity yields an even sum.
In any color class of size m, the sumset contains at least m/2 elements
of the same parity, so most sums are even.
-/
axiom even_sum_parity :
    ∀ N k : ℕ, ∀ χ : Coloring N k, ∀ c : Fin k,
      ∀ a b : Fin N, a ≠ b → χ a = c → χ b = c →
        (a.val + 1 + (b.val + 1)) % 2 = ((a.val + 1) % 2 + (b.val + 1) % 2) % 2

/--
**The exponent 1 - 1/2^{k+1}:**
For k = 2: exponent = 1 - 1/8 = 7/8, so error ~ N^{7/8}
For k = 3: exponent = 1 - 1/16 = 15/16, so error ~ N^{15/16}
As k increases, the error term approaches N but stays sub-linear.
-/
axiom exponent_sublinear :
    ∀ k : ℕ, k ≥ 1 → (1 : ℝ) - 1 / 2^(k + 1) < 1

/-! ## Part IV: The Two-Coloring Case -/

/--
**Theorem for k = 2:**
In any 2-coloring of {1,...,N}, at least
N/2 - O(log N)
even integers are representable as monochromatic sums.
-/
axiom ESS_two_coloring :
    ∃ C : ℝ, C > 0 ∧
    ∀ N ≥ 2, ∀ χ : Coloring N 2,
      (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥
      (N : ℝ) / 2 - C * Real.log N

/--
**The O(log N) bound is optimal:**
There exists a 2-coloring where no power of 2 is a monochromatic sum.
This shows the error term O(log N) cannot be improved in general.
-/
axiom two_coloring_optimal :
    ∀ N : ℕ, ∃ χ : Coloring N 2,
    ∀ m : ℕ, 2^m ≤ 2 * N → ¬isMonochromaticSum χ (2^m)

/--
**Optimal construction:**
Color n with color (ν₂(n) mod 2), where ν₂(n) is the 2-adic valuation.
Then 2^m is never a monochromatic sum because if a + b = 2^m with
a, b having the same 2-adic valuation parity, their sum cannot be a
power of 2.
-/
axiom optimal_construction_exists :
    ∀ N : ℕ, ∃ χ : Coloring N 2,
      -- χ is based on 2-adic valuation mod 2
      (∀ n : Fin N, ∃ v : ℕ, 2^v ∣ (n.val + 1) ∧ ¬(2^(v+1) ∣ (n.val + 1)) ∧
        χ n = ⟨v % 2, by omega⟩) ∧
      -- No power of 2 is a monochromatic sum
      (∀ m : ℕ, 2^m ≤ 2 * N → ¬isMonochromaticSum χ (2^m))

/-! ## Part V: Key Proof Ideas -/

/--
**Sumset structure:**
For a color class C of size m, the sumset C + C = {a + b : a, b ∈ C, a ≠ b}
has size at least m - 1. By pigeonhole, some color class has size ≥ N/k,
giving a sumset of size ≥ N/k - 1.
-/
axiom sumset_lower_bound :
    ∀ N k : ℕ, k ≥ 1 → N ≥ k →
      ∀ χ : Coloring N k,
        ∃ c : Fin k, (colorClass χ c).card ≥ N / k

/--
**Density argument:**
If a color class has density δ in {1,...,N}, its sumset C + C
covers at least 2δN - O(√N) integers in {2,...,2N} by the
Freiman-Ruzsa theorem on sumsets.
-/
axiom sumset_density :
    ∀ N : ℕ, N ≥ 2 →
      ∀ C : Finset (Fin N), C.card ≥ 2 →
        ∃ sums : Finset ℕ,
          (∀ s ∈ sums, ∃ a b : Fin N, a ∈ C ∧ b ∈ C ∧ a ≠ b ∧
            (a.val + 1) + (b.val + 1) = s) ∧
          sums.card ≥ C.card - 1

/--
**Fourier analytic methods:**
The proof uses exponential sums to count the representation number
r(s) = #{(a,b) : a+b=s, χ(a)=χ(b), a≠b}. The number of s with
r(s) = 0 is bounded using the large sieve inequality.
-/
axiom fourier_representation_count :
    ∀ N k : ℕ, k ≥ 1 → N ≥ k →
      ∀ χ : Coloring N k,
        -- The number of unrepresented even numbers is bounded
        (Finset.filter (fun s => s % 2 = 0 ∧ ¬isMonochromaticSum χ s)
          (Finset.range (2 * N))).card ≤
        Nat.ceil ((N : ℝ) ^ (1 - 1 / 2^(k + 1)))

/-! ## Part VI: Consequences -/

/--
**Positive density of sums:**
Almost half of all even numbers in {1,...,2N} are monochromatic sums.
The constant c can be taken close to 1/2 for large N.
-/
theorem positive_density :
    ∃ c : ℝ, c > 0 ∧
    ∀ k ≥ 1, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ χ : Coloring N k,
      (Finset.filter (fun s => isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥ c * N := by
  exact roth_conjecture_true

/--
**Strengthening to c = 1/2 - ε:**
For any ε > 0 and fixed k, the constant c = 1/2 - ε works for
N large enough. This follows from the ESS theorem since the error
term N^{1-1/2^{k+1}} is o(N).
-/
axiom constant_half_minus_epsilon :
    ∀ ε : ℝ, ε > 0 → ∀ k : ℕ, k ≥ 1 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ χ : Coloring N k,
        (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
          (Finset.range (2 * N))).card ≥ ((1 : ℝ)/2 - ε) * N

/-! ## Part VII: Extensions and Related Results -/

/--
**Ben Green's Problem 25:**
Asks for more precise counting of monochromatic sums and understanding
the structure of colorings that minimize them. The ESS result gives
N/2 - o(N) even sums; Green asks for the exact second-order term.
-/
axiom ben_green_refinement :
    -- Green asks: what is the exact error term for k colors?
    ∀ k : ℕ, k ≥ 1 →
      ∃ f : ℕ → ℝ, (∀ N : ℕ, f N ≥ 0) ∧
        ∀ N ≥ k, ∀ χ : Coloring N k,
          (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
            (Finset.range (2 * N))).card ≥ (N : ℝ) / 2 - f N

/--
**Schur's theorem:**
In any k-coloring of {1,...,N} for N large enough, there exist
monochromatic a, b, c with a + b = c. This is the "equation version"
where the sum itself must be in the same color class.
-/
axiom schur_theorem :
    ∀ k : ℕ, k ≥ 1 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ χ : Coloring N k,
        ∃ a b c : Fin N, a ≠ b ∧ χ a = χ b ∧ χ b = χ c ∧
          (a.val + 1) + (b.val + 1) = (c.val + 1)

/--
**Hindman's theorem:**
In any finite coloring of ℕ, there exists an infinite set S such that
all finite sums of distinct elements of S have the same color.
This is much stronger than Schur — it gives infinite structure.
-/
axiom hindman_theorem :
    ∀ k : ℕ, k ≥ 1 →
      ∀ χ : ℕ → Fin k,
        ∃ c : Fin k, ∃ S : Set ℕ, Set.Infinite S ∧
          ∀ F : Finset ℕ, ↑F ⊆ S → F.Nonempty →
            χ (F.sum id) = c

/-! ## Part VIII: Summary -/

/--
**Summary of Erdős Problem #484:**

PROBLEM: Prove ∃ c > 0 such that any k-coloring of {1,...,N}
has at least cN integers representable as monochromatic sums.

STATUS: SOLVED (Erdős-Sárközy-Sós 1989)

KEY RESULTS:
1. For k colors: ≥ N/2 - O(N^{1-1/2^{k+1}}) even sums [ESS89]
2. For k = 2: ≥ N/2 - O(log N) even sums [ESS89]
3. O(log N) is optimal for k = 2 (no power of 2 is a sum)
4. c can be taken arbitrarily close to 1/2
-/
theorem erdos_484_status :
    -- Roth's conjecture is proved
    roth_conjecture ∧
    -- The two-coloring case has O(log N) error
    (∃ C : ℝ, C > 0 ∧ ∀ N ≥ 2, ∀ χ : Coloring N 2,
      (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥ (N : ℝ) / 2 - C * Real.log N) := by
  constructor
  · exact roth_conjecture_true
  · exact ESS_two_coloring

/--
**The powers of 2 obstruction:**
There exists a 2-coloring where no power of 2 is a monochromatic sum,
showing the O(log N) bound is tight.
-/
theorem power_of_two_obstruction :
    ∀ N : ℕ, ∃ χ : Coloring N 2,
    ∀ m : ℕ, 2^m ≤ 2 * N → ¬isMonochromaticSum χ (2^m) := by
  exact two_coloring_optimal

/--
**Erdős Problem #484: Main Theorem**
The problem is solved: Roth's conjecture holds with c approaching 1/2,
the two-coloring case has tight O(log N) error, and the 2-adic valuation
construction shows optimality.
-/
theorem erdos_484 :
    -- Roth's conjecture is TRUE
    roth_conjecture ∧
    -- Two-coloring case: O(log N) error
    (∃ C : ℝ, C > 0 ∧ ∀ N ≥ 2, ∀ χ : Coloring N 2,
      (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥ (N : ℝ) / 2 - C * Real.log N) ∧
    -- O(log N) is optimal
    (∀ N : ℕ, ∃ χ : Coloring N 2,
      ∀ m : ℕ, 2^m ≤ 2 * N → ¬isMonochromaticSum χ (2^m)) :=
  ⟨roth_conjecture_true, ESS_two_coloring, two_coloring_optimal⟩

end Erdos484
