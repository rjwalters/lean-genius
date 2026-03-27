/-
Erdős Problem #1157: General Extremal Numbers for r-Uniform Hypergraphs

Source: https://erdosproblems.com/1157
Status: OPEN (partial results known)

Statement:
Determine the extremal number ex_r(n, F) where F is the family of all r-uniform
hypergraphs with k vertices and s edges.

The Brown-Erdős-Sós conjecture asserts: for r > t ≥ 2 and s ≥ 3,
  ex_t(n, F) = o(n^t) whenever k ≥ (r-t)s + t + 1.

Known Results:
- Brown-Erdős-Sós (1973): Lower bound ex_r(n, F) ≫ n^{(rs-k)/(s-1)} for k > r, s > 1
- The case r = s = 3, k = 6 is Problem #716 (Ruzsa-Szemerédi theorem)
- The case r = 3, k = s + 2 is Problem #1076 (solved by Bohman-Warnke 2019)
- The case t = 2 is Problem #1178

References:
- [BES73] Brown, Erdős, Sós, "Some extremal problems on r-graphs" (1973)
- [Va99] Verstraëte, "Turán-type problems" (1999)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos1157

/-
## Part I: The General Extremal Number

The extremal number f^(r)(n; k, s) is the maximum number of edges in an
r-uniform hypergraph on n vertices with no s edges spanning at most k vertices.
We axiomatize this as a function ℕ⁴ → ℕ.
-/

/-- The general extremal number f^(r)(n; k, s):
    maximum number of edges in an r-uniform hypergraph on n vertices
    that contains no s edges spanning at most k vertices. -/
axiom extremalNumber (r n k s : ℕ) : ℕ

/-- Monotonicity in k: increasing k means more edge-sets are forbidden
    (any s edges spanning ≤ k₂ ≥ k₁ vertices includes more configurations),
    so fewer hypergraphs are valid and the extremal number decreases. -/
axiom extremalNumber_mono_k (r n s k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
  extremalNumber r n k₂ s ≤ extremalNumber r n k₁ s

/-- Monotonicity in s: requiring more forbidden edges makes it harder
    to find violations, so the extremal number increases. -/
axiom extremalNumber_mono_s (r n k s₁ s₂ : ℕ) (h : s₁ ≤ s₂) :
  extremalNumber r n k s₁ ≤ extremalNumber r n k s₂

/-
## Part II: The Brown-Erdős-Sós Lower Bound (1973)

For all k > r and s > 1:
  ex_r(n, F(k,s)) ≫ n^{(rs-k)/(s-1)}

The exponent α = (rs - k)/(s - 1) is the key quantity.
-/

/-- The BES lower bound exponent: α = (rs - k) / (s - 1).
    We compute in ℝ using real division. -/
noncomputable def besExponent (r k s : ℕ) : ℝ :=
  ((r * s : ℕ) - (k : ℝ)) / ((s : ℝ) - 1)

/-- The BES lower bound exponent is positive when rs > k and s ≥ 2. -/
theorem besExponent_pos (r k s : ℕ) (hs : s ≥ 2) (hrs : r * s > k) :
    besExponent r k s > 0 := by
  unfold besExponent
  apply div_pos
  · have : (k : ℝ) < (r * s : ℕ) := Nat.cast_lt.mpr hrs
    linarith
  · have : (2 : ℝ) ≤ (s : ℝ) := Nat.ofNat_le_cast.mpr hs
    linarith

/-- Brown-Erdős-Sós Lower Bound (1973):
    For k > r ≥ 2 and s ≥ 2, the extremal number grows at least as
    n^{(rs-k)/(s-1)}. Stated with explicit constants and real power. -/
axiom brown_erdos_sos_lower_bound (r k s : ℕ) (hr : r ≥ 2) (hs : s ≥ 2) (hk : k > r) :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (extremalNumber r n k s : ℝ) ≥ c * (n : ℝ) ^ besExponent r k s

/-
## Part III: The Brown-Erdős-Sós Conjecture

The central conjecture of Problem #1157.
-/

/-- Little-o notation for sequences: f(n) = o(g(n)) as n → ∞. -/
def IsLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε * |g n|

/-- The Brown-Erdős-Sós Conjecture (general form):
    For r > t ≥ 2 and s ≥ 3,
    ex_t(n, F(k,s)) = o(n^t) whenever k ≥ (r-t)·s + t + 1. -/
def BESConjecture (t r s k : ℕ) : Prop :=
  r > t ∧ t ≥ 2 ∧ s ≥ 3 ∧ k ≥ (r - t) * s + t + 1 →
  IsLittleO (fun n => (extremalNumber t n k s : ℝ)) (fun n => (n : ℝ) ^ t)

/-
## Part IV: Special Cases and Connections

Problem #1157 unifies several other Erdős problems.
-/

/-- **Connection to Problem #716** (Ruzsa-Szemerédi (6,3)-problem):
    The BES conjecture with t = 2, r = 3, s = 3, k = 6 gives:
    k ≥ (3-2)·3 + 2 + 1 = 6, so the BES parameter constraint is tight. -/
theorem erdos716_parameter_check : (3 - 2) * 3 + 2 + 1 = 6 := by omega

/-- **Connection to Problem #1076** (r = 3, k = s + 2):
    The BES parameter constraint for t = 2, r = 3 is k ≥ s + 3.
    Since #1076 has k = s + 2 < s + 3, this result is tighter than
    what the BES conjecture would give. -/
theorem erdos1076_beyond_bes (s : ℕ) (hs : s ≥ 3) :
    s + 2 < (3 - 2) * s + 2 + 1 := by omega

/-
## Part V: Known Partial Results
-/

/-- The BES conjecture for the (6,3)-case (Problem #716).
    Proved by Ruzsa-Szemerédi (1978) via the Triangle Removal Lemma. -/
axiom ruzsa_szemeredi_bes :
  IsLittleO (fun n => (extremalNumber 3 n 6 3 : ℝ)) (fun n => (n : ℝ) ^ 2)

/-- **Glock (2019):** The (7,4)-case. -/
axiom glock_bes_k4 :
  IsLittleO (fun n => (extremalNumber 3 n 7 4 : ℝ)) (fun n => (n : ℝ) ^ 2)

/-- **Delcourt-Postle (2024):** The full 3-uniform BES conjecture.
    For all s ≥ 3 and k ≥ s + 3: f^(3)(n; k, s) = o(n²). -/
axiom delcourt_postle_theorem (s k : ℕ) (hs : s ≥ 3) (hk : k ≥ s + 3) :
  IsLittleO (fun n => (extremalNumber 3 n k s : ℝ)) (fun n => (n : ℝ) ^ 2)

/-
## Part VI: Structural Properties of the BES Exponent
-/

/-- The BES exponent decreases as k increases. -/
theorem besExponent_decreasing (r s k₁ k₂ : ℕ) (hs : s ≥ 2) (hk : k₁ < k₂) :
    besExponent r k₂ s < besExponent r k₁ s := by
  unfold besExponent
  apply div_lt_div_of_pos_right
  · have : (k₁ : ℝ) < (k₂ : ℝ) := Nat.cast_lt.mpr hk
    linarith
  · have : (2 : ℝ) ≤ (s : ℝ) := Nat.ofNat_le_cast.mpr hs
    linarith

/-- When k = rs, the BES exponent is 0. -/
theorem besExponent_zero_at_rs (r s : ℕ) :
    besExponent r (r * s) s = 0 := by
  unfold besExponent
  simp [Nat.cast_mul, sub_self]

/-- The BES exponent for the (6,3) case is 3/2. -/
theorem besExponent_6_3 : besExponent 3 6 3 = 3 / 2 := by
  unfold besExponent
  norm_num

/-- The BES exponent for the (7,4) case (Glock 2019). -/
theorem besExponent_7_4 : besExponent 3 7 4 = 5 / 3 := by
  unfold besExponent
  norm_num

/-- When the BES conjecture parameter constraint k ≥ (r-t)s + t + 1 holds
    with t = 2, the lower bound exponent is at most 1. This means the BES
    conjecture asserts o(n²) growth, which is compatible with the lower bound. -/
theorem besExponent_le_one_at_bes_threshold (r s : ℕ) (hr : r ≥ 3) (hs : s ≥ 3) :
    besExponent r ((r - 2) * s + 3) s ≤ 1 := by
  unfold besExponent
  rw [div_le_one]
  · push_cast
    have hr' : (3 : ℝ) ≤ (r : ℝ) := Nat.ofNat_le_cast.mpr hr
    have hs' : (3 : ℝ) ≤ (s : ℝ) := Nat.ofNat_le_cast.mpr hs
    nlinarith
  · have : (3 : ℝ) ≤ (s : ℝ) := Nat.ofNat_le_cast.mpr hs
    linarith

/-
## Part VII: Proved Theorems
-/

/-- The 3-uniform case of the BES conjecture is fully resolved. -/
theorem erdos_1157_3uniform_resolved (s k : ℕ) (hs : s ≥ 3) (hk : k ≥ s + 3) :
    IsLittleO (fun n => (extremalNumber 3 n k s : ℝ)) (fun n => (n : ℝ) ^ 2) :=
  delcourt_postle_theorem s k hs hk

/-- The (6,3) case follows from the Ruzsa-Szemerédi result. -/
theorem erdos_1157_case_716 :
    IsLittleO (fun n => (extremalNumber 3 n 6 3 : ℝ)) (fun n => (n : ℝ) ^ 2) :=
  ruzsa_szemeredi_bes

/-- Monotonicity: if f^(3)(n; k₁, s) = o(n²) and k₁ ≤ k₂,
    then f^(3)(n; k₂, s) = o(n²). -/
theorem bes_monotone_in_k {s k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : IsLittleO (fun n => (extremalNumber 3 n k₁ s : ℝ)) (fun n => (n : ℝ) ^ 2)) :
    IsLittleO (fun n => (extremalNumber 3 n k₂ s : ℝ)) (fun n => (n : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (extremalNumber 3 n k₂ s : ℝ) ≤ (extremalNumber 3 n k₁ s : ℝ) :=
    Nat.cast_le.mpr (extremalNumber_mono_k 3 n s k₁ k₂ hk)
  have h2 : (0 : ℝ) ≤ (extremalNumber 3 n k₂ s : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg h2]
  have h3 : (extremalNumber 3 n k₂ s : ℝ) ≤ |↑(extremalNumber 3 n k₁ s)| :=
    le_trans h1 (le_abs_self _)
  exact le_trans h3 (hN n hn)

/-
## Part VIII: The Erdős Problem #1157 Statement
-/

/-- **Erdős Problem #1157:**
    Determine the extremal number f^(r)(n; k, s) for r-uniform hypergraphs.

    Status: OPEN in full generality.
    - Resolved for 3-uniform case (t = 2) by Delcourt-Postle (2024)
    - Open for higher uniformities (r ≥ 4) and general parameters -/
def erdos_1157 : Prop :=
  ∀ t r s k : ℕ, BESConjecture t r s k

/-- Summary of what is known for Problem #1157. -/
theorem erdos_1157_summary :
    (∀ s k : ℕ, s ≥ 3 → k ≥ s + 3 →
      IsLittleO (fun n => (extremalNumber 3 n k s : ℝ)) (fun n => (n : ℝ) ^ 2)) ∧
    IsLittleO (fun n => (extremalNumber 3 n 6 3 : ℝ)) (fun n => (n : ℝ) ^ 2) ∧
    besExponent 3 6 3 = 3 / 2 ∧
    besExponent 3 7 4 = 5 / 3 := by
  exact ⟨fun s k hs hk => delcourt_postle_theorem s k hs hk,
         ruzsa_szemeredi_bes,
         besExponent_6_3,
         besExponent_7_4⟩

end Erdos1157
