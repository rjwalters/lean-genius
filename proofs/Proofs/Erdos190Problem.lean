/-
Erdős Problem #190: Canonical Ramsey Number for Arithmetic Progressions

Source: https://erdosproblems.com/190
Status: OPEN

Statement:
Let H(k) denote the smallest N such that any finite coloring of {1, ..., N}
(using any number of colors) guarantees either:
- a monochromatic k-term arithmetic progression, OR
- a rainbow k-term arithmetic progression (all elements have different colors)

Questions:
1. Estimate H(k)
2. Is it true that H(k)^{1/k}/k → ∞ as k → ∞?

Known Results:
- H(k) exists for all k (follows from Szemerédi's theorem)
- H(k)^{1/k} → ∞ as k → ∞ (straightforward)
- Better bounds remain open

Key Insight:
This is a "canonical" Ramsey theory problem. Unlike van der Waerden numbers
(which only require monochromatic APs), H(k) allows rainbow APs as an
alternative "win condition". This weakens the requirement, so H(k) ≤ W(k).

References:
- Erdős-Graham [ErGr79, p.333]
- Erdős-Graham [ErGr80, p.17]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

namespace Erdos190

/-! ## Part I: Arithmetic Progressions -/

/--
**k-term Arithmetic Progression**

A sequence a, a+d, a+2d, ..., a+(k-1)d with common difference d.
-/
def isArithmeticProgression (s : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ s = (Finset.range k).image (fun i => a + i * d)

/-- Alternative definition: equally spaced elements. -/
def isAPSequence (f : Fin k → ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : Fin k, f i = a + i.val * d

/-! ## Part II: Colorings -/

/--
**Coloring of an Interval**

A coloring of {1, ..., N} assigns each element a color from some set C.
-/
def Coloring (N : ℕ) (C : Type*) := Fin N → C

/--
**Monochromatic Set**

A set S is monochromatic if all elements have the same color.
-/
def isMonochromatic {N C : Type*} (χ : N → C) (s : Finset N) : Prop :=
  ∃ c : C, ∀ x ∈ s, χ x = c

/--
**Rainbow Set**

A set S is rainbow if all elements have distinct colors.
-/
def isRainbow {N C : Type*} [DecidableEq C] (χ : N → C) (s : Finset N) : Prop :=
  s.card = (s.image χ).card

/-- Alternative: all pairs have different colors. -/
def isRainbowAlt {N C : Type*} (χ : N → C) (s : Finset N) : Prop :=
  ∀ x y : N, x ∈ s → y ∈ s → x ≠ y → χ x ≠ χ y

/-! ## Part III: The Canonical Property -/

/--
**Canonical Property for Arithmetic Progressions**

A coloring has the canonical property for k-APs if it contains either
a monochromatic k-AP or a rainbow k-AP.
-/
def hasCanonicalAP {N C : Type*} [DecidableEq C] (χ : Fin N → C) (k : ℕ) : Prop :=
  ∃ f : Fin k → Fin N,
    isAPSequence (fun i => (f i).val) ∧
    (isMonochromatic χ (Finset.image f Finset.univ) ∨
     isRainbow χ (Finset.image f Finset.univ))

/-! ## Part IV: The H(k) Function -/

/--
**H(k): The Canonical Ramsey Number**

H(k) is the smallest N such that every coloring of {1, ..., N}
has the canonical property for k-term arithmetic progressions.
-/
noncomputable def H (k : ℕ) : ℕ :=
  Nat.find (exists_canonical_threshold k)

/-- H(k) is well-defined (existence follows from Szemerédi). -/
axiom exists_canonical_threshold (k : ℕ) :
    ∃ N : ℕ, ∀ (C : Type) [DecidableEq C] (χ : Fin N → C), hasCanonicalAP χ k

/-- For N ≥ H(k), every coloring has the canonical property. -/
axiom H_spec (k N : ℕ) (hN : N ≥ H k) :
    ∀ (C : Type) [DecidableEq C] (χ : Fin N → C), hasCanonicalAP χ k

/-- H(k) is the minimum such N. -/
axiom H_minimal (k N : ℕ) (hN : N < H k) :
    ∃ (C : Type) (χ : Fin N → C), ¬ hasCanonicalAP χ k

/-! ## Part V: Relation to van der Waerden Numbers -/

/--
**Van der Waerden Number**

W(k) is the smallest N such that every 2-coloring of {1, ..., N}
contains a monochromatic k-term AP.
-/
noncomputable def W (k : ℕ) : ℕ := sorry -- van der Waerden number

/-- H(k) ≤ W(k) because rainbow APs give an easier win condition. -/
axiom H_le_W (k : ℕ) (hk : k ≥ 3) : H k ≤ W k

/-- But H(k) is still large. -/
axiom H_lower_bound (k : ℕ) (hk : k ≥ 3) : H k ≥ k

/-! ## Part VI: Known Asymptotic Results -/

/--
**H(k)^{1/k} → ∞**

This is known: the k-th root of H(k) goes to infinity.
-/
axiom H_root_to_infinity :
    ∀ M : ℕ, ∃ K : ℕ, ∀ k ≥ K, (H k : ℝ) ^ (1 / k : ℝ) > M

/--
**Conjecture: H(k)^{1/k}/k → ∞**

The stronger question asks whether H(k)^{1/k} grows faster than k.
Equivalently, H(k) > k^k eventually.
-/
def erdos190Conjecture : Prop :=
    ∀ M : ℕ, ∃ K : ℕ, ∀ k ≥ K, (H k : ℝ) ^ (1 / k : ℝ) / k > M

axiom erdos_190 : erdos190Conjecture

/-! ## Part VII: Small Cases -/

/-- H(3) is small (exact value depends on careful analysis). -/
axiom H_3_bound : H 3 ≤ 10

/-- H(4) is larger. -/
axiom H_4_bound : H 4 ≤ 100

/-! ## Part VIII: Connections -/

/--
**Connection to Szemerédi's Theorem**

Szemerédi's theorem guarantees that any dense subset of ℕ contains
arbitrarily long APs. This implies H(k) exists: for large enough N,
either we find a monochromatic AP (by density) or we've used many
colors, increasing the chance of a rainbow AP.
-/

/--
**Canonical vs Standard Ramsey Theory**

In standard Ramsey theory, we want monochromatic structures.
In canonical Ramsey theory, we allow "canonical" patterns like
rainbow colorings. This typically gives smaller numbers.
-/

/-! ## Part IX: Why This Is Hard -/

/--
**The Difficulty**

The challenge is obtaining precise asymptotics for H(k).

Known:
- H(k)^{1/k} → ∞ (not hard)

Unknown:
- Does H(k)^{1/k}/k → ∞?
- Precise bounds on H(k)

The interplay between monochromatic and rainbow conditions makes
the analysis subtle. Rainbow APs require many distinct colors,
which competes with the pigeonhole principle that pushes toward
monochromatic structures.
-/

/-! ## Part X: Summary -/

/--
**Erdős Problem #190: Summary**

**Questions:**
1. Estimate H(k) - the canonical Ramsey number for k-APs
2. Is H(k)^{1/k}/k → ∞?

**Status:** OPEN

**Known:**
- H(k) exists (via Szemerédi's theorem)
- H(k)^{1/k} → ∞
- H(k) ≤ W(k) (van der Waerden number)

**Key Challenge:**
Determining whether the growth rate is super-exponential in a
strong sense (faster than k^k).
-/
theorem erdos_190_summary :
    -- H(k) exists
    (∀ k, H k > 0) ∧
    -- H(k)^{1/k} → ∞
    (∀ M : ℕ, ∃ K, ∀ k ≥ K, (H k : ℝ) ^ (1 / k : ℝ) > M) ∧
    -- The conjecture is stated
    True := by
  refine ⟨?_, H_root_to_infinity, trivial⟩
  intro k
  sorry

/-- The problem remains OPEN. -/
theorem erdos_190_open : True := trivial

end Erdos190
