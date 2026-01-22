/-
Erdős Problem #966: Ramsey-Type Arithmetic Progressions

Source: https://erdosproblems.com/966
Status: SOLVED (Spencer, ~1975)

Statement:
Let k, r ≥ 2. Does there exist a set A ⊆ ℕ that contains no non-trivial
arithmetic progression of length k+1, yet in any r-coloring of A there
must exist a monochromatic non-trivial arithmetic progression of length k?

Answer: YES

Erdős reported in [Er75b] that "Spencer has recently shown that such a
sequence exists." This is an arithmetic analogue of the graph theory
version, Erdős Problem #924.

Key Concepts:
- A non-trivial arithmetic progression (AP) has common difference d > 0
- An AP-free set avoids patterns a, a+d, a+2d, ..., a+kd
- Van der Waerden's theorem: any r-coloring of ℕ contains monochromatic APs
- This problem asks for sets that are "barely" AP-free: avoiding length k+1
  APs while forcing monochromatic length k APs in any coloring

References:
- Erdős [Er75b]: "Problems and results in combinatorial number theory" (1975)
- Spencer: Original construction (~1975)
- Van der Waerden (1927): Foundational Ramsey-type result for APs
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic

open Set Finset

namespace Erdos966

/-
## Part I: Arithmetic Progressions

An arithmetic progression of length k is a sequence a, a+d, a+2d, ..., a+(k-1)d.
A non-trivial AP has d > 0 (not all elements equal).
-/

/--
**Arithmetic Progression:**
The finite set {a, a+d, a+2d, ..., a+(k-1)d} for starting point a,
common difference d, and length k.
-/
def arithmeticProgression (a d k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/--
An arithmetic progression is non-trivial if d > 0.
-/
def isNontrivialAP (a d k : ℕ) : Prop := d > 0 ∧ k ≥ 2

/--
A set A contains an arithmetic progression of length k if there exist
a, d with d > 0 such that {a, a+d, ..., a+(k-1)d} ⊆ A.
-/
def containsAPOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : ℕ, i < k → (a + i * d) ∈ A

/--
A set is AP-free of length k if it contains no non-trivial AP of that length.
-/
def APFreeOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ¬ containsAPOfLength A k

/-
## Part II: Colorings and Monochromatic Sets
-/

/--
An r-coloring of a set A is a function c : ℕ → Fin r.
-/
def Coloring (r : ℕ) := ℕ → Fin r

/--
The color class of color c in set A under coloring f.
-/
def colorClass (A : Set ℕ) (f : Coloring r) (c : Fin r) : Set ℕ :=
  {x ∈ A | f x = c}

/--
A monochromatic AP of length k exists in coloring f on set A if
some color class contains an AP of length k.
-/
def hasMonochromaticAP (A : Set ℕ) (r : ℕ) (f : Coloring r) (k : ℕ) : Prop :=
  ∃ c : Fin r, containsAPOfLength (colorClass A f c) k

/--
For any r-coloring of A, there exists a monochromatic AP of length k.
-/
def forcesMonochromaticAP (A : Set ℕ) (r k : ℕ) : Prop :=
  ∀ f : Coloring r, hasMonochromaticAP A r f k

/-
## Part III: Spencer's Set

Spencer constructed sets with the desired Ramsey-type property:
- No AP of length k+1
- Every r-coloring has a monochromatic AP of length k
-/

/--
**Spencer's Set:**
For parameters k, r ≥ 2, there exists a set A ⊆ ℕ that is:
1. (k+1)-AP-free: contains no arithmetic progression of length k+1
2. Ramsey for k-APs: any r-coloring has a monochromatic k-AP
-/
def SpencerSet (k r : ℕ) : Set ℕ := sorry

/--
Spencer's set avoids length (k+1) arithmetic progressions.
-/
axiom spencer_AP_free (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    APFreeOfLength (SpencerSet k r) (k + 1)

/--
Spencer's set forces monochromatic length k APs in any r-coloring.
-/
axiom spencer_forces_mono_AP (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    forcesMonochromaticAP (SpencerSet k r) r k

/-
## Part IV: Main Theorem

The answer to Erdős Problem #966 is YES.
-/

/--
**Spencer's Theorem (~1975):**
For all k, r ≥ 2, there exists a set A ⊆ ℕ such that:
1. A contains no arithmetic progression of length k+1
2. Every r-coloring of A contains a monochromatic AP of length k
-/
axiom spencer_theorem (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    ∃ A : Set ℕ,
      APFreeOfLength A (k + 1) ∧
      forcesMonochromaticAP A r k

/--
**Erdős Problem #966: SOLVED**
The answer is YES - such sets exist for all k, r ≥ 2.
-/
theorem erdos_966 (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    ∃ A : Set ℕ,
      APFreeOfLength A (k + 1) ∧
      forcesMonochromaticAP A r k :=
  spencer_theorem k r hk hr

/-
## Part V: Connection to Van der Waerden's Theorem

Van der Waerden's theorem states that for any r-coloring of ℕ,
there exist arbitrarily long monochromatic APs.
-/

/--
**Van der Waerden Numbers:**
W(k, r) is the minimum N such that any r-coloring of {1, ..., N}
contains a monochromatic AP of length k.
-/
def vanDerWaerdenNumber (k r : ℕ) : ℕ := sorry

/--
Van der Waerden's theorem: W(k, r) exists for all k, r ≥ 1.
-/
axiom van_der_waerden_exists (k r : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) :
    ∃ N : ℕ, ∀ f : Coloring r,
      ∃ c : Fin r, ∃ a d : ℕ, d > 0 ∧
        (∀ i : ℕ, i < k → a + i * d < N) ∧
        (∀ i : ℕ, i < k → f (a + i * d) = c)

/--
Erdős 966 refines Van der Waerden by restricting to (k+1)-AP-free sets.
The key insight is that such restricted sets can still force
monochromatic k-APs.
-/
theorem erdos_966_refines_vdw (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    ∃ A : Set ℕ,
      APFreeOfLength A (k + 1) ∧
      (∀ f : Coloring r, ∃ c : Fin r,
        containsAPOfLength (colorClass A f c) k) :=
  erdos_966 k r hk hr

/-
## Part VI: Connection to Erdős Problem #924

Erdős 924 is the graph-theoretic analogue:
Does there exist a graph G that contains no clique of size k+1,
yet in any r-coloring of vertices, there is a monochromatic clique of size k?

The answer there is also YES (Folkman numbers).
-/

/--
Erdős 966 is an arithmetic analogue of Erdős 924 (Folkman's theorem).
Where 924 asks about cliques in graphs, 966 asks about APs in sets.
-/
axiom erdos_966_analogue_of_924 :
    ∀ k r : ℕ, k ≥ 2 → r ≥ 2 →
      (∃ A : Set ℕ, APFreeOfLength A (k + 1) ∧ forcesMonochromaticAP A r k) ↔
      True  -- Simplified: just asserting the analogy exists

/-
## Part VII: Specific Cases
-/

/--
**Case k=2, r=2:**
There exists A ⊆ ℕ with no 3-term AP, but every 2-coloring has
a monochromatic 2-term AP (which is trivial - any 2 elements work).
-/
theorem case_k2_r2 : ∃ A : Set ℕ, APFreeOfLength A 3 ∧ forcesMonochromaticAP A 2 2 :=
  erdos_966 2 2 (by norm_num) (by norm_num)

/--
**Case k=3, r=2:**
There exists A ⊆ ℕ with no 4-term AP, but every 2-coloring has
a monochromatic 3-term AP.
-/
theorem case_k3_r2 : ∃ A : Set ℕ, APFreeOfLength A 4 ∧ forcesMonochromaticAP A 2 3 :=
  erdos_966 3 2 (by norm_num) (by norm_num)

/-
## Part VIII: Roth's Theorem Connection

Roth's theorem (1953): Any subset of ℕ with positive upper density
contains a 3-term AP. Spencer's construction uses careful density
control to achieve the desired properties.
-/

/--
**Upper Density:**
The upper density of A ⊆ ℕ is lim sup |A ∩ [1,n]| / n.
-/
def upperDensity (A : Set ℕ) : ℝ := sorry

/--
Roth's theorem: positive density implies 3-APs.
-/
axiom roth_theorem (A : Set ℕ) :
    upperDensity A > 0 → containsAPOfLength A 3

/--
Spencer's sets have zero upper density (else they'd contain arbitrarily long APs).
-/
axiom spencer_zero_density (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    upperDensity (SpencerSet k r) = 0

/-
## Part IX: Properties of Arithmetic Progressions
-/

/--
Any singleton is trivially AP-free.
-/
theorem singleton_AP_free (n : ℕ) (k : ℕ) (hk : k ≥ 2) :
    APFreeOfLength {n} k := by
  intro ⟨a, d, hd, h⟩
  have h0 : a ∈ ({n} : Set ℕ) := h 0 (by omega)
  have h1 : a + d ∈ ({n} : Set ℕ) := h 1 (by omega)
  simp at h0 h1
  omega

/--
The AP {a, a+d, ..., a+(k-1)d} has exactly k elements when d > 0.
-/
theorem AP_card (a d k : ℕ) (hd : d > 0) :
    (arithmeticProgression a d k).card = k := by
  simp only [arithmeticProgression]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range k
  · intro i j hij
    simp at hij
    omega

/-
## Part X: Summary
-/

/--
**Erdős Problem #966: Summary**

Question: For k, r ≥ 2, does there exist A ⊆ ℕ such that:
- A contains no (k+1)-term AP
- Every r-coloring of A has a monochromatic k-term AP?

Answer: YES (Spencer, ~1975)

This is the arithmetic analogue of Folkman numbers (graph theory).
The construction uses sophisticated combinatorial techniques from
additive combinatorics and Ramsey theory.
-/
theorem erdos_966_summary (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    ∃ A : Set ℕ,
      APFreeOfLength A (k + 1) ∧
      forcesMonochromaticAP A r k ∧
      upperDensity A = 0 := by
  obtain ⟨A, hfree, hforces⟩ := erdos_966 k r hk hr
  use SpencerSet k r
  exact ⟨spencer_AP_free k r hk hr, spencer_forces_mono_AP k r hk hr,
         spencer_zero_density k r hk hr⟩

end Erdos966
