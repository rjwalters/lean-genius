/-
Erdős Problem #1204: Admissible Sequences

We call a sequence of integers 0 ≤ a₁ < ⋯ < a_k *admissible* if it is missing
at least one congruence class modulo every prime p. (This is exactly the
notion of an "admissible k-tuple" from the Hardy–Littlewood prime k-tuples
conjecture and the bounded-gaps-between-primes work of Zhang, Maynard, Tao.)

Let A(k) = min a_k over admissible k-element sequences.

**Main Questions (OPEN)**:
1. Estimate A(k). In particular, is it true that A(k) ∼ k log k?
2. Estimate B(k) = min (a₁ + ⋯ + a_k)/k.

**What is formalized here**:
- `Admissible`: a finite set of naturals misses a residue class mod every prime.
- `missing_class_of_card_lt`: a set of size < p always misses a class mod p
  (only `card` distinct residues can be occupied, and there are `p` of them).
- `admissible_iff_card`: **the key reduction** — admissibility is equivalent to
  missing a class modulo every prime `p ≤ card`; all larger primes are automatic.
- Worked examples: `∅`, `{0}`, `{0,2}` are admissible; `{0,1}` is not (it covers
  both classes mod 2).

The asymptotic questions A(k) ∼ k log k and the estimate for B(k) are OPEN and
are not asserted here.

Reference: https://erdosproblems.com/1204
-/

import Mathlib

open Finset

namespace Erdos1204

/- ## Definition -/

/-- A finite set `a ⊆ ℕ` is **admissible** if, for every prime `p`, it misses at
least one residue class modulo `p`: there is some `r : ZMod p` not equal to `↑x`
for any `x ∈ a`. -/
def Admissible (a : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ x ∈ a, (x : ZMod p) ≠ r

/- ## The reduction to small primes

The content of admissibility lies entirely in the small primes `p ≤ |a|`. For a
prime `p` larger than `|a|`, the `|a|` elements occupy at most `|a| < p` of the
`p` residue classes, so some class is automatically missed. -/

/-- A set with fewer than `p` elements always misses a residue class modulo `p`:
its image in `ZMod p` cannot be all of `ZMod p`. -/
theorem missing_class_of_card_lt {a : Finset ℕ} {p : ℕ} [NeZero p]
    (h : a.card < p) : ∃ r : ZMod p, ∀ x ∈ a, (x : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ r, ∃ x ∈ a, (x : ZMod p) = r, i.e. the image is all of ZMod p
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ a.image (fun x : ℕ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have hle : (Finset.univ : Finset (ZMod p)).card ≤ a.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card p] at hle
  omega

/-- **Key reduction.** A finite set is admissible iff it misses a residue class
modulo every prime `p` that is at most its cardinality. Larger primes impose no
constraint. -/
theorem admissible_iff_card {a : Finset ℕ} :
    Admissible a ↔
      ∀ p : ℕ, p.Prime → p ≤ a.card → ∃ r : ZMod p, ∀ x ∈ a, (x : ZMod p) ≠ r := by
  constructor
  · intro ha p hp _; exact ha p hp
  · intro h p hp
    rcases le_or_gt p a.card with hle | hlt
    · exact h p hp hle
    · haveI : NeZero p := ⟨hp.pos.ne'⟩
      exact missing_class_of_card_lt hlt

/- ## Examples -/

/-- The empty set is admissible (it misses every class). -/
theorem admissible_empty : Admissible (∅ : Finset ℕ) :=
  fun p _ => ⟨0, by simp⟩

/-- Every singleton is admissible: with only one element occupied there is
nothing to check below `p = 2`, and `missing_class_of_card_lt` handles the rest. -/
theorem admissible_singleton (n : ℕ) : Admissible ({n} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  rw [Finset.card_singleton] at hcard
  -- p ≤ 1 contradicts p prime (p ≥ 2)
  have := hp.two_le
  exfalso; omega

/-- `{0, 2}` is admissible: modulo 2 both elements are even, so the odd class
is missed; modulo every larger prime the size bound applies. This is the
smallest nontrivial admissible 2-tuple. -/
theorem admissible_zero_two : Admissible ({0, 2} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  -- card {0,2} = 2, so the only prime to check is p = 2
  have hc : ({0, 2} : Finset ℕ).card = 2 := by decide
  rw [hc] at hcard
  interval_cases p
  · exact absurd hp (by decide)   -- p = 0
  · exact absurd hp (by decide)   -- p = 1
  · -- p = 2: miss the class 1
    refine ⟨1, ?_⟩
    intro x hx
    fin_cases hx <;> decide

/-- `{0, 1}` is **not** admissible: modulo 2 it occupies both residue classes,
so no class is missed. -/
theorem not_admissible_zero_one : ¬ Admissible ({0, 1} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr⟩ := h 2 (by decide)
  -- both residue classes 0 and 1 mod 2 are occupied, so no r is missed
  fin_cases r
  · exact (hr 0 (by decide)) (by decide)
  · exact (hr 1 (by decide)) (by decide)

/- ## Open Problems

The asymptotic behaviour of the extremal quantities is OPEN:

- **A(k)** = min a_k over admissible k-element sequences `0 ≤ a₁ < ⋯ < a_k`.
  Is A(k) ∼ k log k? (The prime k-tuples heuristic suggests the minimal
  diameter of an admissible k-tuple is ∼ k log k.)
- **B(k)** = min (a₁ + ⋯ + a_k)/k over admissible k-element sequences.
  Estimate B(k).

These require analytic number theory (sieve methods, distribution of primes in
residue classes) and are not formalized here.
-/

end Erdos1204
