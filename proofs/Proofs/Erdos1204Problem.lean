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

/- ## Structural properties

Admissibility is closed downward and is invariant under translation, and admissible
`k`-tuples exist for every `k` — so the extremal quantity `A(k)` is well-defined. -/

/-- **Downward closure.** Any subset of an admissible set is admissible: a residue class
missed by `a` mod `p` is still missed by any subset of `a`. -/
theorem Admissible.subset {a b : Finset ℕ} (ha : Admissible a) (hba : b ⊆ a) :
    Admissible b := by
  intro p hp
  obtain ⟨r, hr⟩ := ha p hp
  exact ⟨r, fun x hx => hr x (hba hx)⟩

/-- **Translation invariance.** Translating every element by a fixed `t` preserves
admissibility: if `a` misses class `r` modulo `p`, then `a + t` misses class `r + t`.
Admissibility depends only on the *pattern* of a tuple, not its position. -/
theorem admissible_image_add {a : Finset ℕ} (t : ℕ) (ha : Admissible a) :
    Admissible (a.image (· + t)) := by
  intro p hp
  obtain ⟨r, hr⟩ := ha p hp
  refine ⟨r + (t : ZMod p), fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hx' := hr x hx
  push_cast
  exact fun h => hx' (add_right_cancel h)

/-- Translation by a fixed `t` is injective, so it preserves cardinality: it sends
admissible `k`-tuples to admissible `k`-tuples. -/
theorem card_image_add (a : Finset ℕ) (t : ℕ) :
    (a.image (· + t)).card = a.card :=
  Finset.card_image_of_injective _ (add_left_injective t)

/-- **Existence / well-definedness of `A(k)`.** For every `k` there is an admissible set of
size exactly `k`, so the extremal value `A(k) = min a_k` is taken over a nonempty family.

Construction: the multiples `0, N, 2N, …, (k-1)N` of the primorial
`N = ∏_{p ≤ k, p prime} p`. Modulo each prime `p ≤ k` every element is `≡ 0` (since `p ∣ N`),
so the class `1` is missed; primes `p > k = card` are automatic by `missing_class_of_card_lt`.
This also gives the explicit (weak) upper bound `A(k) ≤ (k-1)·∏_{p ≤ k} p`. -/
theorem exists_admissible_card (k : ℕ) :
    ∃ a : Finset ℕ, a.card = k ∧ Admissible a := by
  classical
  -- An `N > 0` divisible by every prime `p ≤ k` (the primorial works).
  obtain ⟨N, hNpos, hNdvd⟩ : ∃ N : ℕ, 0 < N ∧ ∀ p, p.Prime → p ≤ k → p ∣ N := by
    refine ⟨((Finset.range (k + 1)).filter Nat.Prime).prod id, ?_, ?_⟩
    · exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.pos)
    · intro p hp hpk
      exact Finset.dvd_prod_of_mem id
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  have hinj : Function.Injective (fun x : ℕ => x * N) :=
    fun x y h => Nat.eq_of_mul_eq_mul_right hNpos h
  refine ⟨(Finset.range k).image (fun x => x * N), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  · rw [admissible_iff_card, Finset.card_image_of_injective _ hinj, Finset.card_range]
    intro p hp hpk
    haveI : Fact p.Prime := ⟨hp⟩
    have hp0 : (N : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p N).mpr (hNdvd p hp hpk)
    refine ⟨1, fun x hx => ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    push_cast
    rw [hp0, mul_zero]
    exact zero_ne_one

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
