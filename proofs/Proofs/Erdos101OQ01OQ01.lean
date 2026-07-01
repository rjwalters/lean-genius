/-
# Erdős #101 OQ-01 · Sub-question 01: The Incidence Handshake Identity

Erdős asked whether an `n`-point planar set with no five collinear points can
contain more than `o(n²)` lines meeting exactly four of the points.  The parent
file `Erdos101OQ01.lean` records the `o(n²)` conjecture as an open `sorry`; the
framework file `Erdos101Problem.lean` proves the unconditional pair-counting
bound `fourPointLineCount P ≤ n(n-1)/12` together with the per-point bound
`fourCollinearThrough_bound : (fourCollinearThrough P p).card ≤ (n-1)/3`.

This file supplies the **incidence handshake identity** that ties the local
(per-point) and global (total) counts together:

  `∑_{p ∈ P.points} (fourCollinearThrough P p).card = 4 · fourPointLineCount P`.

Each four-point line is a `4`-element collinear subset, and it is counted once
for each of its four points — the geometric analogue of the handshaking lemma
`∑ deg = 2|E|`.  From it we obtain:

* an **independent, incidence-based re-derivation** of the global upper bound
  `fourPointLineCount P ≤ n(n-1)/12`, routed through the per-point bound rather
  than through the direct pair count (`improved_upper_bound` in the parent);

* the **Cauchy–Schwarz second-moment inequality**
  `16 · L² ≤ n · ∑_p tₚ²`  where `tₚ = (fourCollinearThrough P p).card` and
  `L = fourPointLineCount P`.  This is exactly the object named in open
  question #2 of the parent entry ("does the per-point bound admit a
  Cauchy–Schwarz second-moment improvement?"): the incidence degree sequence
  `(tₚ)` is pinned to a fixed first moment `4L`, so any *upper* bound on its
  second moment `∑ tₚ²` immediately upgrades the global count.  We supply the
  identity and the lower bound; the matching upper bound on `∑ tₚ²` is the
  remaining open input.

Everything below is proved with no `axiom`, no `sorry`, and no `native_decide`.
-/

import Proofs.Erdos101Problem
import Mathlib.Algebra.Order.Chebyshev

namespace Erdos101OQ01OQ01

open Classical

/-- **Filter reformulation.**  The four-point lines through a fixed point `p`
    are exactly the members of `fourCollinearFamily P` that contain `p`.  This
    lets us treat the local families as slices of the one global family. -/
theorem fourCollinearThrough_eq_filter (P : PlanarPointSet) (p : ℝ × ℝ) :
    fourCollinearThrough P p
      = (fourCollinearFamily P).filter (fun S => p ∈ S) := by
  unfold fourCollinearThrough fourCollinearFamily
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hcard, hpS, hline⟩
    exact ⟨⟨hsub, hcard, hline⟩, hpS⟩
  · rintro ⟨⟨hsub, hcard, hline⟩, hpS⟩
    exact ⟨hsub, hcard, hpS, hline⟩

/-- For any four-point line `S` (a member of the family), exactly four points of
    `P` lie on it: the incidence count of a single line is its four points. -/
theorem incidence_of_member (P : PlanarPointSet) {S : Finset (ℝ × ℝ)}
    (hS : S ∈ fourCollinearFamily P) :
    (P.points.filter (fun p => p ∈ S)).card = 4 := by
  have hmem := Finset.mem_filter.mp hS
  have hsub : S ⊆ P.points := Finset.mem_powerset.mp hmem.1
  have hcard : S.card = 4 := hmem.2.1
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub, hcard]

/-- **Incidence Handshake Identity.**  Summing the per-point four-point-line
    counts over all points of `P` recovers four times the global count, since
    each four-point line carries exactly four incidences.

    This is the double-counting bridge between `fourCollinearThrough_bound`
    (local) and `fourPointLineCount` (global). -/
theorem sum_fourCollinearThrough_card (P : PlanarPointSet) :
    ∑ p ∈ P.points, (fourCollinearThrough P p).card
      = 4 * fourPointLineCount P := by
  rw [fourPointLineCount_eq_family]
  -- Replace each local family by the corresponding slice of the global family.
  have step : ∀ p ∈ P.points, (fourCollinearThrough P p).card
      = ∑ S ∈ fourCollinearFamily P, if p ∈ S then 1 else 0 := by
    intro p _
    rw [fourCollinearThrough_eq_filter, Finset.card_filter]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  -- Each line contributes its four incident points.
  have inner : ∀ S ∈ fourCollinearFamily P,
      (∑ p ∈ P.points, if p ∈ S then 1 else 0) = 4 := by
    intro S hS
    rw [← Finset.card_filter]
    exact incidence_of_member P hS
  rw [Finset.sum_congr rfl inner, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Incidence-routed upper bound.**  Combining the handshake identity with the
    per-point bound `(fourCollinearThrough P p).card ≤ (n-1)/3` gives the global
    bound `fourPointLineCount P ≤ n(n-1)/12`.

    This reproves the parent's `improved_upper_bound` through a genuinely
    different argument: the parent counts point *pairs* directly, whereas here
    the bound is assembled from local per-point contributions via the handshake
    identity. -/
theorem improved_upper_bound_via_handshake (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 12 := by
  set n := P.points.card with hn
  -- Step 1: bound the summed local counts by n · (n-1)/3.
  have hsum_le : ∑ p ∈ P.points, (fourCollinearThrough P p).card
      ≤ n * ((n - 1) / 3) := by
    calc ∑ p ∈ P.points, (fourCollinearThrough P p).card
        ≤ ∑ _p ∈ P.points, (n - 1) / 3 := by
          apply Finset.sum_le_sum
          intro p hp
          exact fourCollinearThrough_bound P hP p hp
      _ = n * ((n - 1) / 3) := by
          rw [Finset.sum_const, smul_eq_mul, hn]
  -- Step 2: turn the handshake identity into 4 · L ≤ n · (n-1)/3.
  rw [sum_fourCollinearThrough_card] at hsum_le
  -- Step 3: nat-division bookkeeping: 12 L ≤ n(n-1), hence L ≤ n(n-1)/12.
  have hdiv : 3 * ((n - 1) / 3) ≤ n - 1 := Nat.mul_div_le (n - 1) 3
  have h12 : 12 * fourPointLineCount P ≤ n * (n - 1) := by
    calc 12 * fourPointLineCount P = 3 * (4 * fourPointLineCount P) := by ring
      _ ≤ 3 * (n * ((n - 1) / 3)) := by
          apply Nat.mul_le_mul_left
          exact hsum_le
      _ = n * (3 * ((n - 1) / 3)) := by ring
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n hdiv
  exact Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by linarith [h12])

/-- **Cauchy–Schwarz second moment (real form).**  With `tₚ` the number of
    four-point lines through `p` and `L = fourPointLineCount P`, the incidence
    degree sequence has fixed first moment `∑ tₚ = 4L`, so by Cauchy–Schwarz

      `(4L)² ≤ n · ∑_p tₚ²`.

    Any *upper* bound `∑_p tₚ² ≤ B` therefore forces `L² ≤ nB/16` — the
    second-moment lever named in open question #2 of the parent entry. -/
theorem sq_count_le_card_mul_sum_sq (P : PlanarPointSet) :
    16 * (fourPointLineCount P : ℝ) ^ 2
      ≤ (P.points.card : ℝ)
          * ∑ p ∈ P.points, ((fourCollinearThrough P p).card : ℝ) ^ 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := P.points)
    (f := fun p => ((fourCollinearThrough P p).card : ℝ))
  -- Rewrite the first moment via the handshake identity.
  have hsum : (∑ p ∈ P.points, ((fourCollinearThrough P p).card : ℝ))
      = 4 * (fourPointLineCount P : ℝ) := by
    rw [← Nat.cast_sum, sum_fourCollinearThrough_card]
    push_cast
    ring
  rw [hsum] at hcs
  calc 16 * (fourPointLineCount P : ℝ) ^ 2
      = (4 * (fourPointLineCount P : ℝ)) ^ 2 := by ring
    _ ≤ (P.points.card : ℝ)
          * ∑ p ∈ P.points, ((fourCollinearThrough P p).card : ℝ) ^ 2 := hcs

end Erdos101OQ01OQ01
