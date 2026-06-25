/-
  The First-Moment Lower Bound for van der Waerden Numbers

  Van der Waerden's theorem guarantees that for every `k` there is an `N` such
  that every 2-colouring of `{0, …, N-1}` contains a monochromatic arithmetic
  progression of length `k`; the least such `N` is the van der Waerden number
  `W(k)`.  The classical *lower* bound on `W(k)` is a first-moment (union-bound)
  argument: colour each point independently and uniformly at random; a fixed
  length-`k` AP is monochromatic with probability `2^(1-k)`, so if the number of
  length-`k` APs that fit in `[n]` is `< 2^(k-1)` then some 2-colouring leaves
  *every* AP non-monochromatic, witnessing `W(k) > n`.

  This file derives that bound as a verified theorem.  The observation that makes
  it cheap is structural: a length-`k` arithmetic progression is simply a
  `k`-element subset of the ground set, and "monochromatic AP" is exactly
  "monochromatic edge" of the hypergraph whose edges are the AP-subsets.  So the
  van der Waerden lower bound is **Property B applied to the AP-hypergraph**, and
  we obtain it by instantiating the gallery's verified Erdős-1963 Property-B
  engine `ProbMethod.PropertyB.property_b_two_colorable` rather than redoing the
  counting.

  New content here:
    * `vdwAP`     — the length-`k` AP `{a, a+d, …, a+(k-1)d}` as a `Finset (Fin n)`.
    * `card_vdwAP`— a fitting AP with positive step has exactly `k` elements.
    * `vdwFamily` — the family of all length-`k` APs that fit in `[n]`.
    * `card_vdwFamily_le` — at most `n²` of them.
    * `vdw_two_coloring_exists` / `vdw_lower_bound` — the first-moment lower
      bound: when the AP family is small there is a 2-colouring of `[n]` with no
      monochromatic length-`k` AP.

  CONTRAST WITH THE GALLERY.  The van der Waerden lower bound is currently only
  *axiomatized* (entry `erdos-138`, 8 axioms).  This file proves the elementary
  first-moment form outright.  The bound `n² < 2^(k-1)` it delivers is the clean
  union-bound threshold (`W(k) ≳ 2^((k-1)/2)`); it is deliberately loose in the
  AP count (every `(a,d)` pair is allowed) but fully verified.

  Status: 0 sorries, 0 axioms, no `native_decide`.  #print axioms reports only
  `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.PropertyBFirstMoment

namespace ProbMethod.VanDerWaerden

open Finset
open ProbMethod.PropertyB (Mono property_b_two_colorable)
open scoped Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- The length-`k` arithmetic progression with first term `a` and common
difference `d`, as a subset of `Fin n`: `{a, a+d, …, a+(k-1)d}`. -/
def vdwAP (n : ℕ) [NeZero n] (a d k : ℕ) : Finset (Fin n) :=
  (Finset.range k).image (fun i => (Nat.cast (a + i * d) : Fin n))

/-- **A fitting AP with positive step has exactly `k` elements.**
If the top term `a + (k-1)d` is `< n` and the step `d` is positive, the map
`i ↦ a + i·d` is injective on `{0, …, k-1}` (its values are distinct naturals
all below `n`), so the AP has `k` distinct points. -/
theorem card_vdwAP {a d k : ℕ} (hd : 1 ≤ d) (hbound : a + (k - 1) * d < n) :
    (vdwAP n a d k).card = k := by
  unfold vdwAP
  rw [Finset.card_image_of_injOn, Finset.card_range]
  -- the index map is injective on range k
  intro i hi j hj hij
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  -- the i-th and j-th terms are below n, so the casts recover the naturals
  have hbi : a + i * d < n := by
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  have hbj : a + j * d < n := by
    have : j * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  have hval : a + i * d = a + j * d := by
    have := congrArg Fin.val hij
    rwa [Fin.val_cast_of_lt hbi, Fin.val_cast_of_lt hbj] at this
  -- cancel: a + i·d = a + j·d, d > 0 ⟹ i = j
  have : i * d = j * d := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

/-- The family of all length-`k` arithmetic progressions that fit in `[n]`:
ranging over first term `a < n` and positive step `d ≤ n` with `a + (k-1)d < n`. -/
def vdwFamily (n : ℕ) [NeZero n] (k : ℕ) : Finset (Finset (Fin n)) :=
  (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
      (fun p => p.1 + (k - 1) * p.2 < n)).image (fun p => vdwAP n p.1 p.2 k)

/-- Every member of the AP family is a genuine `k`-element set. -/
theorem vdwFamily_uniform (k : ℕ) :
    ∀ e ∈ vdwFamily n k, e.card = k := by
  intro e he
  rw [vdwFamily, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
  obtain ⟨⟨_, hd1, _⟩, hbound⟩ := hp
  exact card_vdwAP hd1 hbound

/-- **At most `n²` length-`k` APs fit in `[n]`.**
The family is the image of a set of `(a, d)` pairs drawn from
`{0,…,n-1} × {1,…,n}`, of which there are `n · n`. -/
theorem card_vdwFamily_le (k : ℕ) : (vdwFamily n k).card ≤ n * n := by
  calc (vdwFamily n k).card
      ≤ (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
          (fun p => p.1 + (k - 1) * p.2 < n)).card := Finset.card_image_le
    _ ≤ ((Finset.range n) ×ˢ (Finset.Icc 1 n)).card := Finset.card_filter_le _ _
    _ = n * n := by rw [Finset.card_product, Finset.card_range, Nat.card_Icc,
                        Nat.add_sub_cancel]

/-- **First-moment van der Waerden lower bound (hypergraph form).**
If fewer than `2^(k-1)` length-`k` APs fit in `[n]`, there is a 2-colouring of
`[n]` under which no length-`k` AP is monochromatic.  This is exactly Erdős'
Property B for the AP-hypergraph. -/
theorem vdw_two_coloring_exists {k : ℕ} (hk : 1 ≤ k)
    (hsmall : (vdwFamily n k).card < 2 ^ (k - 1)) :
    ∃ c : Fin n → Bool, ∀ e ∈ vdwFamily n k, ¬ Mono e c :=
  property_b_two_colorable (vdwFamily n k) k hk (vdwFamily_uniform k) hsmall

/-- **First-moment van der Waerden lower bound, AP form.**
If `n² < 2^(k-1)` (so `n < 2^((k-1)/2)`, i.e. `W(k) > n`), there is a
2-colouring of `[n]` under which every length-`k` arithmetic progression with
positive step contains both colours.  Combining `card_vdwFamily_le` with the
hypergraph form. -/
theorem vdw_lower_bound {k : ℕ} (hk : 2 ≤ k) (hnk : n * n < 2 ^ (k - 1)) :
    ∃ c : Fin n → Bool, ∀ a d : ℕ, 1 ≤ d → a + (k - 1) * d < n →
      ¬ Mono (vdwAP n a d k) c := by
  obtain ⟨c, hc⟩ :=
    vdw_two_coloring_exists (by omega) (lt_of_le_of_lt (card_vdwFamily_le k) hnk)
  refine ⟨c, fun a d hd hb => ?_⟩
  apply hc
  -- the AP `vdwAP n a d k` belongs to the family
  rw [vdwFamily, Finset.mem_image]
  refine ⟨(a, d), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  -- d ≤ n since (k-1) ≥ 1, and a < n since a ≤ a + (k-1)d
  have hdn : d ≤ (k - 1) * d := Nat.le_mul_of_pos_left d (by omega)
  exact ⟨⟨by omega, hd, by omega⟩, hb⟩

end ProbMethod.VanDerWaerden
