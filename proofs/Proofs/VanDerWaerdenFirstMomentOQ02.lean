/-
  Bounded dependency degree of the AP-hypergraph
  (open question van-der-waerden-first-moment-oq-02, the Lovász-Local-Lemma route)

  The base entry `Proofs.VanDerWaerdenFirstMoment` proves the first-moment
  (union-bound) lower bound `W(k) ≳ 2^((k-1)/2)` by instantiating the gallery's
  Property-B engine on the AP-hypergraph.  The Seeker's open question asks to push
  the exponent up to the Lovász-Local-Lemma form `W(k) ≳ 2^k/(e·k)`.  As the
  question itself notes, the LLL route needs two verified ingredients:

    (1) a symmetric Lovász Local Lemma statement, and
    (2) **a bound on the AP-overlap ("dependency") degree** of the hypergraph.

  This file supplies ingredient (2) — the concrete, elementary combinatorial
  input — outright, with 0 axioms.  Ingredient (1) is a genuine build (Mathlib
  has no symmetric LLL) and remains the open gap; see the closing remarks.

  WHY THE DEGREE BOUND MUST BE LINEAR IN `n`.  In the LLL each event
  `A_e = "AP e is monochromatic"` is mutually independent of every `A_f` whose AP
  `f` is disjoint from `e`; the dependency degree is therefore
  `d = max_e #{f ∈ family : f ≠ e, f ∩ e ≠ ∅}`.  The symmetric LLL then gives a
  good colouring whenever `e · 2^(1-k) · (d+1) ≤ 1`, i.e. `n ≲ 2^(k-1)/(e·d/n)`.
  Only a bound `d ≤ C(k)·n` *linear in n* turns this into `W(k) ≳ 2^k/(e·k)`;
  the trivial `d ≤ |family| ≤ n²` (quadratic) recovers nothing beyond the
  first-moment `2^(k/2)`.  So the content here is precisely the *linear* bound.

  MAIN RESULTS
    * `exists_index_of_mem`       — recover the index `i < k` with `x = a + i·d`
                                    from `x ∈ vdwAP n a d k`.
    * `card_params_through_le`    — at most `k·n` fitting parameter pairs `(a,d)`
                                    put a length-`k` AP through a fixed point `x`
                                    (via the injection `(a,d) ↦ ((x-a)/d, d)`).
    * `card_family_through_le`    — hence at most `k·n` APs of the family contain
                                    a fixed point.
    * `card_vdwFamily_meeting_le` /
      `vdwHypergraph_degree_le`   — **the dependency-degree bound**: every
                                    length-`k` AP meets at most `k²·n` members of
                                    the family (each of its `k` points lies on
                                    `≤ k·n` APs).

  Everything is elementary counting on the base entry's `vdwAP` / `vdwFamily`;
  the probabilistic core is untouched.

  Status: 0 sorries, 0 axioms, no `native_decide`.  #print axioms reports only
  `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.VanDerWaerdenFirstMoment

namespace ProbMethod.VanDerWaerden

open Finset
open scoped Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- **Index recovery.** If the length-`k` AP with first term `a` and step `d`
fits in `[n]` (`a + (k-1)d < n`) and the point `x` lies on it, then
`x = a + i·d` (as underlying naturals) for some index `i < k`. -/
theorem exists_index_of_mem {a d k : ℕ} (hbound : a + (k - 1) * d < n)
    {x : Fin n} (hx : x ∈ vdwAP n a d k) : ∃ i < k, (x : Fin n).val = a + i * d := by
  rw [vdwAP, Finset.mem_image] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  rw [Finset.mem_range] at hi
  refine ⟨i, hi, ?_⟩
  have hb : a + i * d < n := by
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  rw [← hxi, Fin.val_cast_of_lt hb]

/-- **APs through a fixed point: parameter count.**
At most `k · n` fitting parameter pairs `(a, d)` produce a length-`k` AP through a
given point `x`.  The map `(a, d) ↦ ((x - a)/d, d)` sends such a pair to its index
`i = (x - a)/d < k` together with the step `d ∈ {1, …, n}`, and is injective
because `a = x - i·d` is recovered from the image. -/
theorem card_params_through_le (k : ℕ) (x : Fin n) :
    (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
        (fun p => p.1 + (k - 1) * p.2 < n ∧ x ∈ vdwAP n p.1 p.2 k)).card ≤ k * n := by
  classical
  have hcard :
      (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
        (fun p => p.1 + (k - 1) * p.2 < n ∧ x ∈ vdwAP n p.1 p.2 k)).card
      ≤ ((Finset.range k) ×ˢ (Finset.Icc 1 n)).card := by
    apply Finset.card_le_card_of_injOn
      (fun p => (((x : Fin n).val - p.1) / p.2, p.2))
    · -- maps into (range k) ×ˢ (Icc 1 n)
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hp
      obtain ⟨⟨-, hd⟩, hbound, hmem⟩ := hp
      obtain ⟨i, hik, hxi⟩ := exists_index_of_mem hbound hmem
      have hsub : (x : Fin n).val - p.1 = i * p.2 := by omega
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
      refine ⟨?_, hd⟩
      rw [hsub, Nat.mul_div_cancel _ hd.1]
      exact hik
    · -- injective on the filtered set
      intro p hp q hq hfeq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hp hq
      obtain ⟨⟨-, hdp⟩, hbp, hmp⟩ := hp
      obtain ⟨⟨-, hdq⟩, hbq, hmq⟩ := hq
      obtain ⟨ip, hipk, hxp⟩ := exists_index_of_mem hbp hmp
      obtain ⟨iq, hiqk, hxq⟩ := exists_index_of_mem hbq hmq
      simp only [Prod.mk.injEq] at hfeq
      obtain ⟨hfst, hd⟩ := hfeq
      have hdivp : ((x : Fin n).val - p.1) / p.2 = ip := by
        have : (x : Fin n).val - p.1 = ip * p.2 := by omega
        rw [this, Nat.mul_div_cancel _ hdp.1]
      have hdivq : ((x : Fin n).val - q.1) / q.2 = iq := by
        have : (x : Fin n).val - q.1 = iq * q.2 := by omega
        rw [this, Nat.mul_div_cancel _ hdq.1]
      rw [hdivp, hdivq] at hfst
      -- hfst : ip = iq ; hd : p.2 = q.2
      have hprod : ip * p.2 = iq * q.2 := by rw [hfst, hd]
      have hp1 : p.1 = q.1 := by omega
      exact Prod.ext hp1 hd
  calc
    (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
        (fun p => p.1 + (k - 1) * p.2 < n ∧ x ∈ vdwAP n p.1 p.2 k)).card
        ≤ ((Finset.range k) ×ˢ (Finset.Icc 1 n)).card := hcard
    _ = k * n := by
        rw [Finset.card_product, Finset.card_range, Nat.card_Icc, Nat.add_sub_cancel]

/-- **APs of the family through a fixed point.**
At most `k · n` length-`k` APs of `vdwFamily n k` contain a given point `x`.
The family is the image of the fitting parameter set under `vdwAP`, so each member
through `x` comes from a parameter pair through `x`, of which there are `≤ k·n`. -/
theorem card_family_through_le (k : ℕ) (x : Fin n) :
    ((vdwFamily n k).filter (fun f => x ∈ f)).card ≤ k * n := by
  classical
  have hsub :
      (vdwFamily n k).filter (fun f => x ∈ f)
      ⊆ (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
            (fun p => p.1 + (k - 1) * p.2 < n ∧ x ∈ vdwAP n p.1 p.2 k)).image
            (fun p => vdwAP n p.1 p.2 k) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfam, hxf⟩ := hf
    rw [vdwFamily, Finset.mem_image] at hfam
    obtain ⟨p, hp, rfl⟩ := hfam
    rw [Finset.mem_filter] at hp
    obtain ⟨hpmem, hpb⟩ := hp
    rw [Finset.mem_image]
    exact ⟨p, Finset.mem_filter.mpr ⟨hpmem, hpb, hxf⟩, rfl⟩
  calc
    ((vdwFamily n k).filter (fun f => x ∈ f)).card
        ≤ ((((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
            (fun p => p.1 + (k - 1) * p.2 < n ∧ x ∈ vdwAP n p.1 p.2 k)).image
            (fun p => vdwAP n p.1 p.2 k)).card := Finset.card_le_card hsub
    _ ≤ (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
            (fun p => p.1 + (k - 1) * p.2 < n ∧ x ∈ vdwAP n p.1 p.2 k)).card :=
          Finset.card_image_le
    _ ≤ k * n := card_params_through_le k x

/-- **Dependency-degree bound for the AP-hypergraph (product form).**
Every length-`k` AP `e` of the family meets at most `k · (k · n)` members of the
family: `e` has exactly `k` points, and each point lies on at most `k · n` APs
of the family (`card_family_through_le`). -/
theorem card_vdwFamily_meeting_le {k : ℕ} {e : Finset (Fin n)}
    (he : e ∈ vdwFamily n k) :
    ((vdwFamily n k).filter (fun f => (e ∩ f).Nonempty)).card ≤ k * (k * n) := by
  classical
  have hecard : e.card = k := vdwFamily_uniform k e he
  have hsub :
      (vdwFamily n k).filter (fun f => (e ∩ f).Nonempty)
      ⊆ e.biUnion (fun x => (vdwFamily n k).filter (fun f => x ∈ f)) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfam, hne⟩ := hf
    obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_biUnion]
    exact ⟨x, hx.1, Finset.mem_filter.mpr ⟨hfam, hx.2⟩⟩
  calc
    ((vdwFamily n k).filter (fun f => (e ∩ f).Nonempty)).card
        ≤ (e.biUnion (fun x => (vdwFamily n k).filter (fun f => x ∈ f))).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ x ∈ e, ((vdwFamily n k).filter (fun f => x ∈ f)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ e, k * n := Finset.sum_le_sum (fun x _ => card_family_through_le k x)
    _ = e.card * (k * n) := by rw [Finset.sum_const, smul_eq_mul]
    _ = k * (k * n) := by rw [hecard]

/-- **Dependency-degree bound for the AP-hypergraph, `k²·n` form.**
The maximum degree of the AP-overlap graph on `vdwFamily n k` is at most `k² · n`.
This is the linear-in-`n` dependency bound the symmetric Lovász Local Lemma needs
to upgrade the first-moment `W(k) ≳ 2^((k-1)/2)` to `W(k) ≳ 2^k/(e·k)`. -/
theorem vdwHypergraph_degree_le {k : ℕ} {e : Finset (Fin n)}
    (he : e ∈ vdwFamily n k) :
    ((vdwFamily n k).filter (fun f => (e ∩ f).Nonempty)).card ≤ k ^ 2 * n := by
  calc
    ((vdwFamily n k).filter (fun f => (e ∩ f).Nonempty)).card
        ≤ k * (k * n) := card_vdwFamily_meeting_le he
    _ = k ^ 2 * n := by ring

end ProbMethod.VanDerWaerden
