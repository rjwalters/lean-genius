/-
  Exact count of length-`k` arithmetic progressions fitting in `[n]`
  (follow-up van-der-waerden-first-moment-oq-01-oq-01)

  The sharpening `Proofs.VanDerWaerdenFirstMomentOQ01` proves the *upper* bound

        (vdwFamily n k).card  ≤  ∑_{d=1}^{n} (n - (k-1)·d)        (card_vdwFamily_le_sum)

  via `Finset.card_image_le`, which silently allows two distinct parameter pairs
  `(a, d)` to collapse to the same arithmetic progression.  Here we close that gap:
  for `k ≥ 2` the parameterisation `(a, d) ↦ vdwAP n a d k` is *injective* on the
  fitting box, so the bound is an **equality** —

        (vdwFamily n k).card  =  ∑_{d=1}^{n} (n - (k-1)·d)        (card_vdwFamily_eq_sum)

  i.e. the triangular sum is the *exact* number of length-`k` arithmetic
  progressions that fit in `[n]`.  Together with the telescoping bound
  `2(k-1)·(∑ …) ≤ n²` from the parent file this pins the count between the two
  sides: the parent's `≤ n²/(2(k-1))` is now an exact value, not just an estimate.

  The injectivity is established by pure membership, with no `min'`/order
  machinery: for `k ≥ 2` the first two terms `a` and `a+d` of one progression both
  lie in the other (they are its `i = 0` and `i = 1` members), and matching them up
  forces the parameters to coincide.

  Why `k ≥ 2` is necessary: for `k = 0` every pair maps to `∅`, and for `k = 1`
  every pair `(a, d)` maps to the singleton `{a}`, losing the step `d`.  Injectivity
  genuinely requires at least two points.

  Status: 0 sorries, 0 axioms, no `native_decide`.  #print axioms reports only
  `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.VanDerWaerdenFirstMomentOQ01

namespace ProbMethod.VanDerWaerden

open Finset
open scoped Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- **The `i`-th term lies in the AP.** For any index `i < k`, the point
`a + i·d` (as an element of `Fin n`) is a member of `vdwAP n a d k`.  This needs
no fitting hypothesis — it is immediate from the image definition. -/
theorem mem_vdwAP_term {a d k i : ℕ} (hi : i < k) :
    (Nat.cast (a + i * d) : Fin n) ∈ vdwAP n a d k := by
  rw [vdwAP, Finset.mem_image]
  exact ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- **Membership extraction.** If the AP `vdwAP n a d k` fits (`a + (k-1)d < n`)
then every member's underlying value is `a + i·d` for some index `i < k`. -/
theorem val_of_mem_vdwAP {a d k : ℕ} (hbound : a + (k - 1) * d < n)
    {z : Fin n} (hz : z ∈ vdwAP n a d k) : ∃ i, i < k ∧ a + i * d = (z : ℕ) := by
  rw [vdwAP, Finset.mem_image] at hz
  obtain ⟨i, hi, hiz⟩ := hz
  rw [Finset.mem_range] at hi
  have hb : a + i * d < n := by
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  refine ⟨i, hi, ?_⟩
  have := congrArg Fin.val hiz
  rwa [Fin.val_cast_of_lt hb] at this

/-- **Cross-membership equation.** If two fitting APs are equal, then the `i`-th
term of the first equals the `j`-th term of the second for some `j < k`. -/
theorem term_eq_of_vdwAP_eq {a d a' d' k i : ℕ} (hi : i < k)
    (hb : a + i * d < n) (hbound' : a' + (k - 1) * d' < n)
    (heq : vdwAP n a d k = vdwAP n a' d' k) :
    ∃ j, j < k ∧ a' + j * d' = a + i * d := by
  have hmem : (Nat.cast (a + i * d) : Fin n) ∈ vdwAP n a' d' k := by
    rw [← heq]; exact mem_vdwAP_term hi
  obtain ⟨j, hj, e⟩ := val_of_mem_vdwAP hbound' hmem
  exact ⟨j, hj, by rwa [Fin.val_cast_of_lt hb] at e⟩

/-- **Injectivity of the AP parameterisation.** For `k ≥ 2`, distinct fitting
parameter pairs `(a, d)` yield distinct length-`k` arithmetic progressions. -/
theorem vdwAP_injOn (k : ℕ) (hk : 2 ≤ k) :
    Set.InjOn (fun p : ℕ × ℕ => vdwAP n p.1 p.2 k)
      ↑(((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
          (fun p => p.1 + (k - 1) * p.2 < n)) := by
  intro p hp q hq heq
  obtain ⟨a, d⟩ := p
  obtain ⟨a', d'⟩ := q
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_Icc] at hp hq
  obtain ⟨⟨_, hd1, _⟩, hpb⟩ := hp
  obtain ⟨⟨_, hd1', _⟩, hqb⟩ := hq
  -- `heq : vdwAP n a d k = vdwAP n a' d' k`
  simp only at heq
  -- term bounds: a, a+d, a', a'+d' are all `< n`
  have hba : a + 0 * d < n := by omega
  have hbad : a + 1 * d < n := by
    have : (1 : ℕ) * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  have hba' : a' + 0 * d' < n := by omega
  have hbad' : a' + 1 * d' < n := by
    have : (1 : ℕ) * d' ≤ (k - 1) * d' := Nat.mul_le_mul_right d' (by omega)
    omega
  -- (A) a = a' + i₁·d'  and  (C) a' = a + i₂·d  ⟹  a = a'
  obtain ⟨i₁, _, eA⟩ := term_eq_of_vdwAP_eq (n := n) (by omega : 0 < k) hba hqb heq
  obtain ⟨i₂, _, eC⟩ := term_eq_of_vdwAP_eq (n := n) (by omega : 0 < k) hba' hpb heq.symm
  -- eA : a' + i₁ * d' = a + 0 * d ;  eC : a + i₂ * d = a' + 0 * d'
  have haa' : a = a' := by
    have e1 : a' + i₁ * d' = a := by simpa using eA
    have e2 : a + i₂ * d = a' := by simpa using eC
    have hx : i₂ * d = 0 ∧ i₁ * d' = 0 := by
      constructor <;> omega
    have hi2 : i₂ = 0 := by
      rcases Nat.mul_eq_zero.mp hx.1 with h | h
      · exact h
      · omega
    have hi1 : i₁ = 0 := by
      rcases Nat.mul_eq_zero.mp hx.2 with h | h
      · exact h
      · omega
    omega
  -- (B) a+d = a' + i₃·d'  and  (D) a'+d' = a + i₄·d  ⟹  d = d'
  obtain ⟨i₃, _, eB⟩ := term_eq_of_vdwAP_eq (n := n) (by omega : 1 < k) hbad hqb heq
  obtain ⟨i₄, _, eD⟩ := term_eq_of_vdwAP_eq (n := n) (by omega : 1 < k) hbad' hpb heq.symm
  have hdd' : d = d' := by
    -- using a = a': d = i₃·d' and d' = i₄·d
    have e3 : d = i₃ * d' := by
      have : a' + i₃ * d' = a + 1 * d := eB
      rw [← haa'] at this; omega
    have e4 : d' = i₄ * d := by
      have : a + i₄ * d = a' + 1 * d' := eD
      rw [← haa'] at this; omega
    have hi3 : 1 ≤ i₃ := by
      rcases Nat.eq_zero_or_pos i₃ with h | h
      · simp [h] at e3; omega
      · exact h
    have hi4 : 1 ≤ i₄ := by
      rcases Nat.eq_zero_or_pos i₄ with h | h
      · simp [h] at e4; omega
      · exact h
    have hge : d ≥ d' := by
      calc d = i₃ * d' := e3
        _ ≥ 1 * d' := Nat.mul_le_mul_right d' hi3
        _ = d' := one_mul d'
    have hle : d' ≥ d := by
      calc d' = i₄ * d := e4
        _ ≥ 1 * d := Nat.mul_le_mul_right d hi4
        _ = d := one_mul d
    omega
  -- conclude (a, d) = (a', d')
  simp only [Prod.mk.injEq]
  exact ⟨haa', hdd'⟩

/-- **Exact count of length-`k` APs in `[n]`.** For `k ≥ 2` the number of
length-`k` arithmetic progressions with positive step that fit in `[n]` is exactly
the triangular sum `∑_{d=1}^{n} (n - (k-1)·d)`.  This upgrades the parent file's
upper bound `card_vdwFamily_le_sum` (proved by `card_image_le`) to an equality, by
injectivity of the parameterisation. -/
theorem card_vdwFamily_eq_sum (k : ℕ) (hk : 2 ≤ k) :
    (vdwFamily n k).card = ∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d) := by
  rw [vdwFamily, Finset.card_image_of_injOn (vdwAP_injOn k hk)]
  exact vdwFilter_card_eq_sum n k

end ProbMethod.VanDerWaerden
