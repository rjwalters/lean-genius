import Proofs.Erdos85BinaryCycleIntertwiner
import Proofs.Erdos85EvenCycleSelfIntertwiner
import Proofs.Erdos85FrequencyPairGraphBlocks
import Proofs.Erdos85SecondOrderEvenDefect

/-!
# C4-free rigidity of the two checkerboard orientations on an even cycle

For an even cyclic self-block, the d'Alembert coordinates split into two
parity classes.  On same-parity pairs the block is circulant; on
opposite-parity pairs it is reverse-circulant.  The two sectors cannot both
carry an edge in a `C4`-free graph: an internal edge and a cross-parity edge
translate to the opposite sides of a four-cycle.

This file isolates that geometric argument.  The remaining input needed for
the full even-cycle orientation theorem is the checkerboard invariance itself.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Modulo two, sum and difference have the same parity. -/
theorem castHom_two_sub_eq_add
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r) (x y : ZMod r) :
    ZMod.castHom h2r (ZMod 2) (y - x) =
      ZMod.castHom h2r (ZMod 2) (y + x) := by
  rw [map_sub, map_add, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

/-- A forward cyclic diagonal `y - x = d` and a reverse cyclic diagonal
`y + x = s` are disjoint whenever their offsets have different parity. -/
theorem forward_reverse_diagonals_disjoint_of_castHom_ne
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r) (d s : ZMod r)
    (hparity : ZMod.castHom h2r (ZMod 2) d ≠
      ZMod.castHom h2r (ZMod 2) s) :
    ¬ ∃ x y : ZMod r, y - x = d ∧ y + x = s := by
  rintro ⟨x, y, hsub, hadd⟩
  apply hparity
  calc
    ZMod.castHom h2r (ZMod 2) d =
        ZMod.castHom h2r (ZMod 2) (y - x) := by rw [hsub]
    _ = ZMod.castHom h2r (ZMod 2) (y + x) :=
      castHom_two_sub_eq_add h2r x y
    _ = ZMod.castHom h2r (ZMod 2) s := by rw [hadd]

/-- On an even cyclic group, the image of doubling is exactly the kernel of
reduction modulo two. -/
theorem zmod_mem_range_two_mul_iff_castHom_eq_zero
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r) (z : ZMod r) :
    z ∈ Set.range (fun t : ZMod r ↦ 2 * t) ↔
      ZMod.castHom h2r (ZMod 2) z = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [map_mul]
    have htwo : ZMod.castHom h2r (ZMod 2) (2 : ZMod r) = 0 := by
      rw [map_ofNat]
      exact ZMod.natCast_self 2
    rw [htwo, zero_mul]
  · intro hz
    have hzval : ((z.val : ℕ) : ZMod 2) = 0 := by
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hz
    obtain ⟨k, hk⟩ := ZMod.natCast_eq_zero_iff_even.mp hzval
    refine ⟨(k : ZMod r), ?_⟩
    rw [← ZMod.natCast_zmod_val z, hk]
    push_cast
    ring

/-- Forward and reverse cyclic diagonals whose offsets have the same parity
do intersect.  Equivalently, solving the two diagonal equations amounts to
halving `s - d`, which is possible precisely in the even-parity fiber. -/
theorem exists_forward_reverse_diagonal_intersection_of_castHom_eq
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r) (d s : ZMod r)
    (hparity : ZMod.castHom h2r (ZMod 2) d =
      ZMod.castHom h2r (ZMod 2) s) :
    ∃ x y : ZMod r, y - x = d ∧ y + x = s := by
  have hzero : ZMod.castHom h2r (ZMod 2) (s - d) = 0 := by
    rw [map_sub, ← hparity, sub_self]
  obtain ⟨x, hx⟩ :=
    (zmod_mem_range_two_mul_iff_castHom_eq_zero h2r (s - d)).mpr hzero
  have hx' : 2 * x = s - d := by simpa using hx
  refine ⟨x, x + d, ?_, ?_⟩
  · ring
  · change x + d + x = s
    calc
      x + d + x = 2 * x + d := by ring
      _ = (s - d) + d := by rw [hx']
      _ = s := by ring

/-- For a cycle-intertwining matrix, the simultaneous-translation
difference depends only on the coordinate sum. -/
theorem cycleIntertwiner_translationDifference_eq_of_add_eq
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    {x y x' y' : ZMod r} (hadd : y + x = y' + x') :
    H (x + 1) (y + 1) - H x y =
      H (x' + 1) (y' + 1) - H x' y' := by
  let Δ : Matrix (ZMod r) (ZMod r) ℤ :=
    fun a b ↦ H (a + 1) (b + 1) - H a b
  have hstep (a b : ZMod r) : Δ a b = Δ (a - 1) (b + 1) := by
    dsimp only [Δ]
    have h := hinter a (b + 1)
    rw [show b + 1 - 1 = b by ring] at h
    rw [show a - 1 + 1 = a by ring]
    linear_combination h
  have hrev : ∀ a b, Δ (a + 1) (b - 1) = Δ a b := by
    intro a b
    have h := hstep (a + 1) (b - 1)
    simpa only [add_sub_cancel_right, sub_add_cancel] using h
  exact reverseTranslationInvariant_eq_of_add_eq Δ hrev hadd

/-- A nonzero translation difference in a binary intertwiner makes its
entire cyclic anti-diagonal constant. -/
theorem binary_cycleIntertwiner_antidiagonal_constant_of_difference_ne_zero
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    {a b : ZMod r}
    (hne : H (a + 1) (b + 1) - H a b ≠ 0) :
    ∀ {x y : ZMod r}, y + x = b + a → H x y = H a b := by
  intro x y hsum
  have hδ := cycleIntertwiner_translationDifference_eq_of_add_eq
    H hinter hsum
  rcases hbinary a b with hab | hab <;>
    rcases hbinary (a + 1) (b + 1) with hab' | hab' <;>
    rcases hbinary x y with hxy | hxy <;>
    rcases hbinary (x + 1) (y + 1) with hxy' | hxy' <;>
    omega

/-- Equality of two entries on one anti-diagonal is preserved by a common
simultaneous shift. -/
theorem cycleIntertwiner_simultaneous_shift_preserves_eq
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    {x y x' y' : ZMod r} (hsum : y + x = y' + x')
    (heq : H x y = H x' y') : ∀ n : ℕ,
    H (x + (n : ZMod r)) (y + (n : ZMod r)) =
      H (x' + (n : ZMod r)) (y' + (n : ZMod r)) := by
  intro n
  induction n with
  | zero => simpa using heq
  | succ n ih =>
      have hsumN :
          (y + (n : ZMod r)) + (x + (n : ZMod r)) =
            (y' + (n : ZMod r)) + (x' + (n : ZMod r)) := by
        linear_combination hsum
      have hδ := cycleIntertwiner_translationDifference_eq_of_add_eq
        H hinter hsumN
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show x + ((n : ZMod r) + 1) = x + (n : ZMod r) + 1 by ring,
        show y + ((n : ZMod r) + 1) = y + (n : ZMod r) + 1 by ring,
        show x' + ((n : ZMod r) + 1) = x' + (n : ZMod r) + 1 by ring,
        show y' + ((n : ZMod r) + 1) = y' + (n : ZMod r) + 1 by ring]
      calc
        H (x + (n : ZMod r) + 1) (y + (n : ZMod r) + 1) =
            (H (x + (n : ZMod r) + 1) (y + (n : ZMod r) + 1) -
              H (x + (n : ZMod r)) (y + (n : ZMod r))) +
              H (x + (n : ZMod r)) (y + (n : ZMod r)) := by ring
        _ = (H (x' + (n : ZMod r) + 1) (y' + (n : ZMod r) + 1) -
              H (x' + (n : ZMod r)) (y' + (n : ZMod r))) +
              H (x' + (n : ZMod r)) (y' + (n : ZMod r)) := by
                rw [hδ, ih]
        _ = H (x' + (n : ZMod r) + 1) (y' + (n : ZMod r) + 1) := by ring

/-- On the doubling-image checkerboard, looplessness and intertwining make
the block depend only on coordinate difference. -/
theorem selfIntertwiner_eq_of_sub_eq_of_mem_range_two
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    {x y x' y' : ZMod r}
    (hhalf : y - x ∈ Set.range (fun t : ZMod r ↦ 2 * t))
    (hsub : y - x = y' - x') : H x y = H x' y' := by
  let t : ZMod r := x' - x
  have hhalf' : x - y ∈ Set.range (fun t : ZMod r ↦ 2 * t) := by
    obtain ⟨w, hw⟩ := hhalf
    change 2 * w = y - x at hw
    refine ⟨-w, ?_⟩
    change 2 * (-w) = x - y
    calc
      2 * (-w) = -(2 * w) := by ring
      _ = -(y - x) := by rw [hw]
      _ = x - y := by ring
  have hiter : ∀ n : ℕ,
      H (x + (n : ZMod r)) (y + (n : ZMod r)) = H x y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hdiff :
            (x + (n : ZMod r)) - (y + (n : ZMod r)) = x - y := by ring
        have hstep := selfIntertwiner_translationInvariant_of_mem_range_two_mul
          H hdiag hinter (x + (n : ZMod r)) (y + (n : ZMod r))
            (by simpa only [hdiff] using hhalf')
        simp only [Nat.cast_add, Nat.cast_one]
        rw [show x + ((n : ZMod r) + 1) = x + (n : ZMod r) + 1 by ring,
          show y + ((n : ZMod r) + 1) = y + (n : ZMod r) + 1 by ring,
          hstep, ih]
  have ht := hiter t.val
  rw [ZMod.natCast_zmod_val] at ht
  have hx : x + t = x' := by dsimp only [t]; ring
  have hy : y + t = y' := by
    dsimp only [t]
    rw [sub_eq_sub_iff_add_eq_add] at hsub
    linear_combination hsub
  rw [hx, hy] at ht
  exact ht.symm

/-- If one odd-checkerboard anti-diagonal has a nonzero translation
difference, binary rigidity propagates reverse-circulant dependence to every
odd-checkerboard anti-diagonal. -/
theorem binary_evenCycleIntertwiner_reverse_on_odd_checkerboard
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r)
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (hdiag : ∀ z, H z z = 0)
    {a b : ZMod r}
    (hne : H (a + 1) (b + 1) - H a b ≠ 0) :
    ∀ {x y x' y' : ZMod r},
      ZMod.castHom h2r (ZMod 2) (y - x) ≠ 0 →
      y + x = y' + x' → H x y = H x' y' := by
  intro x y x' y' hodd hsum
  let φ : ZMod r →+* ZMod 2 := ZMod.castHom h2r (ZMod 2)
  have hbaseOdd : φ (b - a) ≠ 0 := by
    intro hzero
    have hzero' : φ (a - b) = 0 := by
      rw [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
      simpa [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two,
        add_comm] using hzero
    have hrange := (zmod_mem_range_two_mul_iff_castHom_eq_zero h2r
      (a - b)).mpr hzero'
    have heq := selfIntertwiner_translationInvariant_of_mem_range_two_mul
      H hdiag hinter a b hrange
    apply hne
    omega
  have hsumParity : φ (y + x) = φ (b + a) := by
    have hyx : φ (y + x) ≠ 0 := by
      intro hz
      apply hodd
      change φ (y - x) = 0
      rw [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
      simpa [map_add] using hz
    have hba : φ (b + a) ≠ 0 := by
      intro hz
      apply hbaseOdd
      rw [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
      simpa [map_add] using hz
    have hone_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
      fin_cases z
      · exact (hz rfl).elim
      · rfl
    rw [hone_of_ne_zero _ hyx, hone_of_ne_zero _ hba]
  have hdiffZero : φ ((y + x) - (b + a)) = 0 := by
    simp only [map_sub, hsumParity, sub_self]
  obtain ⟨k, hk⟩ :=
    (zmod_mem_range_two_mul_iff_castHom_eq_zero h2r
      ((y + x) - (b + a))).mpr hdiffZero
  change 2 * k = (y + x) - (b + a) at hk
  let x₀ := x - k
  let y₀ := y - k
  let x₀' := x' - k
  let y₀' := y' - k
  have hbaseSum : y₀ + x₀ = b + a := by
    dsimp only [x₀, y₀]
    calc
      y - k + (x - k) = y + x - 2 * k := by ring
      _ = b + a := by rw [hk]; ring
  have hbaseSum' : y₀' + x₀' = b + a := by
    dsimp only [x₀', y₀']
    calc
      y' - k + (x' - k) = y' + x' - 2 * k := by ring
      _ = y + x - 2 * k := by rw [hsum]
      _ = b + a := by rw [hk]; ring
  have heq₀ : H x₀ y₀ = H x₀' y₀' := by
    rw [binary_cycleIntertwiner_antidiagonal_constant_of_difference_ne_zero
      H hinter hbinary hne hbaseSum,
      binary_cycleIntertwiner_antidiagonal_constant_of_difference_ne_zero
        H hinter hbinary hne hbaseSum']
  have hshift := cycleIntertwiner_simultaneous_shift_preserves_eq
    H hinter (hbaseSum.trans hbaseSum'.symm) heq₀ k.val
  rw [ZMod.natCast_zmod_val] at hshift
  simpa only [x₀, y₀, x₀', y₀', sub_add_cancel] using hshift

/-- **Mixed checkerboard orientations force a four-cycle.**  Suppose the
same-parity part of a cyclic adjacency block depends only on coordinate
difference, while the opposite-parity part depends only on coordinate sum.
In a `C4`-free graph, at most one of those two parts can contain an edge. -/
theorem no_edges_in_one_checkerboard_sector
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod r → V) (hu : Function.Injective u)
    (hcirc : ∀ {x y x' y' : ZMod r},
      ZMod.castHom h2r (ZMod 2) (y - x) = 0 →
      y - x = y' - x' →
      (G.Adj (u x) (u y) ↔ G.Adj (u x') (u y')))
    (hrev : ∀ {x y x' y' : ZMod r},
      ZMod.castHom h2r (ZMod 2) (y - x) ≠ 0 →
      y + x = y' + x' →
      (G.Adj (u x) (u y) ↔ G.Adj (u x') (u y'))) :
    (∀ x y : ZMod r,
        ZMod.castHom h2r (ZMod 2) (y - x) = 0 →
        ¬ G.Adj (u x) (u y)) ∨
      (∀ x y : ZMod r,
        ZMod.castHom h2r (ZMod 2) (y - x) ≠ 0 →
        ¬ G.Adj (u x) (u y)) := by
  classical
  let φ : ZMod r →+* ZMod 2 := ZMod.castHom h2r (ZMod 2)
  by_contra hnot
  push Not at hnot
  obtain ⟨⟨x, y, hxy0, hxy⟩, ⟨a, b, hab0, hab⟩⟩ := hnot
  let s : ZMod r := a + b
  let c : ZMod r := s - y
  let e : ZMod r := s - x
  have hφxy : φ y = φ x := by
    have h := hxy0
    simp only [map_sub] at h
    linear_combination h
  have hφab : φ a + φ b ≠ 0 := by
    intro hz
    apply hab0
    simp only [map_sub]
    change φ b - φ a = 0
    have hneg (z : ZMod 2) : -z = z := by
      fin_cases z <;> decide
    rw [sub_eq_add_neg, hneg]
    simpa [add_comm] using hz
  have hxe0 : φ (e - x) ≠ 0 := by
    dsimp only [e, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ x)
  have hyc0 : φ (c - y) ≠ 0 := by
    dsimp only [c, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ y)
  have hce0 : φ (e - c) = 0 := by
    dsimp only [e, c]
    have hdiff : e - c = y - x := by ring
    rw [hdiff]
    exact hxy0
  have hcx0 : φ (c - x) ≠ 0 := by
    dsimp only [c, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ x) + hφxy
  have hey0 : φ (e - y) ≠ 0 := by
    dsimp only [e, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ y) - hφxy
  have hxe : G.Adj (u x) (u e) := by
    apply (hrev hab0 (by dsimp [e, s]; ring)).mp hab
  have hyc : G.Adj (u y) (u c) := by
    apply (hrev hab0 (by dsimp [c, s]; ring)).mp hab
  have hce : G.Adj (u c) (u e) := by
    apply (hcirc hxy0 (by dsimp [c, e]; ring)).mp hxy
  have hxc : x ≠ c := by
    intro h
    apply hcx0
    rw [← h, sub_self, map_zero]
  have hye : y ≠ e := by
    intro h
    apply hey0
    rw [← h, sub_self, map_zero]
  have hucx : u c ≠ u x := fun h ↦ hxc (hu h).symm
  have huyue : u y ≠ u e := fun h ↦ hye (hu h)
  have hy_mem : u y ∈ G.neighborFinset (u x) ∩
      G.neighborFinset (u c) := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxy, hyc.symm⟩
  have he_mem : u e ∈ G.neighborFinset (u x) ∩
      G.neighborFinset (u c) := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxe, hce⟩
  have htwo : 2 ≤ (G.neighborFinset (u x) ∩
      G.neighborFinset (u c)).card := by
    have hsub : ({u y, u e} : Finset V) ⊆
        G.neighborFinset (u x) ∩ G.neighborFinset (u c) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hy_mem
      · exact he_mem
    have hcard : ({u y, u e} : Finset V).card = 2 := by
      simp [huyue]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hone := common_le_one_of_not_containsC4 hfree (u x) (u c) hucx.symm
  omega

/-- **Even-cycle diagonal-block orientation.**  A loopless binary
self-intertwiner coming from a `C4`-free graph is globally either circulant
or reverse-circulant, even when the cycle length is even.  The proof combines
the two checkerboard invariances with
`no_edges_in_one_checkerboard_sector`. -/
theorem graph_equalEvenCycle_diagBlock_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) (hrEven : Even r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod r → V) (huinj : Function.Injective u)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huD : ∀ x, D.neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) :
    (∀ x y, G.adjMatrix ℤ (u (x + 1)) (u (y + 1)) =
        G.adjMatrix ℤ (u x) (u y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (u (y - 1)) =
        G.adjMatrix ℤ (u x) (u y)) := by
  classical
  let H : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (u y)
  obtain ⟨q, hqr⟩ := hrEven
  have h2r : 2 ∣ r := ⟨q, by omega⟩
  let φ : ZMod r →+* ZMod 2 := ZMod.castHom h2r (ZMod 2)
  have hdiag : ∀ z, H z z = 0 := by
    intro z
    simp [H, SimpleGraph.adjMatrix_apply]
  have hupair : ∀ x, u (x - 1) ≠ u (x + 1) := fun x ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le hr3 x)
  have hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1) := by
    simpa only [H] using entry_cycleIntertwine_of_adjMatrix_comm
      G D u u (1 : ZMod r) (1 : ZMod r) hcomm huD huD hupair hupair
  have hbinary : ∀ x y, H x y = 0 ∨ H x y = 1 := by
    intro x y
    simp only [H, SimpleGraph.adjMatrix_apply]
    split <;> simp
  have hcircH : ∀ {x y x' y' : ZMod r},
      φ (y - x) = 0 → y - x = y' - x' → H x y = H x' y' := by
    intro x y x' y' hpar hsub
    exact selfIntertwiner_eq_of_sub_eq_of_mem_range_two H hdiag hinter
      ((zmod_mem_range_two_mul_iff_castHom_eq_zero h2r _).mpr hpar) hsub
  by_cases htrans : ∀ x y, H (x + 1) (y + 1) - H x y = 0
  · left
    intro x y
    exact sub_eq_zero.mp (htrans x y)
  · push Not at htrans
    obtain ⟨a, b, hab⟩ := htrans
    have hrevH : ∀ {x y x' y' : ZMod r},
        φ (y - x) ≠ 0 → y + x = y' + x' → H x y = H x' y' :=
      binary_evenCycleIntertwiner_reverse_on_odd_checkerboard
        h2r H hinter hbinary hdiag hab
    have entry_iff {x y x' y' : ZMod r} (h : H x y = H x' y') :
        G.Adj (u x) (u y) ↔ G.Adj (u x') (u y') := by
      simp only [H, SimpleGraph.adjMatrix_apply] at h
      by_cases h₁ : G.Adj (u x) (u y) <;>
        by_cases h₂ : G.Adj (u x') (u y') <;> simp_all
    have hsectors := no_edges_in_one_checkerboard_sector h2r G hfree u
      huinj (fun hpar hsub ↦ entry_iff (hcircH hpar hsub))
        (fun hpar hsum ↦ entry_iff (hrevH hpar hsum))
    rcases hsectors with hnoEven | hnoOdd
    · right
      intro x y
      by_cases hpar : φ (y - x) = 0
      · have hpar' : φ ((y - 1) - (x + 1)) = 0 := by
          have hdiff : (y - 1) - (x + 1) = (y - x) - 2 := by ring
          rw [hdiff, map_sub, hpar]
          have htwo : φ (2 : ZMod r) = 0 := by
            rw [map_ofNat]
            exact ZMod.natCast_self 2
          rw [htwo, sub_zero]
        have h0 : H x y = 0 := by
          simp only [H, SimpleGraph.adjMatrix_apply]
          rw [if_neg (hnoEven x y hpar)]
        have h0' : H (x + 1) (y - 1) = 0 := by
          simp only [H, SimpleGraph.adjMatrix_apply]
          rw [if_neg (hnoEven (x + 1) (y - 1) hpar')]
        simpa only [H, h0, h0']
      · exact (hrevH hpar (by ring)).symm
    · left
      intro x y
      by_cases hpar : φ (y - x) = 0
      · exact (hcircH hpar (by ring)).symm
      · have hpar' : φ ((y + 1) - (x + 1)) ≠ 0 := by
          simpa only [show (y + 1) - (x + 1) = y - x by ring] using hpar
        have h0 : H x y = 0 := by
          simp only [H, SimpleGraph.adjMatrix_apply]
          rw [if_neg (hnoOdd x y hpar)]
        have h0' : H (x + 1) (y + 1) = 0 := by
          simp only [H, SimpleGraph.adjMatrix_apply]
          rw [if_neg (hnoOdd (x + 1) (y + 1) hpar')]
        simpa only [H, h0, h0']

/-- Uniform odd/even wrapper: every labeled diagonal block of a commuting
cycle factor in a `C4`-free graph has a global cyclic orientation. -/
theorem graph_cycle_diagBlock_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod r → V) (huinj : Function.Injective u)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huD : ∀ x, D.neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) :
    (∀ x y, G.adjMatrix ℤ (u (x + 1)) (u (y + 1)) =
        G.adjMatrix ℤ (u x) (u y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (u (y - 1)) =
        G.adjMatrix ℤ (u x) (u y)) := by
  rcases Nat.even_or_odd r with hrEven | hrOdd
  · exact graph_equalEvenCycle_diagBlock_orientation hr3 hrEven G D hfree
      u huinj hcomm huD
  · exact Or.inl (graph_equalOddCycle_diagBlock_translationInvariant
      hr3 hrOdd G D u huinj hcomm huD)

/-- Field-valued form consumed by the frequency projector trace layer. -/
theorem graph_cycle_diagBlock_orientation_field
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod r → V) (huinj : Function.Injective u)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huD : ∀ x, D.neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) :
    (∀ x y, G.adjMatrix K (u (x + 1)) (u (y + 1)) =
        G.adjMatrix K (u x) (u y)) ∨
      (∀ x y, G.adjMatrix K (u (x + 1)) (u (y - 1)) =
        G.adjMatrix K (u x) (u y)) := by
  rcases graph_cycle_diagBlock_orientation hr3 G D hfree u huinj hcomm
    huD with htrans | hrev
  · left
    intro x y
    have h := htrans x y
    simp only [SimpleGraph.adjMatrix_apply] at h ⊢
    by_cases h₁ : G.Adj (u (x + 1)) (u (y + 1)) <;>
      by_cases h₂ : G.Adj (u x) (u y) <;> simp_all
  · right
    intro x y
    have h := hrev x y
    simp only [SimpleGraph.adjMatrix_apply] at h ⊢
    by_cases h₁ : G.Adj (u (x + 1)) (u (y - 1)) <;>
      by_cases h₂ : G.Adj (u x) (u y) <;> simp_all

end

end Erdos85
