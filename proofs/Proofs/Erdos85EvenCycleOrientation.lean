import Proofs.Erdos85BinaryCycleIntertwiner
import Proofs.Erdos85EvenCycleSelfIntertwiner
import Proofs.Erdos85FrequencyPairGraphBlocks
import Proofs.Erdos85MixedAnchorSupport
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

/-- If a square block commutes with a symmetric operator, then its row Gram
also commutes with that operator.  This is the algebraic bridge from an
off-diagonal cycle block to the diagonal common-neighbor block. -/
theorem Matrix.mul_transpose_gram_comm_of_comm
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (A B : Matrix ι ι R) (hA : Matrix.transpose A = A)
    (hAB : A * B = B * A) :
    A * (B * Matrix.transpose B) =
      (B * Matrix.transpose B) * A := by
  have hBtA : Matrix.transpose B * A =
      A * Matrix.transpose B := by
    have h := congrArg Matrix.transpose hAB
    simpa only [Matrix.transpose_mul, hA] using h
  calc
    A * (B * Matrix.transpose B) =
        (A * B) * Matrix.transpose B := by rw [Matrix.mul_assoc]
    _ = (B * A) * Matrix.transpose B := by rw [hAB]
    _ = B * (A * Matrix.transpose B) := by rw [Matrix.mul_assoc]
    _ = B * (Matrix.transpose B * A) := by rw [hBtA]
    _ = (B * Matrix.transpose B) * A := by rw [Matrix.mul_assoc]

/-- The column Gram of a square block commuting with a symmetric operator
commutes with the same operator as well. -/
theorem Matrix.transpose_mul_gram_comm_of_comm
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (A B : Matrix ι ι R) (hA : Matrix.transpose A = A)
    (hAB : A * B = B * A) :
    A * (Matrix.transpose B * B) =
      (Matrix.transpose B * B) * A := by
  have hBtA : Matrix.transpose B * A =
      A * Matrix.transpose B := by
    have h := congrArg Matrix.transpose hAB
    simpa only [Matrix.transpose_mul, hA] using h
  calc
    A * (Matrix.transpose B * B) =
        (A * Matrix.transpose B) * B := by rw [Matrix.mul_assoc]
    _ = (Matrix.transpose B * A) * B := by rw [hBtA]
    _ = Matrix.transpose B * (A * B) := by rw [Matrix.mul_assoc]
    _ = Matrix.transpose B * (B * A) := by rw [hAB]
    _ = (Matrix.transpose B * B) * A := by rw [Matrix.mul_assoc]

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

/-- Exact parity criterion for disjoint forward and reverse cyclic
diagonals in an even modulus. -/
theorem forward_reverse_diagonals_disjoint_iff_castHom_ne
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r) (d s : ZMod r) :
    (¬ ∃ x y : ZMod r, y - x = d ∧ y + x = s) ↔
      ZMod.castHom h2r (ZMod 2) d ≠
        ZMod.castHom h2r (ZMod 2) s := by
  constructor
  · intro hdisjoint hparity
    exact hdisjoint
      (exists_forward_reverse_diagonal_intersection_of_castHom_eq
        h2r d s hparity)
  · exact forward_reverse_diagonals_disjoint_of_castHom_ne h2r d s

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

/-- Any nonzero simultaneous-translation defect of a binary cycle
intertwiner forces a complete reverse diagonal of ones.  This is the first
half of the quotient-two decomposition: the diagonal is a reverse perfect
matching which can be split from the block. -/
theorem binary_cycleIntertwiner_exists_full_reverse_diagonal
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    {a b : ZMod r}
    (hne : H (a + 1) (b + 1) - H a b ≠ 0) :
    ∃ s : ZMod r, ∀ x, H x (s - x) = 1 := by
  rcases hbinary a b with hab | hab
  · have hab' : H (a + 1) (b + 1) = 1 := by
      rcases hbinary (a + 1) (b + 1) with hab' | hab'
      · exact (hne (by rw [hab, hab']; norm_num)).elim
      · exact hab'
    refine ⟨b + a + 2, ?_⟩
    intro x
    let x₀ : ZMod r := x - 1
    let y₀ : ZMod r := (b + a + 2 - x) - 1
    have hsum : y₀ + x₀ = b + a := by
      dsimp only [x₀, y₀]
      ring
    have hbase : H x₀ y₀ = H a b :=
      binary_cycleIntertwiner_antidiagonal_constant_of_difference_ne_zero
        H hinter hbinary hne hsum
    have hdelta := cycleIntertwiner_translationDifference_eq_of_add_eq
      H hinter hsum
    have hx : x₀ + 1 = x := by dsimp only [x₀]; ring
    have hy : y₀ + 1 = b + a + 2 - x := by dsimp only [y₀]; ring
    rw [hx, hy, hbase, hab, hab'] at hdelta
    omega
  · refine ⟨b + a, ?_⟩
    intro x
    have hsum : (b + a - x) + x = b + a := by ring
    calc
      H x (b + a - x) = H a b :=
        binary_cycleIntertwiner_antidiagonal_constant_of_difference_ne_zero
          H hinter hbinary hne hsum
      _ = 1 := hab

/-- The permutation matrix of the reverse matching `y = s - x`. -/
def reverseMatchingMatrix {r : ℕ} [NeZero r] (s : ZMod r) :
    Matrix (ZMod r) (ZMod r) ℤ :=
  fun x y ↦ if y = s - x then 1 else 0

/-- A reverse matching intertwines the two cycle adjacency operators. -/
theorem reverseMatchingMatrix_entry_intertwine
    {r : ℕ} [NeZero r] (s x y : ZMod r) :
    reverseMatchingMatrix s (x - 1) y +
        reverseMatchingMatrix s (x + 1) y =
      reverseMatchingMatrix s x (y + 1) +
        reverseMatchingMatrix s x (y - 1) := by
  have h₁ : (y = s - (x - 1)) ↔ (y - 1 = s - x) := by
    constructor <;> intro h
    · rw [h]
      ring
    · linear_combination h
  have h₂ : (y = s - (x + 1)) ↔ (y + 1 = s - x) := by
    constructor <;> intro h
    · rw [h]
      ring
    · linear_combination h
  simp only [reverseMatchingMatrix, h₁, h₂]
  ring

/-- Splitting a full reverse matching from a cycle intertwiner leaves another
cycle intertwiner. -/
theorem sub_reverseMatchingMatrix_entry_intertwine
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (s x y : ZMod r) :
    (H - reverseMatchingMatrix s) (x - 1) y +
        (H - reverseMatchingMatrix s) (x + 1) y =
      (H - reverseMatchingMatrix s) x (y + 1) +
        (H - reverseMatchingMatrix s) x (y - 1) := by
  simp only [Matrix.sub_apply]
  linear_combination hinter x y -
    reverseMatchingMatrix_entry_intertwine s x y

/-- If a binary block contains a full reverse matching, subtracting that
matching leaves another binary block. -/
theorem sub_reverseMatchingMatrix_binary
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (s : ZMod r) (hfull : ∀ x, H x (s - x) = 1) :
    ∀ x y, (H - reverseMatchingMatrix s) x y = 0 ∨
      (H - reverseMatchingMatrix s) x y = 1 := by
  intro x y
  by_cases hy : y = s - x
  · left
    simp [Matrix.sub_apply, reverseMatchingMatrix, hy, hfull x]
  · simpa [Matrix.sub_apply, reverseMatchingMatrix, hy] using hbinary x y

/-- Every row of a reverse matching matrix has sum one. -/
theorem reverseMatchingMatrix_row_sum
    {r : ℕ} [NeZero r] (s x : ZMod r) :
    ∑ y, reverseMatchingMatrix s x y = 1 := by
  classical
  simp [reverseMatchingMatrix]

/-- Every column of a reverse matching matrix has sum one. -/
theorem reverseMatchingMatrix_column_sum
    {r : ℕ} [NeZero r] (s y : ZMod r) :
    ∑ x, reverseMatchingMatrix s x y = 1 := by
  classical
  calc
    (∑ x, reverseMatchingMatrix s x y) =
        ∑ x, reverseMatchingMatrix s y x := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [reverseMatchingMatrix]
      congr 1
      apply propext
      constructor <;> intro h
      · linear_combination h
      · linear_combination h
    _ = 1 := reverseMatchingMatrix_row_sum s y

/-- Removing a reverse matching from a row-two block leaves row sum one. -/
theorem sub_reverseMatchingMatrix_row_sum_eq_one
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hrow : ∀ x, ∑ y, H x y = 2) (s x : ZMod r) :
    ∑ y, (H - reverseMatchingMatrix s) x y = 1 := by
  simp_rw [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib, hrow, reverseMatchingMatrix_row_sum]
  norm_num

/-- Removing a reverse matching from a column-two block leaves column sum
one as well. -/
theorem sub_reverseMatchingMatrix_column_sum_eq_one
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hcol : ∀ y, ∑ x, H x y = 2) (s y : ZMod r) :
    ∑ x, (H - reverseMatchingMatrix s) x y = 1 := by
  simp_rw [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib, hcol, reverseMatchingMatrix_column_sum]
  norm_num

/-- Removing a reverse matching from a row-three block leaves row sum two. -/
theorem sub_reverseMatchingMatrix_row_sum_eq_two
    {r : ℕ} [NeZero r]
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hrow : ∀ x, ∑ y, H x y = 3) (s x : ZMod r) :
    ∑ y, (H - reverseMatchingMatrix s) x y = 2 := by
  simp_rw [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib, hrow, reverseMatchingMatrix_row_sum]
  norm_num

/-- A binary matrix with every row summing to one is the graph of a unique
row selector. -/
theorem exists_rowSelector_of_binary_row_sum_one
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (P : Matrix α β ℤ)
    (hbinary : ∀ x y, P x y = 0 ∨ P x y = 1)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    ∃ f : α → β, ∀ x y, P x y = 1 ↔ y = f x := by
  classical
  let S : α → Finset β := fun x => Finset.univ.filter fun y => P x y = 1
  have hcard : ∀ x, (S x).card = 1 := by
    intro x
    have heq : (∑ y, P x y) = ((S x).card : ℤ) := by
      calc
        (∑ y, P x y) = ∑ y, if P x y = 1 then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro y _hy
          rcases hbinary x y with hzero | hone
          · simp [hzero]
          · simp [hone]
        _ = ((S x).card : ℤ) := by
          simpa only [S] using (Finset.sum_boole (R := ℤ)
            (fun y : β => P x y = 1) Finset.univ)
    have hz : ((S x).card : ℤ) = 1 := by rw [← heq, hrow]
    exact_mod_cast hz
  have hex : ∀ x, ∃ y, S x = {y} := fun x => Finset.card_eq_one.mp (hcard x)
  choose f hf using hex
  refine ⟨f, ?_⟩
  intro x y
  have hmem : y ∈ S x ↔ P x y = 1 := by simp [S]
  rw [← hmem, hf]
  simp

/-- A binary row-one square cycle intertwiner is a globally oriented cyclic
matching.  This is the matrix-level quotient-one rigidity consumed by the
residual quotient-two decomposition. -/
theorem binary_rowOne_cycleIntertwiner_orientation
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (P : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      P (x - 1) y + P (x + 1) y =
        P x (y + 1) + P x (y - 1))
    (hbinary : ∀ x y, P x y = 0 ∨ P x y = 1)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    ∃ f : ZMod r → ZMod r,
      (∀ x y, P x y = 1 ↔ y = f x) ∧
      ((∀ x, f (x + 1) = f x + 1) ∨
        (∀ x, f (x + 1) = f x - 1)) := by
  obtain ⟨f, hf⟩ := exists_rowSelector_of_binary_row_sum_one P hbinary hrow
  refine ⟨f, hf, cycleMap_global_orientation hr3 f ?_⟩
  intro x
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have happly : ∀ a b, P a b = if b = f a then 1 else 0 := by
    intro a b
    by_cases h : b = f a
    · rw [if_pos h]
      exact (hf a b).2 h
    · rw [if_neg h]
      rcases hbinary a b with hzero | hone
      · exact hzero
      · exact (h (hf a b |>.1 hone)).elim
  have hrec := hinter x y
  simp only [happly] at hrec
  have hsub : y + 1 = f x ↔ y = f x - 1 := by
    constructor <;> intro h
    · linear_combination h
    · rw [h]
      ring
  have hadd : y - 1 = f x ↔ y = f x + 1 := by
    constructor <;> intro h
    · linear_combination h
    · rw [h]
      ring
  simp only [hsub, hadd] at hrec
  have hpm : f x - 1 ≠ f x + 1 :=
    zmod_sub_one_ne_add_one_of_three_le hr3 (f x)
  by_cases h₁ : y = f (x - 1) <;>
    by_cases h₂ : y = f (x + 1) <;>
    by_cases h₃ : y = f x - 1 <;>
    by_cases h₄ : y = f x + 1 <;>
    simp_all [eq_comm]

/-- The reverse matching matrix is globally reverse-circulant. -/
theorem reverseMatchingMatrix_reverseInvariant
    {r : ℕ} [NeZero r] (s x y : ZMod r) :
    reverseMatchingMatrix s (x + 1) (y - 1) =
      reverseMatchingMatrix s x y := by
  simp only [reverseMatchingMatrix]
  congr 1
  apply propext
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

/-- A binary selector matrix inherits the global reverse orientation of its
selector. -/
theorem binary_selectorMatrix_reverseInvariant
    {r : ℕ} [NeZero r]
    (P : Matrix (ZMod r) (ZMod r) ℤ)
    (hbinary : ∀ x y, P x y = 0 ∨ P x y = 1)
    (f : ZMod r → ZMod r)
    (hf : ∀ x y, P x y = 1 ↔ y = f x)
    (hrev : ∀ x, f (x + 1) = f x - 1) :
    ∀ x y, P (x + 1) (y - 1) = P x y := by
  intro x y
  have hiff : y - 1 = f (x + 1) ↔ y = f x := by
    rw [hrev]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  rcases hbinary (x + 1) (y - 1) with h₁ | h₁ <;>
    rcases hbinary x y with h₂ | h₂ <;> try omega
  · exfalso
    have hone := (hf (x + 1) (y - 1)).2
      (hiff.mpr ((hf x y).1 h₂))
    omega
  · exfalso
    have hone := (hf x y).2
      (hiff.mp ((hf (x + 1) (y - 1)).1 h₁))
    omega

/-- A forward cyclic matching and a reverse cyclic matching on the same
cycle swap their two targets at a distinct source position whenever their
targets at zero are distinct. -/
theorem forward_reverse_matchings_swap
    {r : ℕ} [NeZero r]
    (f g : ZMod r → ZMod r)
    (hf : ∀ y, f (y + 1) = f y + 1)
    (hg : ∀ y, g (y + 1) = g y - 1)
    (hfg : f 0 ≠ g 0) :
    ∃ y : ZMod r, y ≠ 0 ∧ f y = g 0 ∧ g y = f 0 := by
  have hf_formula : ∀ y : ZMod r, f y = f 0 + y := by
    intro y
    have hind : ∀ n : ℕ,
        f (n : ZMod r) = f 0 + (n : ZMod r) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Nat.cast_succ, hf, ih]
          ring
    simpa only [ZMod.natCast_zmod_val] using hind y.val
  have hg_formula : ∀ y : ZMod r, g y = g 0 - y := by
    intro y
    have hind : ∀ n : ℕ,
        g (n : ZMod r) = g 0 - (n : ZMod r) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Nat.cast_succ, hg, ih]
          ring
    simpa only [ZMod.natCast_zmod_val] using hind y.val
  let y : ZMod r := g 0 - f 0
  have hy : y ≠ 0 := by
    intro hy0
    apply hfg
    dsimp only [y] at hy0
    exact sub_eq_zero.mp hy0 |>.symm
  refine ⟨y, hy, ?_, ?_⟩
  · rw [hf_formula]
    dsimp only [y]
    ring
  · rw [hg_formula]
    dsimp only [y]
    ring

/-- **Equal-cycle quotient-two orientation.**  A binary two-regular square
cycle intertwiner with no `2 × 2` all-one rectangle is globally circulant or
reverse-circulant, at every cycle length at least three.  The proof splits a
reverse matching from any translation defect; the residual quotient-one
matching is globally oriented, and a forward residual would form a forbidden
rectangle with the reverse matching. -/
theorem binary_rowTwo_cycleIntertwiner_orientation
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (hrow : ∀ x, ∑ y, H x y = 2)
    (hrect : ∀ x x', x ≠ x' → ∀ y y', y ≠ y' →
      ¬ (H x y = 1 ∧ H x y' = 1 ∧
        H x' y = 1 ∧ H x' y' = 1)) :
    (∀ x y, H (x + 1) (y + 1) = H x y) ∨
      (∀ x y, H (x + 1) (y - 1) = H x y) := by
  by_cases htrans : ∀ x y, H (x + 1) (y + 1) = H x y
  · exact Or.inl htrans
  · push Not at htrans
    obtain ⟨a, b, hab⟩ := htrans
    have hne : H (a + 1) (b + 1) - H a b ≠ 0 := by
      intro hzero
      exact hab (sub_eq_zero.mp hzero)
    obtain ⟨s, hfull⟩ :=
      binary_cycleIntertwiner_exists_full_reverse_diagonal
        H hinter hbinary hne
    let P := H - reverseMatchingMatrix s
    have hinterP : ∀ x y,
        P (x - 1) y + P (x + 1) y =
          P x (y + 1) + P x (y - 1) :=
      sub_reverseMatchingMatrix_entry_intertwine H hinter s
    have hbinaryP : ∀ x y, P x y = 0 ∨ P x y = 1 :=
      sub_reverseMatchingMatrix_binary H hbinary s hfull
    have hrowP : ∀ x, ∑ y, P x y = 1 :=
      sub_reverseMatchingMatrix_row_sum_eq_one H hrow s
    obtain ⟨f, hf, hfor | hrev⟩ :=
      binary_rowOne_cycleIntertwiner_orientation hr3 P hinterP hbinaryP hrowP
    · let g : ZMod r → ZMod r := fun x => s - x
      have hg : ∀ x, g (x + 1) = g x - 1 := by
        intro x
        dsimp only [g]
        ring
      have hfg : f 0 ≠ g 0 := by
        intro heq
        have hpone : P 0 (f 0) = 1 := (hf 0 (f 0)).2 rfl
        have hpzero : P 0 (g 0) = 0 := by
          have hg0 : g 0 = s := by dsimp only [g]; ring
          have hfull0 : H 0 s = 1 := by simpa using hfull 0
          dsimp only [P]
          rw [hg0]
          simp [Matrix.sub_apply, reverseMatchingMatrix, hfull0]
        rw [heq, hpzero] at hpone
        norm_num at hpone
      obtain ⟨x', hx', hfx', hgx'⟩ :=
        forward_reverse_matchings_swap f g hfor hg hfg
      have honeP (x : ZMod r) : P x (f x) = 1 := (hf x (f x)).2 rfl
      have honeR (x : ZMod r) : H x (g x) = 1 := by
        simpa only [g] using hfull x
      have honeH (x : ZMod r) : H x (f x) = 1 := by
        have hp := honeP x
        dsimp only [P] at hp
        simp only [Matrix.sub_apply, reverseMatchingMatrix] at hp
        rcases hbinary x (f x) with hz | ho <;>
          split at hp <;> omega
      exfalso
      apply (hrect 0 x' hx'.symm (f 0) (g 0) hfg)
      refine ⟨honeH 0, honeR 0, ?_, ?_⟩
      · simpa only [hgx'] using honeR x'
      · simpa only [hfx'] using honeH x'
    · right
      have hrevP := binary_selectorMatrix_reverseInvariant
        P hbinaryP f hf hrev
      intro x y
      have hp := hrevP x y
      have hr := reverseMatchingMatrix_reverseInvariant s x y
      dsimp only [P] at hp
      simp only [Matrix.sub_apply] at hp
      linear_combination hp + hr

/-- **Equal-cycle quotient-three orientation.**  The reverse-matching split
reduces a non-circulant row-three block to the row-two theorem above.  A
forward residual contains a forward perfect matching, which forms a
forbidden rectangle with the split reverse matching; a reverse residual
makes the original block globally reverse-circulant. -/
theorem binary_rowThree_cycleIntertwiner_orientation
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (H : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (hrow : ∀ x, ∑ y, H x y = 3)
    (hrect : ∀ x x', x ≠ x' → ∀ y y', y ≠ y' →
      ¬ (H x y = 1 ∧ H x y' = 1 ∧
        H x' y = 1 ∧ H x' y' = 1)) :
    (∀ x y, H (x + 1) (y + 1) = H x y) ∨
      (∀ x y, H (x + 1) (y - 1) = H x y) := by
  by_cases htrans : ∀ x y, H (x + 1) (y + 1) = H x y
  · exact Or.inl htrans
  · push Not at htrans
    obtain ⟨a, b, hab⟩ := htrans
    have hne : H (a + 1) (b + 1) - H a b ≠ 0 := by
      intro hzero
      exact hab (sub_eq_zero.mp hzero)
    obtain ⟨s, hfull⟩ :=
      binary_cycleIntertwiner_exists_full_reverse_diagonal
        H hinter hbinary hne
    let P := H - reverseMatchingMatrix s
    have hinterP : ∀ x y,
        P (x - 1) y + P (x + 1) y =
          P x (y + 1) + P x (y - 1) :=
      sub_reverseMatchingMatrix_entry_intertwine H hinter s
    have hbinaryP : ∀ x y, P x y = 0 ∨ P x y = 1 :=
      sub_reverseMatchingMatrix_binary H hbinary s hfull
    have hrowP : ∀ x, ∑ y, P x y = 2 :=
      sub_reverseMatchingMatrix_row_sum_eq_two H hrow s
    have hrectP : ∀ x x', x ≠ x' → ∀ y y', y ≠ y' →
        ¬ (P x y = 1 ∧ P x y' = 1 ∧
          P x' y = 1 ∧ P x' y' = 1) := by
      intro x x' hxx' y y' hyy' hp
      apply hrect x x' hxx' y y' hyy'
      have honeH (z w : ZMod r) (hone : P z w = 1) : H z w = 1 := by
        dsimp only [P] at hone
        simp only [Matrix.sub_apply, reverseMatchingMatrix] at hone
        rcases hbinary z w with hz | ho <;> split at hone <;> omega
      exact ⟨honeH x y hp.1, honeH x y' hp.2.1,
        honeH x' y hp.2.2.1, honeH x' y' hp.2.2.2⟩
    rcases binary_rowTwo_cycleIntertwiner_orientation hr3 P hinterP
      hbinaryP hrowP hrectP with hforP | hrevP
    · have hex : ∃ y, P 0 y = 1 := by
        by_contra hnot
        push Not at hnot
        have hzero : ∀ y, P 0 y = 0 := by
          intro y
          rcases hbinaryP 0 y with hz | ho
          · exact hz
          · exact (hnot y ho).elim
        have hsum : (∑ y, P 0 y) = 0 := by simp [hzero]
        rw [hrowP] at hsum
        norm_num at hsum
      obtain ⟨f0, hf0⟩ := hex
      let f : ZMod r → ZMod r := fun x => f0 + x
      have hf : ∀ x, P x (f x) = 1 := by
        intro x
        have hind : ∀ n : ℕ, P (n : ZMod r) (f (n : ZMod r)) = 1 := by
          intro n
          induction n with
          | zero => simpa [f] using hf0
          | succ n ih =>
              rw [Nat.cast_succ]
              have hs := hforP (n : ZMod r) (f (n : ZMod r))
              have hfn : f ((n : ZMod r) + 1) = f (n : ZMod r) + 1 := by
                dsimp only [f]
                ring
              rw [hfn, hs]
              exact ih
        simpa only [ZMod.natCast_zmod_val] using hind x.val
      have hfor : ∀ x, f (x + 1) = f x + 1 := by
        intro x
        dsimp only [f]
        ring
      let g : ZMod r → ZMod r := fun x => s - x
      have hg : ∀ x, g (x + 1) = g x - 1 := by
        intro x
        dsimp only [g]
        ring
      have hfg : f 0 ≠ g 0 := by
        intro heq
        have hpone := hf 0
        have hg0 : g 0 = s := by dsimp only [g]; ring
        have hfull0 : H 0 s = 1 := by simpa using hfull 0
        dsimp only [P] at hpone
        rw [heq, hg0] at hpone
        simp [Matrix.sub_apply, reverseMatchingMatrix, hfull0] at hpone
      obtain ⟨x', hx', hfx', hgx'⟩ :=
        forward_reverse_matchings_swap f g hfor hg hfg
      have honeR (x : ZMod r) : H x (g x) = 1 := by
        simpa only [g] using hfull x
      have honeH (x : ZMod r) : H x (f x) = 1 := by
        have hp := hf x
        dsimp only [P] at hp
        simp only [Matrix.sub_apply, reverseMatchingMatrix] at hp
        rcases hbinary x (f x) with hz | ho <;> split at hp <;> omega
      exfalso
      apply hrect 0 x' hx'.symm (f 0) (g 0) hfg
      refine ⟨honeH 0, honeR 0, ?_, ?_⟩
      · simpa only [hgx'] using honeR x'
      · simpa only [hfx'] using honeH x'
    · right
      intro x y
      have hp := hrevP x y
      have hr := reverseMatchingMatrix_reverseInvariant s x y
      dsimp only [P] at hp
      simp only [Matrix.sub_apply] at hp
      linear_combination hp + hr

/-- Graph-facing equal-cycle quotient-two orientation.  If every vertex of
the first labeled defect cycle has exactly two neighbors on the second, then
C4-freeness and block commutation force the whole block to have one global
cyclic orientation, with no parity restriction on the cycle length. -/
theorem graph_equalCycleBlock_quotientTwo_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u v : ZMod r → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hvD : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)})
    (htwo : ∀ x, (mixedAnchorSupport G (u x) v).card = 2) :
    (∀ x y, G.Adj (u (x + 1)) (v (y + 1)) ↔ G.Adj (u x) (v y)) ∨
      (∀ x y, G.Adj (u (x + 1)) (v (y - 1)) ↔ G.Adj (u x) (v y)) := by
  classical
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y => G.adjMatrix ℤ (u x) (v y)
  have hupair : ∀ x, u (x - 1) ≠ u (x + 1) := fun x =>
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le hr3 x)
  have hvpair : ∀ y, v (y - 1) ≠ v (y + 1) := fun y =>
    hvinj.ne (zmod_sub_one_ne_add_one_of_three_le hr3 y)
  have hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1) := by
    simpa only [B] using entry_cycleIntertwine_of_adjMatrix_comm
      G D u v (1 : ZMod r) (1 : ZMod r) hcomm huD hvD hupair hvpair
  have hbinary : ∀ x y, B x y = 0 ∨ B x y = 1 := by
    intro x y
    simp only [B, SimpleGraph.adjMatrix_apply]
    split <;> simp
  have hrow : ∀ x, ∑ y, B x y = 2 := by
    intro x
    calc
      (∑ y, B x y) = ∑ y, if G.Adj (u x) (v y) then (1 : ℤ) else 0 := by
        rfl
      _ = ((mixedAnchorSupport G (u x) v).card : ℤ) := by
        simpa only [mixedAnchorSupport] using (Finset.sum_boole (R := ℤ)
          (fun y : ZMod r => G.Adj (u x) (v y)) Finset.univ)
      _ = 2 := by rw [htwo]; norm_num
  have hrect : ∀ x x', x ≠ x' → ∀ y y', y ≠ y' →
      ¬ (B x y = 1 ∧ B x y' = 1 ∧
        B x' y = 1 ∧ B x' y' = 1) := by
    intro x x' hxx' y y' hyy' hones
    have hux : u x ≠ u x' := huinj.ne hxx'
    have hvy : v y ≠ v y' := hvinj.ne hyy'
    have hone_iff (a b : ZMod r) : B a b = 1 ↔ G.Adj (u a) (v b) := by
      simp only [B, SimpleGraph.adjMatrix_apply]
      by_cases h : G.Adj (u a) (v b) <;> simp [h]
    have hy : v y ∈ G.neighborFinset (u x) ∩
        G.neighborFinset (u x') := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨(hone_iff x y).mp hones.1,
        (hone_iff x' y).mp hones.2.2.1⟩
    have hy' : v y' ∈ G.neighborFinset (u x) ∩
        G.neighborFinset (u x') := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨(hone_iff x y').mp hones.2.1,
        (hone_iff x' y').mp hones.2.2.2⟩
    have htwoCommon : 2 ≤ (G.neighborFinset (u x) ∩
        G.neighborFinset (u x')).card := by
      have hsub : ({v y, v y'} : Finset V) ⊆
          G.neighborFinset (u x) ∩ G.neighborFinset (u x') := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hy
        · exact hy'
      have hc : ({v y, v y'} : Finset V).card = 2 := by simp [hvy]
      rw [← hc]
      exact Finset.card_le_card hsub
    have honeCommon := common_le_one_of_not_containsC4 hfree
      (u x) (u x') hux
    omega
  rcases binary_rowTwo_cycleIntertwiner_orientation hr3 B hinter hbinary
    hrow hrect with hforward | hreverse
  · left
    intro x y
    have h := hforward x y
    simp only [B, SimpleGraph.adjMatrix_apply] at h
    by_cases h₁ : G.Adj (u (x + 1)) (v (y + 1)) <;>
      by_cases h₂ : G.Adj (u x) (v y) <;> simp_all
  · right
    intro x y
    have h := hreverse x y
    simp only [B, SimpleGraph.adjMatrix_apply] at h
    by_cases h₁ : G.Adj (u (x + 1)) (v (y - 1)) <;>
      by_cases h₂ : G.Adj (u x) (v y) <;> simp_all

/-- Boundary-component wrapper for the parity-independent quotient-two
orientation theorem. -/
theorem graph_equalComponent_quotientTwo_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (u v : ZMod r → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (htwo : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 2) :
    (∀ x y, G.Adj (u (x + 1)) (v (y + 1)) ↔ G.Adj (u x) (v y)) ∨
      (∀ x y, G.Adj (u (x + 1)) (v (y - 1)) ↔ G.Adj (u x) (v y)) := by
  apply graph_equalCycleBlock_quotientTwo_orientation hr3 G
    (secondOrderDefectGraph G) hfree u v huinj hvinj
    (adjMatrix_comm_secondOrderDefect_of_even
      G hfree hd heven hmin hcard) huD hvD
  intro x
  have hx : u x ∈ c.supp := by
    rw [← huRange]
    exact ⟨x, rfl⟩
  rw [card_mixedAnchorSupport_eq_componentQuotient
    G hfree hd heven hmin hcard c e hx hvinj hvRange, htwo]

/-- Graph-facing equal-cycle quotient-three orientation, with no parity
restriction on the common cycle length. -/
theorem graph_equalCycleBlock_quotientThree_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u v : ZMod r → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hvD : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)})
    (hthree : ∀ x, (mixedAnchorSupport G (u x) v).card = 3) :
    (∀ x y, G.Adj (u (x + 1)) (v (y + 1)) ↔ G.Adj (u x) (v y)) ∨
      (∀ x y, G.Adj (u (x + 1)) (v (y - 1)) ↔ G.Adj (u x) (v y)) := by
  classical
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y => G.adjMatrix ℤ (u x) (v y)
  have hupair : ∀ x, u (x - 1) ≠ u (x + 1) := fun x =>
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le hr3 x)
  have hvpair : ∀ y, v (y - 1) ≠ v (y + 1) := fun y =>
    hvinj.ne (zmod_sub_one_ne_add_one_of_three_le hr3 y)
  have hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1) := by
    simpa only [B] using entry_cycleIntertwine_of_adjMatrix_comm
      G D u v (1 : ZMod r) (1 : ZMod r) hcomm huD hvD hupair hvpair
  have hbinary : ∀ x y, B x y = 0 ∨ B x y = 1 := by
    intro x y
    simp only [B, SimpleGraph.adjMatrix_apply]
    split <;> simp
  have hrow : ∀ x, ∑ y, B x y = 3 := by
    intro x
    calc
      (∑ y, B x y) = ∑ y, if G.Adj (u x) (v y) then (1 : ℤ) else 0 := by
        rfl
      _ = ((mixedAnchorSupport G (u x) v).card : ℤ) := by
        simpa only [mixedAnchorSupport] using (Finset.sum_boole (R := ℤ)
          (fun y : ZMod r => G.Adj (u x) (v y)) Finset.univ)
      _ = 3 := by rw [hthree]; norm_num
  have hrect : ∀ x x', x ≠ x' → ∀ y y', y ≠ y' →
      ¬ (B x y = 1 ∧ B x y' = 1 ∧
        B x' y = 1 ∧ B x' y' = 1) := by
    intro x x' hxx' y y' hyy' hones
    have hux : u x ≠ u x' := huinj.ne hxx'
    have hvy : v y ≠ v y' := hvinj.ne hyy'
    have hone_iff (a b : ZMod r) : B a b = 1 ↔ G.Adj (u a) (v b) := by
      simp only [B, SimpleGraph.adjMatrix_apply]
      by_cases h : G.Adj (u a) (v b) <;> simp [h]
    have hy : v y ∈ G.neighborFinset (u x) ∩
        G.neighborFinset (u x') := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨(hone_iff x y).mp hones.1,
        (hone_iff x' y).mp hones.2.2.1⟩
    have hy' : v y' ∈ G.neighborFinset (u x) ∩
        G.neighborFinset (u x') := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨(hone_iff x y').mp hones.2.1,
        (hone_iff x' y').mp hones.2.2.2⟩
    have htwoCommon : 2 ≤ (G.neighborFinset (u x) ∩
        G.neighborFinset (u x')).card := by
      have hsub : ({v y, v y'} : Finset V) ⊆
          G.neighborFinset (u x) ∩ G.neighborFinset (u x') := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hy
        · exact hy'
      have hc : ({v y, v y'} : Finset V).card = 2 := by simp [hvy]
      rw [← hc]
      exact Finset.card_le_card hsub
    have honeCommon := common_le_one_of_not_containsC4 hfree
      (u x) (u x') hux
    omega
  rcases binary_rowThree_cycleIntertwiner_orientation hr3 B hinter hbinary
    hrow hrect with hforward | hreverse
  · left
    intro x y
    have h := hforward x y
    simp only [B, SimpleGraph.adjMatrix_apply] at h
    by_cases h₁ : G.Adj (u (x + 1)) (v (y + 1)) <;>
      by_cases h₂ : G.Adj (u x) (v y) <;> simp_all
  · right
    intro x y
    have h := hreverse x y
    simp only [B, SimpleGraph.adjMatrix_apply] at h
    by_cases h₁ : G.Adj (u (x + 1)) (v (y - 1)) <;>
      by_cases h₂ : G.Adj (u x) (v y) <;> simp_all

/-- Boundary-component wrapper for the parity-independent quotient-three
orientation theorem. -/
theorem graph_equalComponent_quotientThree_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (u v : ZMod r → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (hthree : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 3) :
    (∀ x y, G.Adj (u (x + 1)) (v (y + 1)) ↔ G.Adj (u x) (v y)) ∨
      (∀ x y, G.Adj (u (x + 1)) (v (y - 1)) ↔ G.Adj (u x) (v y)) := by
  apply graph_equalCycleBlock_quotientThree_orientation hr3 G
    (secondOrderDefectGraph G) hfree u v huinj hvinj
    (adjMatrix_comm_secondOrderDefect_of_even
      G hfree hd heven hmin hcard) huD hvD
  intro x
  have hx : u x ∈ c.supp := by
    rw [← huRange]
    exact ⟨x, rfl⟩
  rw [card_mixedAnchorSupport_eq_componentQuotient
    G hfree hd heven hmin hcard c e hx hvinj hvRange, hthree]

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
theorem no_edges_in_one_bipartite_checkerboard_sector
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u v : ZMod r → V) (hu : Function.Injective u)
    (hv : Function.Injective v)
    (hcirc : ∀ {x y x' y' : ZMod r},
      ZMod.castHom h2r (ZMod 2) (y - x) = 0 →
      y - x = y' - x' →
      (G.Adj (u x) (v y) ↔ G.Adj (u x') (v y')))
    (hrev : ∀ {x y x' y' : ZMod r},
      ZMod.castHom h2r (ZMod 2) (y - x) ≠ 0 →
      y + x = y' + x' →
      (G.Adj (u x) (v y) ↔ G.Adj (u x') (v y'))) :
    (∀ x y : ZMod r,
        ZMod.castHom h2r (ZMod 2) (y - x) = 0 →
        ¬ G.Adj (u x) (v y)) ∨
      (∀ x y : ZMod r,
        ZMod.castHom h2r (ZMod 2) (y - x) ≠ 0 →
        ¬ G.Adj (u x) (v y)) := by
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
  have hxe : G.Adj (u x) (v e) := by
    apply (hrev hab0 (by dsimp [e, s]; ring)).mp hab
  have hcy : G.Adj (u c) (v y) := by
    apply (hrev hab0 (by dsimp [c, s]; ring)).mp hab
  have hce : G.Adj (u c) (v e) := by
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
  have hvyve : v y ≠ v e := fun h ↦ hye (hv h)
  have hy_mem : v y ∈ G.neighborFinset (u x) ∩
      G.neighborFinset (u c) := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxy, hcy⟩
  have he_mem : v e ∈ G.neighborFinset (u x) ∩
      G.neighborFinset (u c) := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxe, hce⟩
  have htwo : 2 ≤ (G.neighborFinset (u x) ∩
      G.neighborFinset (u c)).card := by
    have hsub : ({v y, v e} : Finset V) ⊆
        G.neighborFinset (u x) ∩ G.neighborFinset (u c) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hy_mem
      · exact he_mem
    have hcard : ({v y, v e} : Finset V).card = 2 := by
      simp [hvyve]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hone := common_le_one_of_not_containsC4 hfree (u x) (u c) hucx.symm
  omega

/-- Diagonal specialization of
`no_edges_in_one_bipartite_checkerboard_sector`. -/
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
        ¬ G.Adj (u x) (u y)) :=
  no_edges_in_one_bipartite_checkerboard_sector h2r G hfree
    u u hu hu hcirc hrev

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
