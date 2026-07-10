/-
  Erdős Problem #434 — the Frobenius finiteness property (Chicken McNugget)

  Source: https://erdosproblems.com/434

  Problem #434 (the *extremal* Frobenius problem) asks which `k`-subset of
  `{1, …, n}` maximises the count of integers not representable as a sum of its
  elements.  The whole question only makes sense because that count is *finite*:
  for a set `A ⊆ ℕ` whose elements have gcd `1`, only finitely many integers are
  non-representable (the largest is the Frobenius number).

  `Erdos434Problem.lean` states this finiteness as `nonrep_finite`/`topK_finite`
  but leaves it as `sorry`.  This companion file proves it from scratch and
  self-containedly.  The mathematical core is the **Chicken McNugget theorem**
  (`exists_nat_combo_of_ge`): for coprime positive `a, b`, every `n ≥ a·b` is a
  non-negative integer combination `x·a + y·b`.  Mathlib has no numerical-semigroup
  API, so this is built directly from `ZMod` unit arithmetic:

  * `a` is a unit mod `b` (coprimality), so `a·x ≡ n (mod b)` is solvable with a
    residue `0 ≤ x < b`;
  * then `x·a ≤ (b-1)·a < a·b ≤ n`, so `n - x·a ≥ 0` is a non-negative multiple
    of `b`, supplying the second coefficient `y`.

  From it, `nonrep_finite` follows: any coprime pair `a, b ∈ A` makes every
  integer `≥ a·b` representable, so the non-representable set is contained in
  `Set.Iio (a·b)`, which is finite.  `topK_finite` is the special case where the
  block `{n-k+1, …, n}` supplies the coprime consecutive pair `n-1, n`.

  Research file — intentionally NOT registered in `Proofs.lean`.
-/

import Mathlib

namespace Erdos434Frobenius

/- ## Representability -/

/-- A natural number `n` is representable by a set `A` if it is the sum of a
    multiset of elements of `A` (repetition allowed). -/
def IsRepresentableAs (n : ℕ) (A : Set ℕ) : Prop :=
  ∃ S : Multiset ℕ, (∀ a ∈ S, a ∈ A) ∧ S.sum = n

/-- The set of integers not representable by `A`. -/
def NonRepresentable (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ¬ IsRepresentableAs n A}

/- ## Chicken McNugget: an explicit combination above `a * b` -/

/-- If `1 ∈ A` then every natural number is representable (as a sum of `n` copies
    of `1`). -/
theorem representable_of_one_mem {A : Set ℕ} (h1 : 1 ∈ A) (n : ℕ) :
    IsRepresentableAs n A :=
  ⟨Multiset.replicate n 1,
    fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h1,
    by rw [Multiset.sum_replicate, smul_eq_mul, mul_one]⟩

/-- **Chicken McNugget theorem (existence form).**  For coprime positive `a, b`,
    every `n ≥ a * b` can be written as a non-negative integer combination
    `x * a + y * b`. -/
theorem exists_nat_combo_of_ge {a b : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (hcop : Nat.Coprime a b) {n : ℕ} (hn : a * b ≤ n) :
    ∃ x y : ℕ, n = x * a + y * b := by
  haveI : NeZero b := ⟨hbpos.ne'⟩
  -- `a` is a unit mod `b`, so `a * x ≡ n (mod b)` is solvable with `x < b`.
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a b).mpr hcop
  set x : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * (n : ZMod b)).val with hxdef
  have hxlt : x < b := by rw [hxdef]; exact ZMod.val_lt _
  have hcast : (a : ZMod b) * (x : ZMod b) = (n : ZMod b) := by
    rw [hxdef, ZMod.natCast_zmod_val, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  -- `x * a ≤ n`, so `n - x * a` is a genuine natural number.
  have hxa : x * a ≤ n := by
    calc x * a ≤ (b - 1) * a := by gcongr <;> omega
      _ ≤ b * a := by gcongr <;> omega
      _ = a * b := by ring
      _ ≤ n := hn
  -- `b ∣ (n - x * a)` from the congruence `a * x ≡ n (mod b)`.
  have hdvd : b ∣ (n - x * a) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hxa]
    push_cast
    rw [mul_comm (x : ZMod b) (a : ZMod b), hcast, sub_self]
  obtain ⟨y, hy⟩ := hdvd
  rw [Nat.mul_comm b y] at hy
  exact ⟨x, y, by omega⟩

/-- Any `n ≥ a * b` is representable by `A`, provided `A` contains a coprime
    positive pair `a, b`. -/
theorem representable_of_ge_of_mem {A : Set ℕ} {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hapos : 0 < a) (hbpos : 0 < b)
    (hcop : Nat.Coprime a b) {n : ℕ} (hn : a * b ≤ n) :
    IsRepresentableAs n A := by
  obtain ⟨x, y, hxy⟩ := exists_nat_combo_of_ge hapos hbpos hcop hn
  refine ⟨Multiset.replicate x a + Multiset.replicate y b, ?_, ?_⟩
  · intro z hz
    rcases Multiset.mem_add.mp hz with h | h
    · rw [Multiset.eq_of_mem_replicate h]; exact ha
    · rw [Multiset.eq_of_mem_replicate h]; exact hb
  · rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate,
        smul_eq_mul, smul_eq_mul]
    omega

/- ## Finiteness of the non-representable set -/

/-- If `1 ∈ A`, the non-representable set is empty, hence finite. -/
theorem nonrep_finite_of_one_mem {A : Set ℕ} (h1 : 1 ∈ A) :
    (NonRepresentable A).Finite := by
  have hempty : NonRepresentable A = ∅ := by
    ext m
    simp only [NonRepresentable, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact representable_of_one_mem h1 m
  rw [hempty]; exact Set.finite_empty

/-- **Finiteness of the non-representable set (Frobenius property).**  If `A`
    contains a coprime pair `a, b`, then every integer `≥ a * b` is representable
    (`representable_of_ge_of_mem`), so the non-representable integers all lie in
    `Set.Iio (a * b)`, a finite set.  A coprime pair involving `0` forces
    `1 ∈ A`, the degenerate case. -/
theorem nonrep_finite {A : Set ℕ}
    (hcop : ∃ a b ∈ A, Nat.Coprime a b) :
    (NonRepresentable A).Finite := by
  obtain ⟨a, ha, b, hb, hcop⟩ := hcop
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · rw [(Nat.coprime_zero_left b).mp hcop] at hb
    exact nonrep_finite_of_one_mem hb
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · rw [(Nat.coprime_zero_right a).mp hcop] at ha
    exact nonrep_finite_of_one_mem ha
  refine Set.Finite.subset (Set.finite_Iio (a * b)) ?_
  intro m hm
  simp only [Set.mem_Iio]
  by_contra h
  push_neg at h
  exact hm (representable_of_ge_of_mem ha hb hapos hbpos hcop h)

/-- The "top-`k`" block `{n-k+1, …, n}`. -/
def topK (n k : ℕ) : Set ℕ := Set.Icc (n - k + 1) n

/-- For `topK n k` with `k ≥ 2` the non-representable count is finite: the block
    contains the coprime consecutive pair `n-1, n`. -/
theorem topK_finite (n k : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    (NonRepresentable (topK n k)).Finite := by
  refine nonrep_finite ⟨n - 1, ?_, n, ?_, ?_⟩
  · simp only [topK, Set.mem_Icc]; omega
  · simp only [topK, Set.mem_Icc]; omega
  · rw [Nat.coprime_self_sub_left (by omega : (1 : ℕ) ≤ n)]
    exact Nat.coprime_one_left n

end Erdos434Frobenius
