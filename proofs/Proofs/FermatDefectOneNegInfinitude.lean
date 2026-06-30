/-
  Negative-defect infinitude for the Fermat Defect-One Conjecture (n = 3)

  Companion to `FermatDefectOneFamilies.lean`, which proves that the *positive*-
  defect Mahler family produces infinitely many primitive witnesses at n = 3
  (`defect_pos_witnesses_infinite`). That theorem leaves the negative-defect side
  at mere existence (`fermat_defect_three_neg_t2`, a single witness at t = 2).

  This file closes the symmetry. The negative-defect Mahler family

      (9t³ − 1)³ + (9t⁴ − 3t)³ + 1 = (9t⁴)³        (defect −1, i.e. aⁿ + bⁿ − cⁿ = −1)

  also yields infinitely many *primitive* witnesses. Combined with the positive
  result, open question OQ-02 ("are both signs of the defect realised for every
  n ≥ 3?") is settled at n = 3 in its strongest form: **each sign of the defect
  occurs infinitely often**, along an explicit polynomial family.

  Ordering note. For t ≥ 2 the base terms satisfy
      9t³ − 1 ≤ 9t⁴ − 3t < 9t⁴,
  so the ordered primitive witness is `(9t³ − 1, 9t⁴ − 3t, 9t⁴)`. (At t = 1 this
  degenerates to the benchmark `(6, 8, 9)` after swapping the first two
  coordinates.) The value of c is `9t⁴`, strictly increasing in t, so the set of
  attainable c's is infinite.
-/
import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOne

/-- **Negative-defect coprimality kernel.** `9t³ − 1` and `9t⁴` are coprime for
every `t ≥ 1`.

Proof: a common divisor `d` divides `9t⁴ = t·(9t³ − 1) + t`, hence — using
`d ∣ t·(9t³ − 1)` — divides `t`; then `d ∣ 9t³ = 9t²·t`, and together with
`d ∣ 9t³ − 1` this forces `d ∣ 1`. The single subtraction `9t³ − 1` is unfolded
over `ℤ` (via `zify`) inside the auxiliary identity. -/
lemma neg_family_coprime (t : ℕ) (ht : 1 ≤ t) :
    Nat.Coprime (9 * t ^ 3 - 1) (9 * t ^ 4) := by
  have hpos : 1 ≤ 9 * t ^ 3 := by
    have : 1 ≤ t ^ 3 := Nat.one_le_pow 3 t ht
    omega
  -- `9t⁴ = t·(9t³ − 1) + t`
  have hca : 9 * t ^ 4 = t * (9 * t ^ 3 - 1) + t := by
    zify [hpos]; ring
  have key : ∀ d : ℕ, d ∣ (9 * t ^ 3 - 1) → d ∣ (9 * t ^ 4) → d ∣ 1 := by
    intro d hda hdc
    have hdt : d ∣ t := by
      have hdta : d ∣ t * (9 * t ^ 3 - 1) := hda.mul_left t
      have h := Nat.dvd_sub hdc hdta
      rwa [hca, Nat.add_sub_cancel_left] at h
    have hd3 : d ∣ 9 * t ^ 3 := by
      have he : 9 * t ^ 3 = 9 * t ^ 2 * t := by ring
      rw [he]; exact hdt.mul_left (9 * t ^ 2)
    have h := Nat.dvd_sub hd3 hda
    rwa [Nat.sub_sub_self hpos] at h
  have hg := key (Nat.gcd (9 * t ^ 3 - 1) (9 * t ^ 4))
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  exact Nat.dvd_one.mp hg

/-- **Core negative-defect witness data at n = 3** (the equation, not the
`FermatDefectWitness` disjunction). For every `t ≥ 2` the triple
`(9t³ − 1, 9t⁴ − 3t, 9t⁴)` is ordered, primitive, and satisfies
`a³ + b³ + 1 = c³`. -/
theorem defect_neg_data (t : ℕ) (ht : 2 ≤ t) :
    2 ≤ 9 * t ^ 3 - 1 ∧ 9 * t ^ 3 - 1 ≤ 9 * t ^ 4 - 3 * t ∧
      9 * t ^ 4 - 3 * t < 9 * t ^ 4 ∧
      Nat.gcd (Nat.gcd (9 * t ^ 3 - 1) (9 * t ^ 4 - 3 * t)) (9 * t ^ 4) = 1 ∧
      (9 * t ^ 3 - 1) ^ 3 + (9 * t ^ 4 - 3 * t) ^ 3 + 1 = (9 * t ^ 4) ^ 3 := by
  have ht1 : 1 ≤ t := by omega
  have hA : 8 ≤ t ^ 3 := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ t ^ 3 := Nat.pow_le_pow_left ht 3
  have hB : t ≤ t ^ 3 := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 3 := Nat.pow_le_pow_right ht1 (by norm_num)
  have hC : 2 * t ^ 3 ≤ t ^ 4 := by
    calc 2 * t ^ 3 ≤ t * t ^ 3 := mul_le_mul_right' ht (t ^ 3)
      _ = t ^ 4 := by ring
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · exact (neg_family_coprime t ht1).coprime_dvd_left (Nat.gcd_dvd_left _ _)
  · have hpos : 1 ≤ 9 * t ^ 3 := by omega
    have hb : 3 * t ≤ 9 * t ^ 4 := by omega
    zify [hpos, hb]; ring

/-- **Generic negative-defect primitive witness.** For every `t ≥ 2`,
`(9t³ − 1, 9t⁴ − 3t, 9t⁴)` is a primitive nontrivial defect-one witness at
`n = 3`. At `t = 2` this is `(71, 138, 144)` (`fermat_defect_three_neg_t2`). -/
theorem defect_neg_witness_ge_two (t : ℕ) (ht : 2 ≤ t) :
    FermatDefectWitness 3 (9 * t ^ 3 - 1) (9 * t ^ 4 - 3 * t) (9 * t ^ 4) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := defect_neg_data t ht
  exact ⟨h1, h2, h3, h4, Or.inl h5⟩

/-- **Negative-defect infinitude at n = 3.** The set of `c` occurring in a
primitive *negative*-defect witness at `n = 3` (i.e. `a³ + b³ + 1 = c³`) is
infinite. The injection is `n ↦ 9(n + 2)⁴`, strictly monotone, each value
witnessed by `defect_neg_data`. Symmetric to `defect_pos_witnesses_infinite`. -/
theorem defect_neg_witnesses_infinite :
    {c : ℕ | ∃ a b : ℕ, 2 ≤ a ∧ a ≤ b ∧ b < c ∧
      Nat.gcd (Nat.gcd a b) c = 1 ∧ a ^ 3 + b ^ 3 + 1 = c ^ 3}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 9 * (n + 2) ^ 4)
  · have hmono : StrictMono (fun n : ℕ => 9 * (n + 2) ^ 4) := by
      apply strictMono_nat_of_lt_succ
      intro n
      have hp : (n + 2) ^ 4 < (n + 1 + 2) ^ 4 :=
        Nat.pow_lt_pow_left (by omega) (by norm_num)
      show 9 * (n + 2) ^ 4 < 9 * (n + 1 + 2) ^ 4
      omega
    exact hmono.injective
  · intro n
    show ∃ a b : ℕ, 2 ≤ a ∧ a ≤ b ∧ b < 9 * (n + 2) ^ 4 ∧
      Nat.gcd (Nat.gcd a b) (9 * (n + 2) ^ 4) = 1 ∧
      a ^ 3 + b ^ 3 + 1 = (9 * (n + 2) ^ 4) ^ 3
    obtain ⟨h1, h2, h3, h4, h5⟩ := defect_neg_data (n + 2) (by omega)
    exact ⟨9 * (n + 2) ^ 3 - 1, 9 * (n + 2) ^ 4 - 3 * (n + 2),
      h1, h2, h3, h4, h5⟩

end FermatDefectOne
