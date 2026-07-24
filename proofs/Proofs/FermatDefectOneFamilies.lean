/-
  Parametric families for the Fermat Defect-One Conjecture (n = 3)

  See `FermatDefectOne.lean` for the main formalization and the open headline
  conjecture `fermat_defect_one_exists` (∀ n ≥ 3, a primitive defect-one
  witness exists). This file addresses open question OQ-02:

      "Are both signs of the defect realised for every n ≥ 3?"

  ## Result for n = 3: both signs come from one parametrization

  Both defect signs at n = 3 are not merely witnessed by two hand-picked
  triples — each lies on an explicit infinite polynomial family, and both
  families descend from Mahler's parametrization of the cubic surface
  $x^3 + y^3 + z^3 = 1$ evaluated at the parameter and its negation:

      x = 9t⁴,   y = 3t − 9t⁴,   z = 1 − 9t³,    x³ + y³ + z³ = 1.

  * **Negative defect** (t ≥ 1, signs (+,−,−)): rearranging gives
        (9t⁴ − 3t)³ + (9t³ − 1)³ + 1 = (9t⁴)³.
    t = 1 ↦ (6, 8, 9)  [the gallery benchmark `fermat_defect_three_neg`],
    t = 2 ↦ (71, 138, 144), t = 3 ↦ (242, 720, 729), …

  * **Positive defect** (parameter −s, s ≥ 1, signs (+,+,−)): rearranging gives
        (9s⁴)³ + (9s³ + 1)³ = (9s⁴ + 3s)³ + 1.
    s = 1 ↦ (9, 10, 12)  [the gallery benchmark `fermat_defect_three_pos`,
    the taxicab number 1729 shifted by one], s = 2 ↦ (73, 144, 150), …

  Both identities are polynomial identities, closed by `ring`. Because the
  parameter ranges over all naturals/integers ≥ 1 and the value of `c`
  (`9t⁴` resp. `9s⁴ + 3s`) is strictly increasing, **each sign of the defect
  at n = 3 has infinitely many primitive witnesses.** OQ-02 is therefore
  fully settled in the affirmative *at n = 3*, and with explicit families
  rather than sporadic examples.

  ## Contrast at n ≥ 4 (see also `FermatDefectOneAristotle.lean`)

  An exact integer search (see
  `research/problems/fermat-defect-one-oq-02/verify_defect_search.py`) finds
  NO primitive defect-one witness of either sign for 4 ≤ n ≤ 7 within large
  bounds (n = 4 up to a, b ≤ 6000; n = 5 ≤ 4000; n = 6 ≤ 2500; n = 7 ≤ 2000).
  The standard heuristic count of primitive solutions up to height X scales
  like X^(3−n): n = 3 is the critical exponent (X⁰, log-divergent ⟹ infinitely
  many, matching the families above), while n ≥ 4 is convergent (⟹ heuristically
  finitely many, plausibly zero). So the n = 3 abundance is a critical-exponent
  phenomenon, and demanding *both signs at every n ≥ 4* is, under standard
  heuristics, expected to be hard or false — not a routine extension of n = 3.
-/
import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOne

/-! ## Parametric identities (the mathematical heart, closed by `ring`) -/

/-- **Negative-defect family at n = 3.** For every integer `t`,
`(9t⁴ − 3t)³ + (9t³ − 1)³ + 1 = (9t⁴)³`. Stated over `ℤ` so that the
truncated subtraction of `ℕ` does not interfere. For `t ≥ 1` the three base
terms are positive and give a primitive negative-defect witness `a³+b³+1=c³`
(after ordering `a ≤ b`); `t = 1` recovers `(6,8,9)`. -/
theorem defect_neg_family (t : ℤ) :
    (9 * t ^ 4 - 3 * t) ^ 3 + (9 * t ^ 3 - 1) ^ 3 + 1 = (9 * t ^ 4) ^ 3 := by
  ring

/-- **Positive-defect family at n = 3.** For every natural `s`,
`(9s⁴)³ + (9s³ + 1)³ = (9s⁴ + 3s)³ + 1`. This family is subtraction-free, so
it holds over `ℕ` directly. For `s ≥ 1` it gives a primitive positive-defect
witness `a³+b³=c³+1` (after ordering `a ≤ b`); `s = 1` recovers `(9,10,12)`,
the taxicab number `1729 = 9³ + 10³ = 12³ + 1`. -/
theorem defect_pos_family (s : ℕ) :
    (9 * s ^ 4) ^ 3 + (9 * s ^ 3 + 1) ^ 3 = (9 * s ^ 4 + 3 * s) ^ 3 + 1 := by
  ring

/-! ## New verified primitive witnesses beyond the gallery's `t = s = 1` pair

The gallery's `FermatDefectOne.lean` verifies only the first member of each
family. These are the next members (`t = 2`, `s = 2`), confirming that the
families produce genuine *primitive* defect-one witnesses, not just solutions
to the equation. Discharged by `native_decide`. -/

/-- Negative-defect family at `t = 2`: `71³ + 138³ + 1 = 144³`, primitive,
`2 ≤ 71 ≤ 138 < 144`. (From `defect_neg_family 2`, ordered.) -/
theorem fermat_defect_three_neg_t2 : FermatDefectWitness 3 71 138 144 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · left; native_decide

/-- Positive-defect family at `s = 2`: `73³ + 144³ = 150³ + 1`, primitive,
`2 ≤ 73 ≤ 144 < 150`. (From `defect_pos_family 2`, ordered.) -/
theorem fermat_defect_three_pos_s2 : FermatDefectWitness 3 73 144 150 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · right; native_decide

/-! ## Existence packaging at n = 3 (both signs), from the families

These re-derive `FermatDefectExists 3` along each family member, witnessing
that the *family* — not just the gallery benchmark — settles n = 3 for each
sign. -/

/-- Negative sign realised at n = 3 (family member `t = 2`). -/
theorem defect_exists_three_neg : FermatDefectExists 3 :=
  ⟨71, 138, 144, fermat_defect_three_neg_t2⟩

/-- Positive sign realised at n = 3 (family member `s = 2`). -/
theorem defect_exists_three_pos : FermatDefectExists 3 :=
  ⟨73, 144, 150, fermat_defect_three_pos_s2⟩

/-! ## Infinitely many primitive witnesses at n = 3

The previous theorems witness one or two members of each family. Here we upgrade
existence to **infinitude**: the positive-defect family produces a primitive
`FermatDefectWitness 3` for *every* parameter `s ≥ 2`, and the value of `c`
(`9s⁴ + 3s`) is strictly increasing, so the set of attainable `c` is infinite.

Restricting to `s ≥ 2` keeps the ordering `a ≤ b` fixed: at `s = 1` the two base
terms `9s⁴ = 9` and `9s³ + 1 = 10` are nearly equal and would flip, but for
`s ≥ 2` we have `9s³ + 1 ≤ 9s⁴`, so the witness is `(9s³+1, 9s⁴, 9s⁴+3s)`. -/

/-- **Primitivity kernel.** `9s³ + 1` and `9s⁴` are coprime for every `s`.

Proof: any common divisor `d` divides `s·(9s³+1) = 9s⁴ + s` and `9s⁴`, hence
divides `s`; then `d ∣ 9s³` and `d ∣ 9s³+1`, so `d ∣ 1`. No subtraction is used
(everything goes through `Nat.dvd_add_right`), keeping the argument `ℕ`-clean. -/
lemma pos_family_gcd (s : ℕ) : Nat.gcd (9 * s ^ 3 + 1) (9 * s ^ 4) = 1 := by
  set d := Nat.gcd (9 * s ^ 3 + 1) (9 * s ^ 4) with hd
  have h1 : d ∣ 9 * s ^ 3 + 1 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ 9 * s ^ 4 := Nat.gcd_dvd_right _ _
  have h3 : d ∣ s := by
    have hds : d ∣ 9 * s ^ 4 + s := by
      have he : 9 * s ^ 4 + s = s * (9 * s ^ 3 + 1) := by ring
      rw [he]; exact h1.mul_left s
    exact (Nat.dvd_add_right h2).mp hds
  have h4 : d ∣ 9 * s ^ 3 := by
    have he : 9 * s ^ 3 = 9 * s ^ 2 * s := by ring
    rw [he]; exact h3.mul_left (9 * s ^ 2)
  have h6 : d ∣ 1 := (Nat.dvd_add_right h4).mp h1
  exact Nat.dvd_one.mp h6

/-- **Generic positive-defect primitive witness.** For every `s ≥ 2`,
`(9s³+1, 9s⁴, 9s⁴+3s)` is a primitive nontrivial defect-one witness at `n = 3`.
At `s = 2` this is `(73, 144, 150)` (`fermat_defect_three_pos_s2`). -/
theorem defect_pos_witness_ge_two (s : ℕ) (hs : 2 ≤ s) :
    FermatDefectWitness 3 (9 * s ^ 3 + 1) (9 * s ^ 4) (9 * s ^ 4 + 3 * s) := by
  have hx : (8 : ℕ) ≤ s ^ 3 := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ s ^ 3 := Nat.pow_le_pow_left hs 3
  have e2 : 2 * s ^ 3 ≤ s ^ 4 := by
    calc 2 * s ^ 3 ≤ s * s ^ 3 := mul_le_mul_right' hs (s ^ 3)
      _ = s ^ 4 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · rw [pos_family_gcd s]; exact Nat.gcd_one_left _
  · right; ring

/-- **Infinitude at n = 3.** The set of `c` occurring in a primitive defect-one
witness at `n = 3` is infinite. Hence n = 3 has infinitely many primitive
witnesses — a strict strengthening of `FermatDefectExists 3`. The injection is
`s ↦ 9(s+2)⁴ + 3(s+2)`, strictly monotone, each value witnessed by
`defect_pos_witness_ge_two`. -/
theorem defect_pos_witnesses_infinite :
    {c : ℕ | ∃ a b : ℕ, FermatDefectWitness 3 a b c}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 9 * (n + 2) ^ 4 + 3 * (n + 2))
  · have hmono : StrictMono (fun n : ℕ => 9 * (n + 2) ^ 4 + 3 * (n + 2)) := by
      apply strictMono_nat_of_lt_succ
      intro n
      show 9 * (n + 2) ^ 4 + 3 * (n + 2) < 9 * (n + 1 + 2) ^ 4 + 3 * (n + 1 + 2)
      have hp : (n + 2) ^ 4 ≤ (n + 1 + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    exact hmono.injective
  · intro n
    show ∃ a b : ℕ, FermatDefectWitness 3 a b (9 * (n + 2) ^ 4 + 3 * (n + 2))
    exact ⟨9 * (n + 2) ^ 3 + 1, 9 * (n + 2) ^ 4,
      defect_pos_witness_ge_two (n + 2) (by omega)⟩

/-! ## Sign-specific infinitude at n = 3

`defect_pos_witnesses_infinite` above shows the *sign-agnostic* witness set is
infinite (its members happen to come from the positive family). OQ-02 asks
about each sign separately, so we now upgrade BOTH `fermat_defect_three_negative`
and `fermat_defect_three_positive` (existence, in `FermatDefectOne.lean`) to
infinitude, with the defect sign pinned in the set comprehension rather than
hidden inside the `FermatDefectWitness` disjunction.

The negative family `(9t³−1, 9t⁴−3t, 9t⁴)` needs `ℕ`-subtraction care that the
positive family avoided: the primitivity kernel goes through
`t·(9t³−1) + t = 9t⁴` (subtraction eliminated by regrouping), and the cubic
identity is transported from `ℤ` via `zify`. As with the positive family, the
ordering `a ≤ b` holds from parameter `2` on (at `t = 1` the family gives
`(8, 6, 9)`, base terms flipped), so witnesses are indexed by `t ≥ 2`. -/

/-- **Negative-family primitivity kernel.** `9t³ − 1` and `9t⁴` are coprime for
every `t ≥ 1`. Proof: a common divisor `d` divides `t·(9t³−1) + t = 9t⁴`, hence
divides `t`, hence divides `9t³ = (9t³−1) + 1`, hence divides `1`. Truncated
subtraction never bites: the only fact used about `9t³ − 1` is
`(9t³ − 1) + 1 = 9t³`, valid since `t ≥ 1`. -/
lemma neg_family_gcd (t : ℕ) (ht : 1 ≤ t) :
    Nat.gcd (9 * t ^ 3 - 1) (9 * t ^ 4) = 1 := by
  have hcube : 1 ≤ 9 * t ^ 3 := by
    have h1 : 1 ≤ t ^ 3 := Nat.one_le_pow 3 t ht
    omega
  have hA : (9 * t ^ 3 - 1) + 1 = 9 * t ^ 3 := by omega
  set d := Nat.gcd (9 * t ^ 3 - 1) (9 * t ^ 4) with hd
  have h1 : d ∣ 9 * t ^ 3 - 1 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ 9 * t ^ 4 := Nat.gcd_dvd_right _ _
  have h3 : d ∣ t := by
    have hds : t * (9 * t ^ 3 - 1) + t = 9 * t ^ 4 := by
      calc t * (9 * t ^ 3 - 1) + t = t * ((9 * t ^ 3 - 1) + 1) := by ring
        _ = t * (9 * t ^ 3) := by rw [hA]
        _ = 9 * t ^ 4 := by ring
    have hdt : d ∣ t * (9 * t ^ 3 - 1) + t := by rw [hds]; exact h2
    exact (Nat.dvd_add_right (h1.mul_left t)).mp hdt
  have h4 : d ∣ (9 * t ^ 3 - 1) + 1 := by
    rw [hA]
    have he : 9 * t ^ 3 = 9 * t ^ 2 * t := by ring
    rw [he]; exact h3.mul_left (9 * t ^ 2)
  have h6 : d ∣ 1 := (Nat.dvd_add_right h1).mp h4
  exact Nat.dvd_one.mp h6

/-- **Generic negative-defect primitive witness.** For every `t ≥ 2`,
`(9t³−1, 9t⁴−3t, 9t⁴)` satisfies all witness conditions with the defect sign
pinned to −1 (`a³ + b³ + 1 = c³`, no disjunction). At `t = 2` this is
`(71, 138, 144)` (`fermat_defect_three_neg_t2`). -/
theorem defect_neg_witness_parts (t : ℕ) (ht : 2 ≤ t) :
    2 ≤ 9 * t ^ 3 - 1 ∧ 9 * t ^ 3 - 1 ≤ 9 * t ^ 4 - 3 * t ∧
    9 * t ^ 4 - 3 * t < 9 * t ^ 4 ∧
    Nat.gcd (Nat.gcd (9 * t ^ 3 - 1) (9 * t ^ 4 - 3 * t)) (9 * t ^ 4) = 1 ∧
    (9 * t ^ 3 - 1) ^ 3 + (9 * t ^ 4 - 3 * t) ^ 3 + 1 = (9 * t ^ 4) ^ 3 := by
  have hx : (8 : ℕ) ≤ t ^ 3 := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ t ^ 3 := Nat.pow_le_pow_left ht 3
  have e2 : 2 * t ^ 3 ≤ t ^ 4 := by
    calc 2 * t ^ 3 ≤ t * t ^ 3 := mul_le_mul_right' ht (t ^ 3)
      _ = t ^ 4 := by ring
  have ht3 : t ≤ t ^ 3 := Nat.le_self_pow (by norm_num) t
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · -- primitivity: any divisor of the full gcd divides both a and c,
    -- hence divides gcd(a, c) = 1 by the kernel.
    have hdvd : Nat.gcd (Nat.gcd (9 * t ^ 3 - 1) (9 * t ^ 4 - 3 * t)) (9 * t ^ 4) ∣
        Nat.gcd (9 * t ^ 3 - 1) (9 * t ^ 4) :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
        (Nat.gcd_dvd_right _ _)
    rw [neg_family_gcd t (by omega)] at hdvd
    exact Nat.dvd_one.mp hdvd
  · -- the cubic identity, transported from ℤ (`defect_neg_family`) via zify
    have h1 : 1 ≤ 9 * t ^ 3 := by omega
    have h2 : 3 * t ≤ 9 * t ^ 4 := by omega
    zify [h1, h2]
    ring

/-- The generic negative witness, packaged as `FermatDefectWitness` (left
disjunct). -/
theorem defect_neg_witness_ge_two (t : ℕ) (ht : 2 ≤ t) :
    FermatDefectWitness 3 (9 * t ^ 3 - 1) (9 * t ^ 4 - 3 * t) (9 * t ^ 4) := by
  obtain ⟨ha, hab, hbc, hgcd, hid⟩ := defect_neg_witness_parts t ht
  exact ⟨ha, hab, hbc, hgcd, Or.inl hid⟩

/-- **Negative-sign infinitude at n = 3.** The set of `c` occurring in a
primitive witness with defect exactly −1 (`a³ + b³ + 1 = c³`) is infinite —
a strict strengthening of `fermat_defect_three_negative` (existence), and
sign-pinned where `defect_pos_witnesses_infinite` is sign-agnostic. Injection
`t ↦ 9(t+2)⁴`, strictly monotone, witnessed by `defect_neg_witness_parts`. -/
theorem defect_neg_sign_witnesses_infinite :
    {c : ℕ | ∃ a b : ℕ, 2 ≤ a ∧ a ≤ b ∧ b < c ∧
      Nat.gcd (Nat.gcd a b) c = 1 ∧ a ^ 3 + b ^ 3 + 1 = c ^ 3}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 9 * (n + 2) ^ 4)
  · have hmono : StrictMono (fun n : ℕ => 9 * (n + 2) ^ 4) := by
      apply strictMono_nat_of_lt_succ
      intro n
      show 9 * (n + 2) ^ 4 < 9 * (n + 1 + 2) ^ 4
      have hp : (n + 2) ^ 4 < (n + 1 + 2) ^ 4 :=
        Nat.pow_lt_pow_left (by omega) (by norm_num)
      omega
    exact hmono.injective
  · intro n
    show ∃ a b : ℕ, 2 ≤ a ∧ a ≤ b ∧ b < 9 * (n + 2) ^ 4 ∧
      Nat.gcd (Nat.gcd a b) (9 * (n + 2) ^ 4) = 1 ∧
      a ^ 3 + b ^ 3 + 1 = (9 * (n + 2) ^ 4) ^ 3
    exact ⟨9 * (n + 2) ^ 3 - 1, 9 * (n + 2) ^ 4 - 3 * (n + 2),
      defect_neg_witness_parts (n + 2) (by omega)⟩

/-- **Positive-sign infinitude at n = 3.** The sign-pinned (`a³ + b³ = c³ + 1`)
counterpart, upgrading `fermat_defect_three_positive` to infinitude via the
positive family. Together with `defect_neg_sign_witnesses_infinite` this
settles OQ-02 at n = 3 in its strongest form: EACH defect sign is realised by
infinitely many primitive witnesses. -/
theorem defect_pos_sign_witnesses_infinite :
    {c : ℕ | ∃ a b : ℕ, 2 ≤ a ∧ a ≤ b ∧ b < c ∧
      Nat.gcd (Nat.gcd a b) c = 1 ∧ a ^ 3 + b ^ 3 = c ^ 3 + 1}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 9 * (n + 2) ^ 4 + 3 * (n + 2))
  · have hmono : StrictMono (fun n : ℕ => 9 * (n + 2) ^ 4 + 3 * (n + 2)) := by
      apply strictMono_nat_of_lt_succ
      intro n
      show 9 * (n + 2) ^ 4 + 3 * (n + 2) < 9 * (n + 1 + 2) ^ 4 + 3 * (n + 1 + 2)
      have hp : (n + 2) ^ 4 ≤ (n + 1 + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    exact hmono.injective
  · intro n
    set s := n + 2 with hs
    show ∃ a b : ℕ, 2 ≤ a ∧ a ≤ b ∧ b < 9 * s ^ 4 + 3 * s ∧
      Nat.gcd (Nat.gcd a b) (9 * s ^ 4 + 3 * s) = 1 ∧
      a ^ 3 + b ^ 3 = (9 * s ^ 4 + 3 * s) ^ 3 + 1
    have hx : (8 : ℕ) ≤ s ^ 3 := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ s ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e2 : 2 * s ^ 3 ≤ s ^ 4 := by
      calc 2 * s ^ 3 ≤ s * s ^ 3 := mul_le_mul_right' (by omega) (s ^ 3)
        _ = s ^ 4 := by ring
    refine ⟨9 * s ^ 3 + 1, 9 * s ^ 4, by omega, by omega, by omega, ?_, by ring⟩
    have hdvd : Nat.gcd (Nat.gcd (9 * s ^ 3 + 1) (9 * s ^ 4)) (9 * s ^ 4 + 3 * s) ∣
        Nat.gcd (9 * s ^ 3 + 1) (9 * s ^ 4) := Nat.gcd_dvd_left _ _
    rw [pos_family_gcd s] at hdvd
    exact Nat.dvd_one.mp hdvd

end FermatDefectOne
