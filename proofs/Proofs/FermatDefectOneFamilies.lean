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

/-! ## Positive-sign-pinned infinitude at n = 3

`defect_pos_witnesses_infinite` above shows the *sign-agnostic* witness set is
infinite: its members come from the positive family, but the statement hides
the sign inside the `FermatDefectWitness` disjunction. OQ-02 asks about each
sign separately. The negative side is sign-pinned and infinite in
`FermatDefectOneNegInfinitude.lean` (`defect_neg_witnesses_infinite`); here we
add the missing positive-side counterpart, pinning `a³ + b³ = c³ + 1` in the
set comprehension. (The ℤ sign-flip involution of `FermatDefectOneOQ06.lean`
does not transport primitive ordered ℕ witnesses, so neither sign-pinned
statement follows formally from the other.) -/

/-- **Positive-sign infinitude at n = 3.** The set of `c` occurring in a
primitive witness with defect exactly +1 (`a³ + b³ = c³ + 1`) is infinite —
upgrading `fermat_defect_three_positive` (existence) to infinitude via the
positive family. Together with `defect_neg_witnesses_infinite`
(`FermatDefectOneNegInfinitude.lean`) this settles OQ-02 at n = 3 in its
strongest form: EACH defect sign is realised by infinitely many primitive
witnesses, with the sign pinned in the statement. -/
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
    rw [pos_family_gcd s]
    exact Nat.gcd_one_left _

end FermatDefectOne
