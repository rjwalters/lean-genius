/-
  Bounded non-existence certificates for the Fermat Defect-One Conjecture

  Companion to `FermatDefectOne.lean`. The headline conjecture

      ∀ n ≥ 3, ∃ primitive (a,b,c) with |aⁿ + bⁿ − cⁿ| = 1

  is verified only at n = 3 (both signs, infinitely often — see
  `FermatDefectOneFamilies.lean` and `FermatDefectOneNegInfinitude.lean`). For
  n ≥ 4 *no* witness is known, and the productive research vector recorded in
  `research/problems/fermat-defect-one/notes/leads.md` is a per-exponent
  *witness search*: "a single positive hit clears the exponent."

  This file discharges the complementary, fully decidable half of that search:
  an **exhaustive verification that the smallest defect-one witness at n = 4 and
  n = 5 — if one exists at all — must have c ≥ 20.** Equivalently, the bounded
  Diophantine systems

      a⁴ + b⁴ + 1 = c⁴   and   a⁴ + b⁴ = c⁴ + 1   (n = 4)
      a⁵ + b⁵ + 1 = c⁵   and   a⁵ + b⁵ = c⁵ + 1   (n = 5)

  have **no** solution in the ordered range 2 ≤ a ≤ b < c < 20. (The primitivity
  condition gcd(a,b,c) = 1 is not even needed to rule these out; the raw
  equations already fail.) The gallery's `no_witness_n_eq_4_below_20` research
  target is met here.

  Method. The claim is a bounded universal statement over `ℕ` and is therefore
  decidable (`Nat.decidableBallLT` / `Nat.decidableBallLE`), so the kernel
  discharges it by `decide` — **no `native_decide`, no `Lean.ofReduceBool`**.
  These theorems are 0-axiom (only the ordinary foundational axioms of Lean).

  Significance. This does not resolve the open conjecture (existence for n ≥ 4
  remains open), but it converts the informal "an exhaustive search to c ≤ 100
  has not been documented in this repository" (leads.md) into a machine-checked
  lower bound on the size of any n ∈ {4,5} witness, and rules out the naive hope
  of a small n = 4 or n = 5 example.
-/

import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOne

/-! ## Decidable bounded search kernels

Each kernel is a bounded universal statement whose innermost predicate is the
conjunction of the two Nat-form defect equations failing. The outermost bound is
always an *upper* bound (`c < 20`, `b < c`, `a ≤ b`), which is what makes the
statement decidable; the lower bound `2 ≤ a` enters as an inner implication. -/

/-- **n = 4 exhaustive kernel.** For every ordered triple `2 ≤ a ≤ b < c < 20`
neither defect-one equation `a⁴ + b⁴ + 1 = c⁴` (negative sign) nor
`a⁴ + b⁴ = c⁴ + 1` (positive sign) holds. Verified by `decide`. -/
theorem defect_n4_below_20_kernel :
    ∀ c, c < 20 → ∀ b, b < c → ∀ a, a ≤ b → 2 ≤ a →
      a ^ 4 + b ^ 4 + 1 ≠ c ^ 4 ∧ a ^ 4 + b ^ 4 ≠ c ^ 4 + 1 := by
  decide

/-- **n = 5 exhaustive kernel.** For every ordered triple `2 ≤ a ≤ b < c < 20`
neither defect-one equation `a⁵ + b⁵ + 1 = c⁵` nor `a⁵ + b⁵ = c⁵ + 1` holds.
Verified by `decide`. -/
theorem defect_n5_below_20_kernel :
    ∀ c, c < 20 → ∀ b, b < c → ∀ a, a ≤ b → 2 ≤ a →
      a ^ 5 + b ^ 5 + 1 ≠ c ^ 5 ∧ a ^ 5 + b ^ 5 ≠ c ^ 5 + 1 := by
  decide

/-! ## Non-existence of small witnesses (gallery predicate form) -/

/-- **No n = 4 defect-one witness below c = 20.** There is no primitive
nontrivial Fermat defect-one witness at exponent 4 with `c < 20`. In particular
the smallest n = 4 witness, should the open conjecture hold at n = 4, has
`c ≥ 20`. Fully verified (0-axiom, `decide`). -/
theorem no_defect_witness_n4_below_20 (a b c : ℕ) (hc : c < 20) :
    ¬ FermatDefectWitness 4 a b c := by
  rintro ⟨ha, hab, hbc, -, hdef⟩
  obtain ⟨hne1, hne2⟩ := defect_n4_below_20_kernel c hc b hbc a hab ha
  rcases hdef with h | h
  · exact hne1 h
  · exact hne2 h

/-- **No n = 5 defect-one witness below c = 20.** There is no primitive
nontrivial Fermat defect-one witness at exponent 5 with `c < 20`. Fully verified
(0-axiom, `decide`). -/
theorem no_defect_witness_n5_below_20 (a b c : ℕ) (hc : c < 20) :
    ¬ FermatDefectWitness 5 a b c := by
  rintro ⟨ha, hab, hbc, -, hdef⟩
  obtain ⟨hne1, hne2⟩ := defect_n5_below_20_kernel c hc b hbc a hab ha
  rcases hdef with h | h
  · exact hne1 h
  · exact hne2 h

/-- **No small defect-one witness at n = 4 or n = 5, either sign.** Packaged
statement: for every exponent `n ∈ {4, 5}` there is no primitive defect-one
witness with `c < 20`. This is the machine-checked content behind the informal
"no small n = 4/5 example" claim; the open conjecture (existence for some, or
every, larger `c`) is untouched. -/
theorem no_defect_witness_n4_n5_below_20 :
    ∀ a b c : ℕ, c < 20 →
      ¬ FermatDefectWitness 4 a b c ∧ ¬ FermatDefectWitness 5 a b c :=
  fun a b c hc =>
    ⟨no_defect_witness_n4_below_20 a b c hc, no_defect_witness_n5_below_20 a b c hc⟩

end FermatDefectOne
