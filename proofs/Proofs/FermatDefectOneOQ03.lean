/-
  Fermat Defect-One — OQ-03: The Minimal n = 3 Defect-One Witness

  The parent entry `FermatDefectOne` studies the "defect one" equation
  |aⁿ + bⁿ − cⁿ| = 1 over primitive nontrivial triples (2 ≤ a ≤ b < c,
  gcd(a,b,c) = 1).  It exhibits witnesses at n = 3 — negative 6³+8³+1 = 9³ and
  positive 9³+10³ = 12³+1 — and leaves the general n ≥ 3 conjecture open.  The
  sibling `FermatDefectOneOQ04` proves bounded *non-existence* for n ∈ {4,5,6}
  (no witness with c ≤ 100), giving M(n) ≥ 2 inside that box, and notes that the
  *minimal* defect-one witness question is exactly OQ-03.

  This file answers that minimal-witness question at n = 3, sharply:

    • `no_small_witness_n3` — there is NO defect-one witness at n = 3 with all of
      a, b, c below 9 (equivalently c ≤ 8);
    • `unique_small_witness_n3` — the ONLY defect-one witness at n = 3 with all of
      a, b, c below 10 is (6, 8, 9);
    • `fermat_defect_three_minimal` — packaging both with existence: (6, 8, 9) is
      THE smallest defect-one witness at n = 3, and it is the unique one with
      c ≤ 9.  So the least third coordinate of any n = 3 defect-one witness is 9.

  Contrast with OQ-04: that file shows (6,8,9) merely *lies inside* the c ≤ 100
  box; here we show nothing smaller works, so 9 is optimal, not just an upper
  witness.

  All proofs use the kernel `decide` (NOT `native_decide`), so the file is fully
  verified with 0 axioms — in particular no `Lean.ofReduceBool` is introduced
  (unlike OQ-04, whose c ≤ 100 searches require `native_decide`).  The small
  bound here (cubes below 9³ = 729) keeps the kernel computation light.

  Honesty note: these are finite bounded-search facts about n = 3 only.  They do
  NOT touch the open asymptotic conjecture (whether M(n) → ∞, or whether
  witnesses exist for all n) — they pin the smallest n = 3 witness exactly.
-/

import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOneOQ03

open FermatDefectOne

/-- There is no defect-one witness at `n = 3` with every coordinate below 9
    (equivalently `c ≤ 8`).  Verified by exhaustive kernel computation. -/
theorem no_small_witness_n3 :
    ∀ a < 9, ∀ b < 9, ∀ c < 9, ¬ FermatDefectWitness 3 a b c := by decide

/-- The only defect-one witness at `n = 3` with every coordinate below 10 is
    `(6, 8, 9)`.  Together with `no_small_witness_n3` this shows `(6,8,9)` is the
    unique witness with `c ≤ 9`. -/
theorem unique_small_witness_n3 :
    ∀ a < 10, ∀ b < 10, ∀ c < 10,
      FermatDefectWitness 3 a b c → a = 6 ∧ b = 8 ∧ c = 9 := by decide

/-- **The smallest `n = 3` defect-one witness.**

    `(6, 8, 9)` is a defect-one witness (`6³ + 8³ + 1 = 9³`), no defect-one
    witness at `n = 3` has all coordinates below 9, and `(6, 8, 9)` is the unique
    witness with all coordinates below 10.  Hence `(6, 8, 9)` is the minimal
    defect-one witness at `n = 3` and `c = 9` is the least possible third
    coordinate. -/
theorem fermat_defect_three_minimal :
    FermatDefectWitness 3 6 8 9 ∧
      (∀ a < 9, ∀ b < 9, ∀ c < 9, ¬ FermatDefectWitness 3 a b c) ∧
      (∀ a < 10, ∀ b < 10, ∀ c < 10,
        FermatDefectWitness 3 a b c → a = 6 ∧ b = 8 ∧ c = 9) :=
  ⟨by decide, no_small_witness_n3, unique_small_witness_n3⟩

end FermatDefectOneOQ03
