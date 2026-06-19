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

  Verification footprint — all proofs are kernel-checked with 0 axioms (no
  `Lean.ofReduceBool`, unlike the parent's `native_decide` witnesses and OQ-04's
  c ≤ 100 searches).  The bounded searches would, if run on the full
  `FermatDefectWitness` predicate, force the kernel to reduce `Nat.gcd` (defined
  by well-founded recursion) hundreds of times — impractical for `decide`.  We
  sidestep this with a gcd-free *core* predicate `DefectCore` (bounds + the cube
  equation only).  Since every `FermatDefectWitness 3 a b c` satisfies
  `DefectCore a b c` (the primitivity conjunct is dropped), `decide`-ing the core
  over the small box (cubes below 9³ = 729) settles both the non-existence and
  the uniqueness, and the single primitivity check `gcd(gcd 6 8) 9 = 1` for the
  witness is discharged by `norm_num` (kernel-checked, no compiled evaluation).

  Honesty note: these are finite bounded-search facts about n = 3 only.  They do
  NOT touch the open asymptotic conjecture (whether M(n) → ∞, or whether
  witnesses exist for all n) — they pin the smallest n = 3 witness exactly.
-/

import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOneOQ03

open FermatDefectOne

/-- The gcd-free *core* of a defect-one witness at `n = 3`: the size bounds
    together with the cube equation, but WITHOUT the primitivity constraint
    `gcd(gcd a b) c = 1`.  Dropping that conjunct keeps `Nat.gcd` — which is
    defined by well-founded recursion and reduces poorly in the kernel — out of
    the `decide`-driven bounded searches below. -/
private def DefectCore (a b c : Nat) : Prop :=
  2 ≤ a ∧ a ≤ b ∧ b < c ∧ (a ^ 3 + b ^ 3 + 1 = c ^ 3 ∨ a ^ 3 + b ^ 3 = c ^ 3 + 1)

/-- Every defect-one witness at `n = 3` satisfies the gcd-free core: we simply
    forget the primitivity conjunct. -/
private theorem witness_imp_core {a b c : Nat}
    (h : FermatDefectWitness 3 a b c) : DefectCore a b c := by
  obtain ⟨h1, h2, h3, -, h5⟩ := h
  exact ⟨h1, h2, h3, h5⟩

/-- There is no defect-one witness at `n = 3` with every coordinate below 9
    (equivalently `c ≤ 8`).  The exhaustive kernel computation runs on the
    gcd-free core; a genuine witness would satisfy the core, so none exists. -/
theorem no_small_witness_n3 :
    ∀ a < 9, ∀ b < 9, ∀ c < 9, ¬ FermatDefectWitness 3 a b c := by
  have hcore : ∀ a < 9, ∀ b < 9, ∀ c < 9, ¬ DefectCore a b c := by decide
  intro a ha b hb c hc hw
  exact hcore a ha b hb c hc (witness_imp_core hw)

/-- The only defect-one witness at `n = 3` with every coordinate below 10 is
    `(6, 8, 9)`.  Together with `no_small_witness_n3` this shows `(6,8,9)` is the
    unique witness with `c ≤ 9`.  Decided on the gcd-free core: `(6,8,9)` is in
    fact the unique core solution in the box, so a fortiori the unique witness. -/
theorem unique_small_witness_n3 :
    ∀ a < 10, ∀ b < 10, ∀ c < 10,
      FermatDefectWitness 3 a b c → a = 6 ∧ b = 8 ∧ c = 9 := by
  have hcore : ∀ a < 10, ∀ b < 10, ∀ c < 10,
      DefectCore a b c → a = 6 ∧ b = 8 ∧ c = 9 := by decide
  intro a ha b hb c hc hw
  exact hcore a ha b hb c hc (witness_imp_core hw)

/-- `(6, 8, 9)` is a defect-one witness at `n = 3`: `6³ + 8³ + 1 = 9³`, the
    bounds `2 ≤ 6 ≤ 8 < 9` hold, and `gcd(gcd 6 8) 9 = gcd 2 9 = 1`.  All four
    obligations are kernel-checked by `norm_num` (no `native_decide`). -/
theorem witness_six_eight_nine : FermatDefectWitness 3 6 8 9 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  exact Or.inl (by norm_num)

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
  ⟨witness_six_eight_nine, no_small_witness_n3, unique_small_witness_n3⟩

end FermatDefectOneOQ03
