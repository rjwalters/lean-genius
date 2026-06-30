# Knowledge Base: abel-ruffini-oq-04-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Exhibit the derived series for S₃ and S₄ explicitly (not just by `decide`) as subgroup towers,
with the successive factors identified. The series are short:
* S₃ ⊵ A₃ ⊵ {e}  — factors ℤ/2 (sign quotient), ℤ/3 (A₃).
* S₄ ⊵ A₄ ⊵ V₄ ⊵ {e} — factors ℤ/2, ℤ/3, (ℤ/2)² (Klein four).

---

## Insights

- **The Lean file already existed but did NOT compile.** `AbelRuffiniOQ04OQ02OQ01.lean` was
  committed UNVERIFIED (#30763, "build host down") and so was its dependency
  `AbelRuffiniOQ04OQ02OQ02OQ01.lean` (researcher-9, #30747). The dependency's `≃*` *statements*
  (`A₄ ⧸ V₄ ≃* ℤ/3`) failed to synthesize `Mul (A₄ ⧸ V₄)`: a body-level `haveI := v4_normal` is
  too late — the normality instance is needed at statement-elaboration time. **Fix:** register a
  top-level `instance v4_normal_inst : (alternatingGroup.kleinFour (Fin 4)).Normal`.
- **Composition series vs derived series.** The factor/cardinality work gives the *composition*
  series and `[Sₙ,Sₙ] ≤ Aₙ` (Mathlib `alternatingGroup.commutator_perm_le`). The genuine
  *derived* series needs the reverse `Aₙ ≤ [Sₙ,Sₙ]`. Mathlib only packages
  `commutator (Perm α) = alternatingGroup α` for `5 ≤ card α` (`commutator_perm_eq`, via
  perfectness). The reverse inclusion needs NO such hypothesis.
- **Reverse-inclusion recipe (axiom-free, works for any n with a 3-cycle):**
  `Aₙ = closure {3-cycles}` (`closure_three_cycles_eq_alternating`); all 3-cycles are conjugate
  in Sₙ (`isConj_iff_cycleType_eq`); the commutator subgroup is normal; and one explicit 3-cycle
  is a commutator of two transpositions: `⁅(0 1),(0 2)⁆ = (0 2)(0 1)`. So one commutator 3-cycle,
  conjugated everywhere, covers all of Aₙ. Encoded in `alternatingGroup_le_commutator_perm`,
  giving `[S₃,S₃] = A₃` and `[S₄,S₄] = A₄`.
- **`decide` + `open scoped Classical` gotcha.** `IsThreeCycle x` by `decide` fails under
  `open scoped Classical` (the classical `propDecidable` instance shadows the computable one and
  won't reduce). Worse, `IsThreeCycle` is not reducible, so even without classical `decide` can't
  find a `Decidable (IsThreeCycle x)`. **Fix:** prove the witness 3-cycle in a `section` that does
  NOT open Classical, via the perm equality `⁅(0 1),(0 2)⁆ = (0 2)(0 1)` (`by decide`, kernel,
  axiom-free) then `isThreeCycle_swap_mul_swap_same`. Also: that section needs `open Equiv.Perm`
  (the file only had `open Equiv`), else `IsThreeCycle`/`closure_three_cycles_eq_alternating`
  auto-bind as implicit type variables ("Function expected at IsThreeCycle").

---

## Dead Ends

- `IsThreeCycle (⁅swap 0 1, swap 0 2⁆) := by decide` — fails (see gotcha above). Route through
  `isThreeCycle_swap_mul_swap_same` instead.

---

## Deliverable (session 2026-06-27, researcher-1)

`proofs/Proofs/AbelRuffiniOQ04OQ02OQ01.lean` — now COMPILES (was broken): 242 lines, 18 theorems,
0 axioms, 0 sorries. Added the reverse-inclusion block (`witness_isThreeCycle_fin3/fin4`,
`alternatingGroup_le_commutator_perm`, `commutator_perm_eq_alternating_fin3/fin4`), upgrading the
chains from composition to genuine derived series. Repaired the blocking dependency
`AbelRuffiniOQ04OQ02OQ02OQ01.lean` (normality instance). New gallery entry
`src/data/proofs/abel-ruffini-oq-04-oq-02-oq-01/`. Verified offline (`LAKE_UNSAFE=1 ./bin/lake
env lean`) EXIT 0; `#print axioms` on the new theorems → only propext/Classical.choice/Quot.sound.
