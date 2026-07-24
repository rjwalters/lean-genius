import Proofs.GodelSecondIncompletenessOQ02Kalmar

/-
# S21: Decidability of the box-free fragment of GL

## Context

`godel-second-incompleteness-oq02-oq-02`, iteration S21. Prior sessions:

* S8 built the Hilbert system `GL_proves` (`GLSyntax.lean`);
* S18 derived the 4 schema axiom-free (`GLFour.lean`);
* S19 proved Kalmár completeness for the box-free fragment
  (`Kalmar.lean`): for box-free `φ`,
  `GL_proves φ ↔ ∀ v, eval v φ = true` (`boxfree_characterization`);
* S20 (PR #43350) adds Kripke soundness — independent of this file.

## What this file does

S19's characterization quantifies over **all** valuations
`v : PropAtom → Bool` — an infinite type, so it is not by itself a
decision procedure. This file closes that gap:

1. `eval_congr` — `eval` only depends on the atoms occurring in the
   formula (no box-freeness needed: boxes evaluate to `true` outright).
2. `allSubsets` / `filterTrue` / `valOf` — a self-contained (core-only,
   Mathlib-free, matching the chain's style) enumeration of the `2^k`
   valuations on the `k` atoms of `φ`, with a coverage lemma: every
   valuation agrees on `atoms φ` with `valOf` of some enumerated subset.
3. `tautCheck : GLFormula → Bool` — the finite truth-table check.
4. **`tautCheck_correct`**: for box-free `φ`,
   `GL_proves φ ↔ tautCheck φ = true`.
5. **`decidableGLProvesBoxFree`**: `Decidable (GL_proves φ)` for
   box-free `φ` — *provability in the box-free fragment of GL is
   decidable*, by kernel computation (no `native_decide`, no axioms
   beyond the foundational ones).
6. Demos by `decide`: GL proves Peirce's law, and GL does **not** prove
   `(p → q) → p` — a non-derivability result obtained by pure
   computation, complementing S19's hand-built `GL_proves_no_atom`.

## Relation to the open question

The parent chain studies provability logic as the modal shadow of
Gödel's second incompleteness theorem. Decidability of the box-free
fragment is the first computability-theoretic metatheorem in the chain;
full GL decidability (Segerberg's finite model property) needs the S20
Kripke semantics plus filtration — recorded as a candidate S22+.

Tags: provability-logic, GL, decidability, truth-table, Kalmar,
finite-model-property
-/

namespace GodelSecondDecidable

open GodelSecondGLSyntax GodelSecondKalmar

local infixr:55 " ⟶ " => GLFormula.impl
local notation "⊥ₘ" => GLFormula.falsum

/-! ## Valuations from finite data -/

/-- The valuation that is `true` exactly on the listed atoms. -/
def valOf : List PropAtom → PropAtom → Bool
  | [], _ => false
  | a :: rest, p => (p == a) || valOf rest p

/-- The atoms of `as` on which `v` is `true`. -/
def filterTrue (v : PropAtom → Bool) : List PropAtom → List PropAtom
  | [] => []
  | a :: rest => if v a then a :: filterTrue v rest else filterTrue v rest

/-- All `2^n` subsets (as sublists) of a list of atoms. -/
def allSubsets : List PropAtom → List (List PropAtom)
  | [] => [[]]
  | a :: rest => allSubsets rest ++ (allSubsets rest).map (a :: ·)

theorem valOf_eq_true_iff_mem (ts : List PropAtom) (a : PropAtom) :
    valOf ts a = true ↔ a ∈ ts := by
  induction ts with
  | nil => simp [valOf]
  | cons b rest ih =>
      simp [valOf, ih, beq_iff_eq]

theorem mem_filterTrue (v : PropAtom → Bool) (as : List PropAtom) (a : PropAtom) :
    a ∈ filterTrue v as ↔ a ∈ as ∧ v a = true := by
  induction as with
  | nil => simp [filterTrue]
  | cons b rest ih =>
      by_cases hb : v b = true
      · simp only [filterTrue, if_pos hb, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨hmem, hv⟩)
          · exact ⟨Or.inl rfl, hb⟩
          · exact ⟨Or.inr hmem, hv⟩
        · rintro ⟨rfl | hmem, hv⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hmem, hv⟩
      · simp only [filterTrue, if_neg hb, List.mem_cons, ih]
        constructor
        · rintro ⟨hmem, hv⟩
          exact ⟨Or.inr hmem, hv⟩
        · rintro ⟨rfl | hmem, hv⟩
          · exact absurd hv hb
          · exact ⟨hmem, hv⟩

/-- **Coverage**: the true-set of any valuation on `as` is one of the
enumerated subsets. -/
theorem filterTrue_mem_allSubsets (v : PropAtom → Bool) (as : List PropAtom) :
    filterTrue v as ∈ allSubsets as := by
  induction as with
  | nil => simp [filterTrue, allSubsets]
  | cons a rest ih =>
      by_cases ha : v a = true
      · simp only [filterTrue, if_pos ha, allSubsets, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨_, ih, rfl⟩)
      · simp only [filterTrue, if_neg ha, allSubsets, List.mem_append]
        exact Or.inl ih

/-- **Agreement**: `valOf (filterTrue v as)` agrees with `v` on `as`. -/
theorem valOf_filterTrue (v : PropAtom → Bool) (as : List PropAtom)
    (a : PropAtom) (ha : a ∈ as) : valOf (filterTrue v as) a = v a := by
  cases hv : v a
  · cases hval : valOf (filterTrue v as) a
    · rfl
    · exact absurd ((mem_filterTrue v as a).mp
        ((valOf_eq_true_iff_mem _ a).mp hval)).2 (by simp [hv])
  · exact (valOf_eq_true_iff_mem _ a).mpr ((mem_filterTrue v as a).mpr ⟨ha, hv⟩)

/-! ## `eval` depends only on the occurring atoms -/

/-- `eval` is determined by the values on `atoms φ`. No box-freeness
hypothesis: boxed subformulas evaluate to `true` regardless of `v`. -/
theorem eval_congr {v w : PropAtom → Bool} :
    ∀ {φ : GLFormula}, (∀ a ∈ atoms φ, v a = w a) → eval v φ = eval w φ
  | .atom p, h => h p (by simp [atoms])
  | .falsum, _ => rfl
  | .impl p q, h => by
      have hp := eval_congr (φ := p) fun a ha => h a (List.mem_append_left _ ha)
      have hq := eval_congr (φ := q) fun a ha => h a (List.mem_append_right _ ha)
      simp [eval, hp, hq]
  | .box _, _ => rfl

/-! ## The decision procedure -/

/-- Finite truth-table check: `φ` evaluates `true` under the valuation
of every subset of its atoms. -/
def tautCheck (φ : GLFormula) : Bool :=
  (allSubsets (atoms φ)).all fun ts => eval (valOf ts) φ

/-- **S21 main theorem**: for box-free `φ`, GL-provability coincides
with the finite truth-table check. Combines S19's
`boxfree_characterization` with coverage + agreement + `eval_congr`. -/
theorem tautCheck_correct {φ : GLFormula} (hbf : BoxFree φ) :
    GL_proves φ ↔ tautCheck φ = true := by
  rw [boxfree_characterization hbf, tautCheck, List.all_eq_true]
  constructor
  · intro h ts _
    exact h (valOf ts)
  · intro h v
    have hmem := filterTrue_mem_allSubsets v (atoms φ)
    have hval := h _ hmem
    have hagree : eval (valOf (filterTrue v (atoms φ))) φ = eval v φ :=
      eval_congr fun a ha => valOf_filterTrue v (atoms φ) a ha
    rw [← hagree]
    exact hval

/-- **Decidability of the box-free fragment of GL**: provability of any
box-free formula is decided by kernel computation of `tautCheck`. -/
def decidableGLProvesBoxFree {φ : GLFormula} (hbf : BoxFree φ) :
    Decidable (GL_proves φ) :=
  decidable_of_iff (tautCheck φ = true) (tautCheck_correct hbf).symm

/-! ## Demos: derivability and non-derivability by pure computation -/

/-- GL proves Peirce's law — by running the decision procedure inside
the kernel (`decide`), not by exhibiting a Hilbert derivation. -/
theorem GL_proves_peirce :
    GL_proves ((((.atom 0 ⟶ .atom 1) ⟶ .atom 0) ⟶ .atom 0)) :=
  (tautCheck_correct (by simp [BoxFree])).mpr (by decide)

/-- GL does **not** prove `(p → q) → p` — non-derivability by pure
computation (the valuation `p ↦ false` refutes it, and the decision
procedure finds this). -/
theorem GL_not_proves_assertion :
    ¬ GL_proves ((.atom 0 ⟶ .atom 1) ⟶ .atom 0) := fun h =>
  absurd ((tautCheck_correct (by simp [BoxFree])).mp h) (by decide)

#check @tautCheck_correct
#check @decidableGLProvesBoxFree
#check @GL_proves_peirce
#check @GL_not_proves_assertion

#print axioms tautCheck_correct
#print axioms GL_proves_peirce

end GodelSecondDecidable
