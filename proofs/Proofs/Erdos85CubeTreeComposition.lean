import Proofs.Erdos85OneHighV2ExtensionCertificate

/-!
# Cube-tree composition for partitioned LRAT certificates

A cube-and-conquer run splits a base CNF `F` along a complete binary tree of
variable decisions.  Each leaf cube `c` is solved as the CNF obtained by
prepending the unit clauses of `c` to `F` (this is exactly the byte layout of
`cube_verdict.cube_bytes`: unit clauses, sorted by variable, inserted directly
after the DIMACS header).  This module proves the composition step:

* `cnf_unsat_of_cubeTree`: if every cube of a complete tree is covered by a
  cube whose extended CNF is UNSAT, then `F` itself is UNSAT;
* `cnf_unsat_of_extension_lrat`: one leaf's `LRAT.check` (on the
  extension-padded CNF produced by `prepareLratProof`) gives that leaf's UNSAT;
* `oneHighFamilyV2CheckedUnsat_of_cubeTree`: the H1 consumer interface.

Completeness of the tree is structural: `CubeTree.split` always has both
children, so `CubeTree.exists_cube` holds for every assignment.  The covering
hypothesis only relates the tree's root-first literal lists to the
solver-side literal lists (which are sorted by variable), and is decidable.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- Satisfaction of one DIMACS literal under a zero-based `Std.Sat`
assignment, matching `dimacsClauseToSatClause`. -/
def DimacsLitTrue (a : Nat → Bool) (l : Int) : Prop :=
  a (l.natAbs - 1) = decide (0 < l)

/-- The cube CNF: the unit clauses of `cube` (in the given order) followed by
the clauses of `cnf`. -/
def cubeCnf (cnf : CNF Nat) (cube : List Int) : CNF Nat where
  clauses := (cube.map fun l => dimacsClauseToSatClause [l]).toArray ++ cnf.clauses

theorem clauseEval_unit_of_dimacsLitTrue {a : Nat → Bool} {l : Int}
    (h : DimacsLitTrue a l) :
    CNF.Clause.eval a (dimacsClauseToSatClause [l]) = true := by
  simp [dimacsClauseToSatClause, CNF.Clause.eval, DimacsLitTrue] at h ⊢
  simp [h]

theorem eval_cubeCnf_of_lits {cnf : CNF Nat} {cube : List Int} {a : Nat → Bool}
    (hlits : ∀ l ∈ cube, DimacsLitTrue a l) (hsat : cnf.eval a = true) :
    (cubeCnf cnf cube).eval a = true := by
  unfold CNF.eval at hsat ⊢
  simp only [cubeCnf, Array.all_append, Bool.and_eq_true]
  refine ⟨?_, hsat⟩
  rw [Array.all_eq_true_iff_forall_mem]
  intro clause hclause
  simp only [List.mem_toArray, List.mem_map] at hclause
  obtain ⟨l, hl, rfl⟩ := hclause
  exact clauseEval_unit_of_dimacsLitTrue (hlits l hl)

/-- A complete binary cube tree.  `split var pos neg` branches on the
zero-based variable `var`, i.e. on the DIMACS literal `var + 1` (subtree
`pos`) versus `-(var + 1)` (subtree `neg`). -/
inductive CubeTree where
  | leaf : CubeTree
  | split (var : Nat) (pos neg : CubeTree) : CubeTree
  deriving Repr, DecidableEq

/-- The leaf cubes of a tree, each listed root-first as DIMACS literals. -/
def CubeTree.cubes : CubeTree → List (List Int)
  | .leaf => [[]]
  | .split var pos neg =>
      pos.cubes.map (((var + 1 : Nat) : Int) :: ·) ++
        neg.cubes.map ((-((var + 1 : Nat) : Int)) :: ·)

/-- Number of leaves. -/
def CubeTree.leafCount : CubeTree → Nat
  | .leaf => 1
  | .split _ pos neg => pos.leafCount + neg.leafCount

/-- Every assignment lies in some leaf cube: the partition is complete. -/
theorem CubeTree.exists_cube (a : Nat → Bool) :
    ∀ T : CubeTree, ∃ c ∈ T.cubes, ∀ l ∈ c, DimacsLitTrue a l
  | .leaf => ⟨[], by simp [CubeTree.cubes]⟩
  | .split var pos neg => by
      cases hv : a var with
      | true =>
          obtain ⟨c, hc, hlits⟩ := CubeTree.exists_cube a pos
          refine ⟨((var + 1 : Nat) : Int) :: c, ?_, ?_⟩
          · simp only [CubeTree.cubes, List.mem_append, List.mem_map]
            exact Or.inl ⟨c, hc, rfl⟩
          · intro l hl
            rcases List.mem_cons.mp hl with rfl | hl
            · have hpos : (0 : Int) < ((var + 1 : Nat) : Int) := by omega
              simp only [DimacsLitTrue, Int.natAbs_cast, Nat.add_sub_cancel, hv,
                decide_eq_true hpos]
            · exact hlits l hl
      | false =>
          obtain ⟨c, hc, hlits⟩ := CubeTree.exists_cube a neg
          refine ⟨(-((var + 1 : Nat) : Int)) :: c, ?_, ?_⟩
          · simp only [CubeTree.cubes, List.mem_append, List.mem_map]
            exact Or.inr ⟨c, hc, rfl⟩
          · intro l hl
            rcases List.mem_cons.mp hl with rfl | hl
            · have hneg : ¬ (0 : Int) < -((var + 1 : Nat) : Int) := by omega
              simp only [DimacsLitTrue, Int.natAbs_neg, Int.natAbs_cast, Nat.add_sub_cancel, hv,
                decide_eq_false hneg]
            · exact hlits l hl

/-- Composition: a complete cube tree whose cubes are each covered by an
UNSAT cube CNF refutes the base CNF. -/
theorem cnf_unsat_of_cubeTree (cnf : CNF Nat) (T : CubeTree)
    (cubes : List (List Int))
    (hcover : ∀ c ∈ T.cubes, ∃ d ∈ cubes, ∀ l ∈ d, l ∈ c)
    (hleaf : ∀ d ∈ cubes, (cubeCnf cnf d).Unsat) :
    cnf.Unsat := by
  intro a
  cases h : cnf.eval a with
  | false => rfl
  | true =>
      obtain ⟨c, hc, hlits⟩ := T.exists_cube a
      obtain ⟨d, hd, hsub⟩ := hcover c hc
      have hfalse := hleaf d hd a
      rw [eval_cubeCnf_of_lits (fun l hl => hlits l (hsub l hl)) h] at hfalse
      exact absurd hfalse (by decide)

/-- One leaf: a successful standard `LRAT.check` on the extension-padded CNF
refutes the unpadded CNF. -/
theorem cnf_unsat_of_extension_lrat (cnf : CNF Nat)
    (rawProof preparedProof : Array LRAT.IntAction)
    (hcheck : LRAT.check preparedProof
      (LratExtensionVariables.padCnfForProof cnf rawProof)) :
    cnf.Unsat :=
  cnf_unsat_of_padCnfForProof_unsat cnf rawProof
    (LRAT.check_sound preparedProof _ hcheck)

/-- The H1 consumer interface from a cube tree of UNSAT leaves. -/
theorem oneHighFamilyV2CheckedUnsat_of_cubeTree
    {profile : Nat} {table : OneHighMissTable}
    (hnz : ∀ clause ∈ (oneHighFamilyV2Clauses profile table).clauses,
      DimacsClauseNonzero clause)
    (T : CubeTree) (cubes : List (List Int))
    (hcover : ∀ c ∈ T.cubes, ∃ d ∈ cubes, ∀ l ∈ d, l ∈ c)
    (hleaf : ∀ d ∈ cubes,
      (cubeCnf (oneHighFamilyV2SatCnf profile table) d).Unsat) :
    OneHighFamilyV2CheckedUnsat profile table where
  nonzero := hnz
  unsat := by
    intro a hsat
    have hu := cnf_unsat_of_cubeTree _ T cubes hcover hleaf a
    rw [CNF.sat_def] at hsat
    rw [hsat] at hu
    contradiction

end Erdos85
