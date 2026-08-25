import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnfSatisfaction
import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneNonzero
import Proofs.Erdos85OrderFortyNineT0CubeResidualTransport

/-!
# Closing the semantic soundness socket for the seven-high t0 cube CNFs

The generator-satisfaction development constructs a valuation and proves all
emitted DIMACS clauses true.  This module packages that result as the
`CNF.Sat` value consumed by the reduced cube-one certificate bridge.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

set_option maxRecDepth 1000000

private theorem sevenHighT0CubeHighPair_bounds :
    ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeHighs,
      pair.1 < 7 ∧ pair.2 < 7 ∧ pair.1 < pair.2 := by
  native_decide

private theorem sevenHighT0CubeVertexPair_bounds :
    ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeVertices,
      pair.1 < 49 ∧ pair.2 < 49 ∧ pair.1 < pair.2 := by
  native_decide

private theorem sevenHighT0CubeLow_bounds :
    ∀ x ∈ sevenHighT0CubeLows, 7 ≤ x ∧ x < 49 := by
  native_decide

private theorem sevenHighT0CubeLow_mem_of_bounds
    {w : Nat} (hlo : 7 ≤ w) (hhi : w < 49) :
    w ∈ sevenHighT0CubeLows := by
  simp only [sevenHighT0CubeLows, List.mem_map, List.mem_range]
  refine ⟨w - 7, ?_, Nat.sub_add_cancel hlo⟩
  omega

private theorem sevenHighT0CubeN1Eight_value (k : Nat) (hk : k < 7) :
    decide (k + 8 = 7 ∨ (15 ≤ k + 8 ∧ k + 8 < 22)) = false := by
  simp
  omega

private theorem sevenHighT0CubeN1Fifteen_value (k : Nat) (hk : k < 7) :
    decide (k + 15 = 7 ∨ (15 ≤ k + 15 ∧ k + 15 < 22)) = true := by
  simp
  omega

private theorem sevenHighT0CubeN1TwentyTwo_value (k : Nat) (_hk : k < 27) :
    decide (k + 22 = 7 ∨ (15 ≤ k + 22 ∧ k + 22 < 22)) = false := by
  simp

private theorem sevenHighT0CubeN0Pair_bounds :
    ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeN0,
      7 ≤ pair.1 ∧ pair.1 < 15 ∧ 7 ≤ pair.2 ∧
        pair.2 < 15 ∧ pair.1 < pair.2 := by
  native_decide

private theorem sevenHighT0CubeN1Pair_bounds :
    ∀ pair ∈ sevenHighT0CubePairs sevenHighT0CubeN1,
      (pair.1 = 7 ∨ (15 ≤ pair.1 ∧ pair.1 < 22)) ∧
      (pair.2 = 7 ∨ (15 ≤ pair.2 ∧ pair.2 < 22)) ∧
      pair.1 < pair.2 := by
  native_decide

private theorem sevenHighT0Cube_mem_of_mem_pairs
    {xs : List Nat} {pair : Nat × Nat}
    (h : pair ∈ sevenHighT0CubePairs xs) :
    pair.1 ∈ xs ∧ pair.2 ∈ xs ∧ pair.1 < pair.2 := by
  simp only [sevenHighT0CubePairs, List.mem_flatMap, List.mem_map,
    List.mem_filter] at h
  obtain ⟨a, ha, b, ⟨hb, hab⟩, hp⟩ := h
  cases hp
  exact ⟨ha, hb, of_decide_eq_true hab⟩

private theorem sevenHighT0CubeAtomValue_edge_nat
    (edges : BitVec 1176) (i j : Nat) (hi : i < 49) (hj : j < 49) :
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges)
      (.edge (min i j) (max i j)) =
      orderFortyNineBitAdj edges ⟨i, hi⟩ ⟨j, hj⟩ := by
  simpa using sevenHighT0CubeAtomValue_edge_bitAdj edges
    ⟨i, hi⟩ ⟨j, hj⟩

private theorem sevenHighT0CubeAtomValue_edge_ordered
    (edges : BitVec 1176) (i j : Nat) (hi : i < 49) (hj : j < 49)
    (hij : i ≤ j) :
    sevenHighT0CubeAtomValue (orderFortyNineBitAdj edges) (.edge i j) =
      orderFortyNineBitAdj edges ⟨i, hi⟩ ⟨j, hj⟩ := by
  simpa [min_eq_left hij, max_eq_right hij] using
    sevenHighT0CubeAtomValue_edge_nat edges i j hi hj

theorem sevenHighT0CubeRunnerPremises_of_relationCore
    {edges : BitVec 1176} {cube : Nat}
    (h : SevenHighT0CubeRelationCore cube
      (orderFortyNineBitAdj edges)) :
    SevenHighT0CubeRunnerPremises edges cube := by
  rcases h with ⟨hcube, hind, hn0, hm0, hn1, hm1, hcommon,
    hc4, hdegrees, hpartition, hcubes⟩
  constructor
  · intro pair hp
    obtain ⟨hi, hj, hij⟩ := sevenHighT0CubeHighPair_bounds pair hp
    have hi49 : pair.1 < 49 := by omega
    have hj49 : pair.2 < 49 := by omega
    let i : Fin 49 := ⟨pair.1, hi49⟩
    let j : Fin 49 := ⟨pair.2, hj49⟩
    have hne : i ≠ j := Fin.ne_of_lt (by simpa [i, j] using hij)
    rw [sevenHighT0CubeAtomValue_edge_nat edges pair.1 pair.2 hi49 hj49]
    simpa only [i, j] using hind i j hi hj hne
  · intro x hx
    obtain ⟨hlo, hhi⟩ := sevenHighT0CubeLow_bounds x hx
    let xf : Fin 49 := ⟨x, hhi⟩
    rw [sevenHighT0CubeAtomValue_edge_ordered edges 0 x (by omega) hhi (by omega)]
    change orderFortyNineBitAdj edges (0 : Fin 49) xf = decide (x < 15)
    exact hn0 xf hlo
  · intro pair hp
    obtain ⟨ha0, ha1, hb0, hb1, hab⟩ :=
      sevenHighT0CubeN0Pair_bounds pair hp
    have ha49 : pair.1 < 49 := by omega
    have hb49 : pair.2 < 49 := by omega
    let a : Fin 49 := ⟨pair.1, ha49⟩
    let b : Fin 49 := ⟨pair.2, hb49⟩
    have hne : a ≠ b := Fin.ne_of_lt (by simpa [a, b] using hab)
    rw [sevenHighT0CubeAtomValue_edge_nat edges pair.1 pair.2 ha49 hb49]
    simpa only [a, b, min_eq_left (Nat.le_of_lt hab),
      max_eq_right (Nat.le_of_lt hab)] using
      hm0 a b ha0 ha1 hb0 hb1 hne
  · rw [sevenHighT0CubeAtomValue_edge_ordered edges 1 7 (by omega) (by omega) (by omega)]
    simpa using hn1 (7 : Fin 49) (by omega)
  · intro k hk
    have hk' : k < 7 := by simpa using hk
    let x : Fin 49 := ⟨k + 8, by omega⟩
    rw [sevenHighT0CubeAtomValue_edge_ordered edges 1 (k + 8) (by omega) (by omega) (by omega)]
    change orderFortyNineBitAdj edges (1 : Fin 49) x = false
    have hxlow : 7 ≤ x.val := by dsimp [x]; omega
    rw [hn1 x hxlow]
    exact sevenHighT0CubeN1Eight_value k hk'
  · intro k hk
    have hk' : k < 7 := by simpa using hk
    let x : Fin 49 := ⟨k + 15, by omega⟩
    rw [sevenHighT0CubeAtomValue_edge_ordered edges 1 (k + 15) (by omega) (by omega) (by omega)]
    change orderFortyNineBitAdj edges (1 : Fin 49) x = true
    have hxlow : 7 ≤ x.val := by dsimp [x]; omega
    rw [hn1 x hxlow]
    exact sevenHighT0CubeN1Fifteen_value k hk'
  · intro k hk
    have hk' : k < 27 := by simpa using hk
    let x : Fin 49 := ⟨k + 22, by omega⟩
    rw [sevenHighT0CubeAtomValue_edge_ordered edges 1 (k + 22) (by omega) (by omega) (by omega)]
    change orderFortyNineBitAdj edges (1 : Fin 49) x = false
    have hxlow : 7 ≤ x.val := by dsimp [x]; omega
    rw [hn1 x hxlow]
    exact sevenHighT0CubeN1TwentyTwo_value k hk'
  · intro pair hp
    obtain ⟨ha, hb, hab⟩ := sevenHighT0CubeN1Pair_bounds pair hp
    have ha49 : pair.1 < 49 := by rcases ha with ha | ha <;> omega
    have hb49 : pair.2 < 49 := by rcases hb with hb | hb <;> omega
    let a : Fin 49 := ⟨pair.1, ha49⟩
    let b : Fin 49 := ⟨pair.2, hb49⟩
    have hne : a ≠ b := Fin.ne_of_lt (by simpa [a, b] using hab)
    rw [sevenHighT0CubeAtomValue_edge_nat edges pair.1 pair.2 ha49 hb49]
    simpa only [a, b, min_eq_left (Nat.le_of_lt hab),
      max_eq_right (Nat.le_of_lt hab)] using
      hm1 a b ha hb hne
  · intro pair hp w hw hvalue
    obtain ⟨hi, hj, hij⟩ := sevenHighT0CubeHighPair_bounds pair hp
    obtain ⟨hlo, hhi⟩ := sevenHighT0CubeLow_bounds w hw
    have hi49 : pair.1 < 49 := by omega
    have hj49 : pair.2 < 49 := by omega
    let i : Fin 49 := ⟨pair.1, hi49⟩
    let j : Fin 49 := ⟨pair.2, hj49⟩
    let wf : Fin 49 := ⟨w, hhi⟩
    simp [sevenHighT0CubeAtomValue, hi49, hj49, hhi] at hvalue
    have hv : orderFortyNineBitAdj edges i wf = true := by
      simpa [i, wf] using hvalue.1
    rw [sevenHighT0CubeAtomValue_edge_nat edges pair.1 w (by omega) hhi]
    exact hv
  · intro pair hp w hw hvalue
    obtain ⟨hi, hj, hij⟩ := sevenHighT0CubeHighPair_bounds pair hp
    obtain ⟨hlo, hhi⟩ := sevenHighT0CubeLow_bounds w hw
    have hi49 : pair.1 < 49 := by omega
    have hj49 : pair.2 < 49 := by omega
    let i : Fin 49 := ⟨pair.1, hi49⟩
    let j : Fin 49 := ⟨pair.2, hj49⟩
    let wf : Fin 49 := ⟨w, hhi⟩
    simp [sevenHighT0CubeAtomValue, hi49, hj49, hhi] at hvalue
    have hv : orderFortyNineBitAdj edges j wf = true := by
      simpa [j, wf] using hvalue.2
    rw [sevenHighT0CubeAtomValue_edge_nat edges pair.2 w (by omega) hhi]
    exact hv
  · intro pair hp
    obtain ⟨hi, hj, hij⟩ := sevenHighT0CubeHighPair_bounds pair hp
    have hi49 : pair.1 < 49 := by omega
    have hj49 : pair.2 < 49 := by omega
    have hne : (⟨pair.1, hi49⟩ : Fin 49) ≠ ⟨pair.2, hj49⟩ :=
      Fin.ne_of_lt (by simpa using hij)
    obtain ⟨w, hwlow, hwi, hwj⟩ :=
      hcommon ⟨pair.1, hi49⟩ ⟨pair.2, hj49⟩
        hi hj hne
    refine ⟨w.val, ?_, ?_⟩
    · exact sevenHighT0CubeLow_mem_of_bounds hwlow w.isLt
    · simp [sevenHighT0CubeAtomValue, hi49, hj49, w.isLt, hwi, hwj]
  · intro pair hp witnesses hw hall
    obtain ⟨hi, hj, hij⟩ := sevenHighT0CubeVertexPair_bounds pair hp
    obtain ⟨hw1list, hw2list, hw12⟩ :=
      sevenHighT0Cube_mem_of_mem_pairs hw
    have hw1 : witnesses.1 < 49 := by
      have := (List.mem_filter.mp hw1list).1
      simpa [sevenHighT0CubeVertices] using this
    have hw2 : witnesses.2 < 49 := by
      have := (List.mem_filter.mp hw2list).1
      simpa [sevenHighT0CubeVertices] using this
    rcases hall with ⟨hi1, hj1, hi2, hj2⟩
    let i : Fin 49 := ⟨pair.1, hi⟩
    let j : Fin 49 := ⟨pair.2, hj⟩
    let w1 : Fin 49 := ⟨witnesses.1, hw1⟩
    let w2 : Fin 49 := ⟨witnesses.2, hw2⟩
    have hi1' : orderFortyNineBitAdj edges i w1 = true := by
      rw [← sevenHighT0CubeAtomValue_edge_nat edges pair.1 witnesses.1 hi hw1]
      simpa [i, w1] using hi1
    have hj1' : orderFortyNineBitAdj edges j w1 = true := by
      rw [← sevenHighT0CubeAtomValue_edge_nat edges pair.2 witnesses.1 hj hw1]
      simpa [j, w1] using hj1
    have hi2' : orderFortyNineBitAdj edges i w2 = true := by
      rw [← sevenHighT0CubeAtomValue_edge_nat edges pair.1 witnesses.2 hi hw2]
      simpa [i, w2] using hi2
    have hj2' : orderFortyNineBitAdj edges j w2 = true := by
      rw [← sevenHighT0CubeAtomValue_edge_nat edges pair.2 witnesses.2 hj hw2]
      simpa [j, w2] using hj2
    let common := Finset.univ.filter fun w =>
      orderFortyNineBitAdj edges i w && orderFortyNineBitAdj edges j w
    have hw1mem : w1 ∈ common := by simp [common, hi1', hj1']
    have hw2mem : w2 ∈ common := by simp [common, hi2', hj2']
    have heq := (Finset.card_le_one.mp
      (hc4 i j (Fin.ne_of_lt (by simpa [i, j] using hij))))
      w1 hw1mem w2 hw2mem
    have hne : w1 ≠ w2 := Fin.ne_of_lt (by simpa [w1, w2] using hw12)
    exact hne heq
  · exact hdegrees
  · intro y hy high hh
    obtain ⟨hylo, hyhi⟩ := sevenHighT0CubeLow_bounds y hy
    have hhigh : high < 2 := by rcases (by simpa using hh) with rfl | rfl <;> omega
    obtain ⟨x, hxmem, hxy, hadj⟩ :=
      hpartition ⟨y, hyhi⟩ hylo ⟨high, hhigh⟩
    refine ⟨x.val, hxmem, ?_, ?_⟩
    · exact fun heq => hxy (Fin.ext heq)
    · rw [sevenHighT0CubeAtomValue_edge_nat edges y x.val hyhi x.isLt]
      exact hadj
  · intro index hindex
    have hi : index < 7 := by simpa using hindex
    let indexf : Fin 7 := ⟨index, hi⟩
    rw [sevenHighT0CubeAtomValue_edge_ordered edges 9 (index + 15)
      (by omega) (by omega) (by omega)]
    simpa [indexf] using hcubes indexf

theorem sevenHighT0CubeOne_formulaSatisfied_of_runnerPremises
    {edges : BitVec 1176}
    (h : SevenHighT0CubeRunnerPremises edges 1) :
    ∃ val : DimacsValuation,
      dimacsFormulaSatisfied val (sevenHighT0CubeFinalState 1).clauses := by
  exact ⟨(sevenHighT0CubeRunner edges 1).2,
    sevenHighT0CubeRunner_finalFormulaSatisfied edges 1 h⟩

set_option maxRecDepth 1000000 in
theorem orderFortyNineGeneratedH7T0CubeSatCnf_sat_of_formulaSatisfied
    {val : DimacsValuation}
    (hsat : dimacsFormulaSatisfied val
      (sevenHighT0CubeFinalState 1).clauses) :
    (orderFortyNineGeneratedH7T0CubeSatCnf 1).Sat
      (satAssignmentOfDimacs val) := by
  simpa only [orderFortyNineGeneratedH7T0CubeSatCnf] using
    satCnf_of_dimacsFormulaSatisfied
      sevenHighT0CubeOneFinalState_clauses_nonzero hsat

theorem orderFortyNineGeneratedH7T0CubeSatCnf_sat_of_runnerPremises
    {edges : BitVec 1176}
    (h : SevenHighT0CubeRunnerPremises edges 1) :
    ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf 1).Sat assignment := by
  obtain ⟨val, hsat⟩ :=
    sevenHighT0CubeOne_formulaSatisfied_of_runnerPremises h
  exact ⟨satAssignmentOfDimacs val,
    orderFortyNineGeneratedH7T0CubeSatCnf_sat_of_formulaSatisfied hsat⟩

/-- The lightweight relation interface produced by normalization extends to
the exact generated CNF.  This is deliberately stated without importing the
larger two-cube capstone, so the expensive generated-CNF development remains
independent of the canonical-stratum import chain. -/
theorem orderFortyNineGeneratedH7T0CubeSatCnf_sat_of_relationCore
    {edges : BitVec 1176}
    (h : SevenHighT0CubeRelationCore 1
      (orderFortyNineBitAdj edges)) :
    ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf 1).Sat assignment := by
  apply orderFortyNineGeneratedH7T0CubeSatCnf_sat_of_runnerPremises
  exact sevenHighT0CubeRunnerPremises_of_relationCore h

end Erdos85
