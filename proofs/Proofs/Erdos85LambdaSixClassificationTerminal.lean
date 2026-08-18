import Proofs.Erdos85LambdaSixClassificationLabels

/-! # Semantic terminal for the kernel-checked lambda-six census -/

namespace Erdos85

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem lambdaSixRelabelsTo_of_bool_eq_true
    {d target : BitVec 256} {p : Fin 16 → Fin 16}
    (h : lambdaSixRelabelsToBool d target p = true) :
    lambdaSixRelabelsTo d target p := by
  rw [lambdaSixRelabelsToBool, Bool.and_eq_true] at h
  rcases h with ⟨hinj, hadj⟩
  constructor
  · exact List.nodup_ofFn.mp (of_decide_eq_true hinj)
  · intro x y
    have hx := (List.all_eq_true.mp hadj) _ (List.mem_ofFn.mpr ⟨x, rfl⟩)
    have hxy := (List.all_eq_true.mp hx) _ (List.mem_ofFn.mpr ⟨y, rfl⟩)
    exact of_decide_eq_true hxy

theorem lambdaSixTenSixRModelLabel_correct (i : Fin 144) :
    let label := lambdaSixTenSixRModelLabels i
    lambdaSixRelabelsTo
      (lambdaSixForcedDefect lambdaSixTenSixH2Support256
        (lambdaSixTenSixRModels.getD i.val 0))
      (lambdaSixTenSixDTarget label.1) label.2 := by
  have h := lambdaSixTenSixRModelLabels_correct
  have hmem :
      lambdaSixRelabelsToBool
        (lambdaSixForcedDefect lambdaSixTenSixH2Support256
          (lambdaSixTenSixRModels.getD i.val 0))
        (lambdaSixTenSixDTarget (lambdaSixTenSixRModelLabels i).1)
        (lambdaSixTenSixRModelLabels i).2 ∈
      List.ofFn (fun j : Fin 144 =>
        let label := lambdaSixTenSixRModelLabels j
        lambdaSixRelabelsToBool
          (lambdaSixForcedDefect lambdaSixTenSixH2Support256
            (lambdaSixTenSixRModels.getD j.val 0))
          (lambdaSixTenSixDTarget label.1) label.2) := by
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hi := (List.all_eq_true.mp h) _ hmem
  exact lambdaSixRelabelsTo_of_bool_eq_true hi

theorem lambdaSixFiveFiveThreeThreeRModelLabel_correct (i : Fin 360) :
    let label := lambdaSixFiveFiveThreeThreeRModelLabels i
    lambdaSixRelabelsTo
      (lambdaSixForcedDefect lambdaSixFiveFiveThreeThreeH2Support256
        (lambdaSixFiveFiveThreeThreeRModels.getD i.val 0))
      (lambdaSixFiveFiveThreeThreeDTarget label.1) label.2 := by
  have h := lambdaSixFiveFiveThreeThreeRModelLabels_correct
  have hmem :
      lambdaSixRelabelsToBool
        (lambdaSixForcedDefect lambdaSixFiveFiveThreeThreeH2Support256
          (lambdaSixFiveFiveThreeThreeRModels.getD i.val 0))
        (lambdaSixFiveFiveThreeThreeDTarget
          (lambdaSixFiveFiveThreeThreeRModelLabels i).1)
        (lambdaSixFiveFiveThreeThreeRModelLabels i).2 ∈
      List.ofFn (fun j : Fin 360 =>
        let label := lambdaSixFiveFiveThreeThreeRModelLabels j
        lambdaSixRelabelsToBool
          (lambdaSixForcedDefect lambdaSixFiveFiveThreeThreeH2Support256
            (lambdaSixFiveFiveThreeThreeRModels.getD j.val 0))
          (lambdaSixFiveFiveThreeThreeDTarget label.1) label.2) := by
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hi := (List.all_eq_true.mp h) _ hmem
  exact lambdaSixRelabelsTo_of_bool_eq_true hi

theorem lambdaSixTenSixRModels_length :
    lambdaSixTenSixRModels.length = 144 := by decide

theorem lambdaSixFiveFiveThreeThreeRModels_length :
    lambdaSixFiveFiveThreeThreeRModels.length = 360 := by decide

theorem lambdaSixTenSix_admissible_classified
    {r : BitVec 256}
    (hr : lambdaSixAdmissibleR lambdaSixTenSixH256
      lambdaSixTenSixH2Support256 r) :
    ∃ tag : Fin 3, ∃ p : Fin 16 → Fin 16,
      lambdaSixRelabelsTo
        (lambdaSixForcedDefect lambdaSixTenSixH2Support256 r)
        (lambdaSixTenSixDTarget tag) p := by
  have hrmem := lambdaSixTenSixRModels_complete r hr
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrmem
  let j : Fin 144 := ⟨i.val, by simpa [lambdaSixTenSixRModels_length] using i.isLt⟩
  have hj : lambdaSixTenSixRModels.getD j.val 0 = r := by
    simpa [j] using hi
  let label := lambdaSixTenSixRModelLabels j
  refine ⟨label.1, label.2, ?_⟩
  rw [← hj]
  exact lambdaSixTenSixRModelLabel_correct j

theorem lambdaSixFiveFiveThreeThree_admissible_classified
    {r : BitVec 256}
    (hr : lambdaSixAdmissibleR lambdaSixFiveFiveThreeThreeH256
      lambdaSixFiveFiveThreeThreeH2Support256 r) :
    ∃ tag : Fin 3, ∃ p : Fin 16 → Fin 16,
      lambdaSixRelabelsTo
        (lambdaSixForcedDefect lambdaSixFiveFiveThreeThreeH2Support256 r)
        (lambdaSixFiveFiveThreeThreeDTarget tag) p := by
  have hrmem := lambdaSixFiveFiveThreeThreeRModels_complete r hr
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrmem
  let j : Fin 360 :=
    ⟨i.val, by
      simpa [lambdaSixFiveFiveThreeThreeRModels_length] using i.isLt⟩
  have hj : lambdaSixFiveFiveThreeThreeRModels.getD j.val 0 = r := by
    simpa [j] using hi
  let label := lambdaSixFiveFiveThreeThreeRModelLabels j
  refine ⟨label.1, label.2, ?_⟩
  rw [← hj]
  exact lambdaSixFiveFiveThreeThreeRModelLabel_correct j

end Erdos85
