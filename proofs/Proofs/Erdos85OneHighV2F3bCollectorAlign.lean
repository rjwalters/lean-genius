import Proofs.Erdos85OneHighV2Satisfaction

/-!
# Exact F3b 5×5 collector alignment for the v2 orbit formula

Mirrors the PURE `OneHighFamilyCollectedCommonsMatch` machinery for the
v2 unpaired common collector: the output variable array of
`oneHighFamilyV2F3bCollectVal` lists, in worker nested order, exactly
the IDs of the 25 `.common (min x z) (max x z)` atoms of the pair
blocks, each recorded in the final allocation state.
-/

namespace Erdos85

noncomputable section

/-- Old-ID preservation through the conditional partner-edge append. -/
theorem oneHighFamilyV2MaybeAppendEdgeVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (cond : Bool) (x w : Nat)
    {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (oneHighFamilyV2MaybeAppendEdgeVal R cond x w input).2.1.ids := by
  rcases input with ⟨ors, acc⟩
  unfold oneHighFamilyV2MaybeAppendEdgeVal
  cases cond with
  | false => simpa using hmem
  | true =>
      simpa [oneHighFamilyV2AppendEdgeVal] using
        (oneHighFamilyCollectAtomVal_old_mem R
          (.edge (min x w) (max x w)) hmem)

/-- Emission folds preserve the ID table. -/
theorem oneHighFamilyEmitFoldVal_ids
    (ors : Array Int) (c : Nat) (acc : OneHighFamilyValState) :
    (ors.foldl (fun acc lit =>
      (oneHighFamilyEmitVal [-lit, (c : Int)] acc).2) acc).1.ids =
      acc.1.ids := by
  rw [← Array.foldl_toList]
  induction ors.toList generalizing acc with
  | nil => rfl
  | cons lit ls ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rfl

/-- The v2 common finish pushes exactly the common atom's ID, records
its membership, and preserves old memberships. -/
theorem oneHighFamilyV2FinishCommonVal_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (cs ors : Array Int) (x z : Nat) (acc : OneHighFamilyValState) :
    let out := oneHighFamilyV2FinishCommonVal R cs ors x z acc
    ∃ c : Nat, out.1 = cs.push (c : Int) ∧
      ((.common (min x z) (max x z)), c) ∈ out.2.1.ids ∧
      ∀ {entry : OneHighFamilyAtom × Nat},
        entry ∈ acc.1.ids → entry ∈ out.2.1.ids := by
  unfold oneHighFamilyV2FinishCommonVal
  generalize hca : oneHighFamilyAtomIdVal R
    (.common (min x z) (max x z)) acc = out
  rcases out with ⟨c, accC⟩
  have hrC := oneHighFamilyAtomIdVal_result R
    (.common (min x z) (max x z)) acc.1 acc.2
  rw [hca] at hrC
  refine ⟨c, rfl, ?_, ?_⟩
  · show ((.common (min x z) (max x z)), c) ∈
      ((oneHighFamilyEmitVal (-(c : Int) :: ors.toList) accC).2 |>
        fun a => ors.foldl (fun acc lit =>
          (oneHighFamilyEmitVal [-lit, (c : Int)] acc).2) a).1.ids
    rw [oneHighFamilyEmitFoldVal_ids]
    exact hrC.1
  · intro entry hmem
    have hm := oneHighFamilyAtomIdVal_old_mem R
      (.common (min x z) (max x z)) acc.1 acc.2 hmem
    rw [hca] at hm
    show entry ∈
      ((oneHighFamilyEmitVal (-(c : Int) :: ors.toList) accC).2 |>
        fun a => ors.foldl (fun acc lit =>
          (oneHighFamilyEmitVal [-lit, (c : Int)] acc).2) a).1.ids
    rw [oneHighFamilyEmitFoldVal_ids]
    exact hm

/-- Old-ID preservation through one v2 unpaired common step. -/
theorem oneHighFamilyV2UnpairedCommonStepVal_old_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b x z : Nat)
    {input : Array Int × OneHighFamilyValState}
    {entry : OneHighFamilyAtom × Nat}
    (hmem : entry ∈ input.2.1.ids) :
    entry ∈ (oneHighFamilyV2UnpairedCommonStepVal R
      profile a b x z input).2.1.ids := by
  rcases input with ⟨cs, acc⟩
  unfold oneHighFamilyV2UnpairedCommonStepVal
  have hmid := oneHighFamilyCollectMidpointsVal_old_mem R x z
    (oneHighFamilyV2UnpairedMidpoints a b)
    (input := ((#[] : Array Int), acc)) hmem
  change entry ∈ (oneHighFamilyCollectMidpointsVal R x z
    (oneHighFamilyV2UnpairedMidpoints a b) acc).2.1.ids at hmid
  generalize hmids : oneHighFamilyCollectMidpointsVal R x z
    (oneHighFamilyV2UnpairedMidpoints a b) acc = midInput
  rw [hmids] at hmid
  have hx := oneHighFamilyV2MaybeAppendEdgeVal_old_mem R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z (input := midInput) hmid
  generalize hxo : oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z midInput = xInput
  rw [hxo] at hx
  have hz := oneHighFamilyV2MaybeAppendEdgeVal_old_mem R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) (input := xInput) hx
  generalize hzo : oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) xInput = zInput
  rw [hzo] at hz
  obtain ⟨c, hpush, hcmem, hold⟩ :=
    oneHighFamilyV2FinishCommonVal_mem R cs zInput.1 x z zInput.2
  show entry ∈ (oneHighFamilyV2FinishCommonVal R cs
    ((oneHighFamilyCollectMidpointsVal R x z
      (oneHighFamilyV2UnpairedMidpoints a b) acc) |>
        (fun m => oneHighFamilyV2MaybeAppendEdgeVal R
          (oneHighFamilyVertexMatched profile x)
          (oneHighFamilyV2PartnerVertex x) z m) |>
        (fun m => oneHighFamilyV2MaybeAppendEdgeVal R
          (oneHighFamilyVertexMatched profile z)
          x (oneHighFamilyV2PartnerVertex z) m)).1 x z
    ((oneHighFamilyCollectMidpointsVal R x z
      (oneHighFamilyV2UnpairedMidpoints a b) acc) |>
        (fun m => oneHighFamilyV2MaybeAppendEdgeVal R
          (oneHighFamilyVertexMatched profile x)
          (oneHighFamilyV2PartnerVertex x) z m) |>
        (fun m => oneHighFamilyV2MaybeAppendEdgeVal R
          (oneHighFamilyVertexMatched profile z)
          x (oneHighFamilyV2PartnerVertex z) m)).2).2.1.ids
  rw [hmids]
  simp only [hxo, hzo]
  exact hold hz

/-- One v2 unpaired common step appends the pair `(x, z)` to a
collected-commons match. -/
noncomputable def oneHighFamilyV2CollectedCommonsMatch_push
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {profile a b x z : Nat} {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    OneHighFamilyCollectedCommonsMatch (pairs ++ [(x, z)])
      (oneHighFamilyV2UnpairedCommonStepVal R profile a b x z input) := by
  rcases input with ⟨cs, acc⟩
  unfold oneHighFamilyV2UnpairedCommonStepVal
  generalize hmids : (oneHighFamilyV2UnpairedMidpoints a b).foldl
    (fun input w => oneHighFamilyMidpointTseitinStepVal R x z w input)
    (#[], acc) = midInput
  generalize hxo : oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z midInput = xInput
  generalize hzo : oneHighFamilyV2MaybeAppendEdgeVal R
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) xInput = zInput
  let ca : OneHighFamilyAtom := .common (min x z) (max x z)
  generalize hca : oneHighFamilyAtomIdVal R ca zInput.2 = out
  rcases out with ⟨c, accC⟩
  have hrC := oneHighFamilyAtomIdVal_result R ca zInput.2.1 zInput.2.2
  rw [hca] at hrC
  have hfinalIds :
      (oneHighFamilyV2FinishCommonVal R cs zInput.1 x z zInput.2).2.1.ids =
        accC.1.ids := by
    simp only [oneHighFamilyV2FinishCommonVal, ca, hca]
    rw [oneHighFamilyEmitFoldVal_ids]
    rfl
  have hold : List.Forall₂ (fun p id =>
      ((.common (min p.1 p.2) (max p.1 p.2)), id) ∈
        (oneHighFamilyV2FinishCommonVal R cs zInput.1 x z
          zInput.2).2.1.ids) pairs h.ids := by
    apply h.aligned.imp
    intro p id hmem
    have hm := oneHighFamilyCollectMidpointsVal_old_mem R x z
      (oneHighFamilyV2UnpairedMidpoints a b)
      (input := ((#[] : Array Int), acc)) hmem
    change ((.common (min p.1 p.2) (max p.1 p.2)), id) ∈
      (oneHighFamilyCollectMidpointsVal R x z
        (oneHighFamilyV2UnpairedMidpoints a b) acc).2.1.ids at hm
    have hmids' : oneHighFamilyCollectMidpointsVal R x z
        (oneHighFamilyV2UnpairedMidpoints a b) acc = midInput := by
      rw [← hmids]; rfl
    rw [hmids'] at hm
    have hx := oneHighFamilyV2MaybeAppendEdgeVal_old_mem R
      (oneHighFamilyVertexMatched profile x)
      (oneHighFamilyV2PartnerVertex x) z (input := midInput) hm
    rw [hxo] at hx
    have hz := oneHighFamilyV2MaybeAppendEdgeVal_old_mem R
      (oneHighFamilyVertexMatched profile z)
      x (oneHighFamilyV2PartnerVertex z) (input := xInput) hx
    rw [hzo] at hz
    have hcOld := oneHighFamilyAtomIdVal_old_mem R ca
      zInput.2.1 zInput.2.2 hz
    rw [hca] at hcOld
    rw [hfinalIds]
    exact hcOld
  simp only [hmids, hxo, hzo]
  refine ⟨h.ids ++ [c], ?_, ?_⟩
  · simp only [oneHighFamilyV2FinishCommonVal, ca, hca]
    rw [Array.toList_push, h.vars_eq]
    simp
  · apply listForall₂_append_singleton hold
    rw [hfinalIds]
    exact hrC.1

/-- Inner 5-vertex fold of the v2 collector. -/
noncomputable def oneHighFamilyV2CollectCommonsInner_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b x : Nat) (zs : List Nat) {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    OneHighFamilyCollectedCommonsMatch
      (zs.foldl (fun pairs z => pairs ++ [(x, z)]) pairs)
      (zs.foldl (fun input z =>
        oneHighFamilyV2UnpairedCommonStepVal R profile a b x z input)
        input) := by
  induction zs generalizing pairs input with
  | nil => exact h
  | cons z zs ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyV2CollectedCommonsMatch_push R h)

/-- Outer fold of the v2 collector. -/
noncomputable def oneHighFamilyV2CollectCommonsOuter_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile a b : Nat) (xs : List Nat) {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    OneHighFamilyCollectedCommonsMatch
      (xs.foldl (fun pairs x =>
        (oneHighFamilyBlockVertices b).foldl
          (fun pairs z => pairs ++ [(x, z)]) pairs) pairs)
      (xs.foldl (fun input x =>
        (oneHighFamilyBlockVertices b).foldl (fun input z =>
          oneHighFamilyV2UnpairedCommonStepVal R profile a b x z input)
          input) input) := by
  induction xs generalizing pairs input with
  | nil => exact h
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (oneHighFamilyV2CollectCommonsInner_match R profile a b x
        (oneHighFamilyBlockVertices b) h)

/-- Full 5×5 alignment: the v2 F3b collector output lists, in worker
order, exactly the common-pair atom IDs of the pair blocks. -/
noncomputable def oneHighFamilyV2F3bCollectVal_match
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (pair : Nat × Nat) (acc : OneHighFamilyValState) :
    OneHighFamilyCollectedCommonsMatch
      (oneHighFamilyCommonPairs pair.1 pair.2)
      (oneHighFamilyV2F3bCollectVal R profile pair acc) :=
  oneHighFamilyV2CollectCommonsOuter_match R profile pair.1 pair.2
    (oneHighFamilyBlockVertices pair.1)
    (oneHighFamilyCollectedCommonsMatch_empty acc)

noncomputable def oneHighFamilyCollectedCommonsMatch_toAtomsMatch
    {pairs : List (Nat × Nat)}
    {input : Array Int × OneHighFamilyValState}
    (h : OneHighFamilyCollectedCommonsMatch pairs input) :
    OneHighFamilyCollectedAtomsMatch
      (pairs.map (fun p =>
        .common (min p.1 p.2) (max p.1 p.2))) input := {
  ids := h.ids
  vars_eq := h.vars_eq
  aligned := by
    simpa only [List.forall₂_map_left_iff] using h.aligned }

theorem oneHighFamilyV2F3bCollectVal_inputAccumSound
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (profile : Nat) (pair : Nat × Nat) {acc : OneHighFamilyValState}
    (hs : OneHighFamilySemanticSound R
      (oneHighFamilyV2F3bCollectVal R profile pair acc).2) :
    OneHighFamilyInputAccumSound R
      (oneHighFamilyV2F3bCollectVal R profile pair acc) := by
  exact oneHighFamilyCollectedAtomsMatch_sound R
    (oneHighFamilyCollectedCommonsMatch_toAtomsMatch
      (oneHighFamilyV2F3bCollectVal_match R profile pair acc)) hs

end

end Erdos85
