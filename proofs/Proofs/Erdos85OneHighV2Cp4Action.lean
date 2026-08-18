import Proofs.Erdos85OneHighV2ProfileSymmetry

/-!
# CP4 stabilizer action: admissibility invariance and canonical reps

Builds on `OneHighProfilePerm` (`Erdos85OneHighV2ProfileSymmetry`):
invariance of `OneHighFamilyV2Admissible` under `permuteTable`, the
induced action on relevant pairs and finite tables, and existence of a
canonical (encode-minimal) representative in every stabilizer orbit of
a finite table.

Follow-on socket (not here): semantic CP4 transfer of
`OneHighFamilyV2CheckedUnsat` across the action, which would let one
certificate discharge its whole orbit.
-/

namespace Erdos85

/-- Membership transport for the erased row domain under `σ⁻¹`. -/
theorem oneHighProfilePerm_mem_row_domain_iff {profile : Nat}
    (σ : OneHighProfilePerm profile) (c j : Fin 8) :
    j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)) ↔
      σ.1.symm j ∈ ((Finset.univ.erase (σ.1.symm c)).erase
        (oneHighStandardMate (σ.1.symm c))) := by
  have hmateSymm : ∀ i, σ.1.symm (oneHighStandardMate i) =
      oneHighStandardMate (σ.1.symm i) := σ.inv.2.1
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hjm, hjc⟩
    refine ⟨?_, fun h => hjc (σ.1.symm.injective h)⟩
    intro h
    apply hjm
    have := congrArg σ.1 h
    rwa [Equiv.apply_symm_apply, ← hmateSymm c, Equiv.apply_symm_apply]
      at this
  · rintro ⟨hjm, hjc⟩
    refine ⟨?_, fun h => hjc (by rw [h])⟩
    intro h
    apply hjm
    rw [h, hmateSymm c]

/-- Admissibility is invariant under the CP4 profile stabilizer. -/
theorem OneHighFamilyV2Admissible.permute {profile : Nat}
    {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table)
    (σ : OneHighProfilePerm profile) :
    OneHighFamilyV2Admissible profile (σ.permuteTable table) := by
  have hmateSymm : ∀ i, σ.1.symm (oneHighStandardMate i) =
      oneHighStandardMate (σ.1.symm i) := σ.inv.2.1
  have hedgeSymm : ∀ i, oneHighFamilyInternalEdges profile (σ.1.symm i) =
      oneHighFamilyInternalEdges profile i := σ.inv.2.2
  constructor
  · intro c j hjc hjm
    rw [OneHighProfilePerm.permuteTable_apply,
      OneHighProfilePerm.permuteTable_apply]
    apply h.symm
    · exact fun hh => hjc (σ.1.symm.injective hh)
    · intro hh
      apply hjm
      have := congrArg σ.1 hh
      rwa [Equiv.apply_symm_apply, ← hmateSymm c, Equiv.apply_symm_apply]
        at this
  · intro c
    have hsum :
        (∑ j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)),
          σ.permuteTable table c.val j.val) =
        ∑ u ∈ ((Finset.univ.erase (σ.1.symm c)).erase
            (oneHighStandardMate (σ.1.symm c))),
          table (σ.1.symm c).val u.val := by
      refine Finset.sum_equiv (σ.1.symm : Equiv.Perm (Fin 8))
        (fun j => oneHighProfilePerm_mem_row_domain_iff σ c j)
        (fun j _ => ?_)
      rw [OneHighProfilePerm.permuteTable_apply]
    rw [hsum, h.row_sum (σ.1.symm c), hedgeSymm c]

/-! ## Induced action on relevant pairs and finite tables -/

/-- Sorted image of a relevant pair under `π`.  For mate-preserving `π`
one of the two sorted branches always applies; the fallback keeps the
map total. -/
def oneHighRelevantPairMap (π : Equiv.Perm (Fin 8))
    (pair : OneHighRelevantPair) : OneHighRelevantPair :=
  if h : π pair.1.1 < π pair.1.2 ∧
      π pair.1.2 ≠ oneHighStandardMate (π pair.1.1) then
    ⟨(π pair.1.1, π pair.1.2), h.1, h.2⟩
  else if h' : π pair.1.2 < π pair.1.1 ∧
      π pair.1.1 ≠ oneHighStandardMate (π pair.1.2) then
    ⟨(π pair.1.2, π pair.1.1), h'.1, h'.2⟩
  else pair

/-- For mate-preserving `π` the fallback branch is unreachable: the
image of a relevant pair is again relevant, in one of its two sorted
orders. -/
theorem oneHighRelevantPairMap_spec {π : Equiv.Perm (Fin 8)}
    (hmate : ∀ i, π (oneHighStandardMate i) = oneHighStandardMate (π i))
    (pair : OneHighRelevantPair) :
    (oneHighRelevantPairMap π pair).1 = (π pair.1.1, π pair.1.2) ∨
      (oneHighRelevantPairMap π pair).1 = (π pair.1.2, π pair.1.1) := by
  obtain ⟨⟨c, j⟩, hlt, hnm⟩ := pair
  have hne : π c ≠ π j := fun h => absurd (π.injective h) (Fin.ne_of_lt hlt)
  have hnm₁ : π j ≠ oneHighStandardMate (π c) := by
    intro h
    apply hnm
    apply π.injective
    rw [hmate c]
    exact h
  have hnm₂ : π c ≠ oneHighStandardMate (π j) := by
    intro h
    apply hnm₁
    rw [h]
    exact (oneHighStandardMate_involutive (π j)).symm
  unfold oneHighRelevantPairMap
  rcases lt_or_gt_of_ne hne with hcj | hjc
  · rw [dif_pos ⟨hcj, hnm₁⟩]
    exact Or.inl rfl
  · rw [dif_neg (by rintro ⟨hh, -⟩; exact absurd hh (asymm hjc)),
      dif_pos ⟨hjc, hnm₂⟩]
    exact Or.inr rfl

/-- Induced action on finite tables: read the original at the sorted
`π⁻¹`-image pair. -/
def oneHighFinitePermute (π : Equiv.Perm (Fin 8))
    (w : OneHighFiniteMissTable) : OneHighFiniteMissTable := fun pair =>
  w (oneHighRelevantPairMap π⁻¹ pair)

/-! ## Canonical representatives -/

/-- Injective numeric encoding of finite tables, fixing the canonical
order used to pick orbit representatives. -/
noncomputable def oneHighCp4Encode : OneHighFiniteMissTable → Nat :=
  fun w => (Fintype.equivFin OneHighFiniteMissTable w).val

theorem oneHighCp4Encode_injective :
    Function.Injective oneHighCp4Encode := by
  intro w u h
  exact (Fintype.equivFin OneHighFiniteMissTable).injective (Fin.ext h)

/-- Every finite table has an encode-minimal image under the CP4 profile
stabilizer: a canonical representative of its constrained orbit. -/
theorem oneHighCp4_exists_canonical (profile : Nat)
    (w : OneHighFiniteMissTable) :
    ∃ σ : OneHighProfilePerm profile,
      ∀ τ : OneHighProfilePerm profile,
        oneHighCp4Encode (oneHighFinitePermute σ.1 w) ≤
          oneHighCp4Encode (oneHighFinitePermute τ.1 w) := by
  classical
  set values := (Finset.univ : Finset (OneHighProfilePerm profile)).image
    (fun σ => oneHighCp4Encode (oneHighFinitePermute σ.1 w)) with hvalues
  have hne : values.Nonempty :=
    ⟨_, Finset.mem_image_of_mem _
      (Finset.mem_univ (oneHighProfilePermId profile))⟩
  obtain ⟨σ, _, hval⟩ := Finset.mem_image.mp (values.min'_mem hne)
  refine ⟨σ, fun τ => ?_⟩
  rw [hval]
  exact values.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ τ))

end Erdos85
