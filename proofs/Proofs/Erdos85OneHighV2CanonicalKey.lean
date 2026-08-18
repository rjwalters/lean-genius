import Proofs.Erdos85OneHighV2Cp4Action
import Proofs.Erdos85OneHighV2EnumCompleteness

/-!
# Computable canonical keys for the CP4 profile stabilizer

Computable Nat-table action and base-5 encoding key, and the canonical
(minimal) key over the profile stabilizer, with selection
specifications and the orientation glue to
`OneHighProfilePerm.permuteTable`.  Interface for the native inventory
comparison:

* `oneHighNatKey w` — base-5 digit key along `oneHighRelevantPairList`;
  injective on `< 5`-bounded tables.
* `oneHighNatPermute π w` — Nat-table action, reading `w` at the sorted
  `π⁻¹`-image pair (same orientation as `permuteTable`).
* `oneHighCanonicalKey profile w` — minimum of
  `oneHighNatKey (oneHighNatPermute σ.1 w)` over all
  `σ : OneHighProfilePerm profile`, computable via `Finset.inf'`.
* `oneHighCanonicalKey_exists` / `oneHighCanonicalKey_le` — the minimum
  is attained and bounds every stabilizer image.
* `oneHighNatPermute_natRestrict` — for admissible tables the Nat
  action matches the total-table action through `oneHighNatRestrict`.
-/

namespace Erdos85

/-- Base-5 digit key along the fixed relevant-pair order. -/
def oneHighNatKey (w : OneHighRelevantPair → Nat) : Nat :=
  oneHighRelevantPairList.foldl (fun acc e => acc * 5 + w e) 0

/-- Computable Nat-table stabilizer action. -/
def oneHighNatPermute (π : Equiv.Perm (Fin 8))
    (w : OneHighRelevantPair → Nat) : OneHighRelevantPair → Nat :=
  fun pair => w (oneHighRelevantPairMap π⁻¹ pair)

/-- The identity acts trivially. -/
theorem oneHighNatPermute_one (w : OneHighRelevantPair → Nat) :
    oneHighNatPermute 1 w = w := by
  funext pair
  unfold oneHighNatPermute oneHighRelevantPairMap
  rw [inv_one]
  rcases pair with ⟨⟨c, j⟩, hlt, hnm⟩
  simp [Equiv.Perm.one_apply, hlt, hnm]

/-- Minimal stabilizer-image key: the canonical representative key of
the constrained orbit of `w`. -/
def oneHighCanonicalKey (profile : Nat)
    (w : OneHighRelevantPair → Nat) : Nat :=
  (Finset.univ : Finset (OneHighProfilePerm profile)).inf'
    ⟨oneHighProfilePermId profile, Finset.mem_univ _⟩
    (fun σ => oneHighNatKey (oneHighNatPermute σ.1 w))

/-- The canonical key is attained by a stabilizer element. -/
theorem oneHighCanonicalKey_exists (profile : Nat)
    (w : OneHighRelevantPair → Nat) :
    ∃ σ : OneHighProfilePerm profile,
      oneHighCanonicalKey profile w =
        oneHighNatKey (oneHighNatPermute σ.1 w) := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (OneHighProfilePerm profile)))
    ⟨oneHighProfilePermId profile, Finset.mem_univ _⟩
    (fun σ => oneHighNatKey (oneHighNatPermute σ.1 w))
  exact ⟨σ, hσ⟩

/-- The canonical key bounds every stabilizer image key. -/
theorem oneHighCanonicalKey_le (profile : Nat)
    (w : OneHighRelevantPair → Nat)
    (σ : OneHighProfilePerm profile) :
    oneHighCanonicalKey profile w ≤
      oneHighNatKey (oneHighNatPermute σ.1 w) :=
  Finset.inf'_le _ (Finset.mem_univ σ)

/-- Orientation glue: on admissible total tables the Nat action agrees
with `permuteTable` through the sorted restriction. -/
theorem oneHighNatPermute_natRestrict {profile : Nat}
    {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table)
    (σ : OneHighProfilePerm profile) :
    oneHighNatPermute σ.1 (oneHighNatRestrict table) =
      oneHighNatRestrict (σ.permuteTable table) := by
  funext pair
  have happ : ∀ x : Fin 8, σ.1 (σ.1⁻¹ x) = x := fun x =>
    σ.1.apply_symm_apply x
  have hmateInv : ∀ i, σ.1⁻¹ (oneHighStandardMate i) =
      oneHighStandardMate (σ.1⁻¹ i) := σ.inv.2.1
  unfold oneHighNatPermute oneHighNatRestrict
  have hperm : σ.permuteTable table pair.1.1.val pair.1.2.val =
      table (σ.1.symm pair.1.1).val (σ.1.symm pair.1.2).val :=
    OneHighProfilePerm.permuteTable_apply σ table pair.1.1 pair.1.2
  rw [hperm]
  rcases oneHighRelevantPairMap_spec hmateInv pair with hspec | hspec
  · rw [hspec]
    rfl
  · rw [hspec]
    have hnec : σ.1⁻¹ pair.1.2 ≠ σ.1⁻¹ pair.1.1 :=
      fun hh => absurd (σ.1⁻¹.injective hh)
        (Fin.ne_of_lt pair.2.1).symm
    have hnem : σ.1⁻¹ pair.1.2 ≠
        oneHighStandardMate (σ.1⁻¹ pair.1.1) := by
      intro hh
      apply pair.2.2
      have hc := congrArg σ.1 hh
      rwa [happ, ← hmateInv, happ] at hc
    exact (h.symm (σ.1⁻¹ pair.1.1) (σ.1⁻¹ pair.1.2) hnec hnem).symm

/-! ## Key injectivity on bounded tables -/

theorem oneHighNatKey_fold_lower (l : List OneHighRelevantPair)
    (w : OneHighRelevantPair → Nat) :
    ∀ acc, acc * 5 ^ l.length ≤
      l.foldl (fun acc e => acc * 5 + w e) acc := by
  induction l with
  | nil => intro acc; simp
  | cons e rest ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons]
      calc acc * 5 ^ (rest.length + 1) = (acc * 5) * 5 ^ rest.length := by
            rw [pow_succ]; ring
        _ ≤ (acc * 5 + w e) * 5 ^ rest.length :=
            Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        _ ≤ rest.foldl (fun acc e => acc * 5 + w e) (acc * 5 + w e) :=
            ih _

theorem oneHighNatKey_fold_upper (l : List OneHighRelevantPair)
    (w : OneHighRelevantPair → Nat) (hw : ∀ e ∈ l, w e < 5) :
    ∀ acc, l.foldl (fun acc e => acc * 5 + w e) acc <
      (acc + 1) * 5 ^ l.length := by
  induction l with
  | nil => intro acc; simpa using Nat.lt_succ_self acc
  | cons e rest ih =>
      intro acc
      have hbound := hw e (List.mem_cons_self ..)
      simp only [List.foldl_cons, List.length_cons]
      calc rest.foldl (fun acc e => acc * 5 + w e) (acc * 5 + w e) <
            (acc * 5 + w e + 1) * 5 ^ rest.length :=
            ih (fun e' he' => hw e' (List.mem_cons_of_mem e he')) _
        _ ≤ ((acc + 1) * 5) * 5 ^ rest.length :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (acc + 1) * 5 ^ (rest.length + 1) := by
            rw [pow_succ]; ring

/-- Equal bounded folds force equal accumulators. -/
theorem oneHighNatKey_fold_acc_inj (l : List OneHighRelevantPair)
    (w u : OneHighRelevantPair → Nat)
    (hw : ∀ e ∈ l, w e < 5) (hu : ∀ e ∈ l, u e < 5)
    (acc₁ acc₂ : Nat)
    (hfold : l.foldl (fun acc e => acc * 5 + w e) acc₁ =
      l.foldl (fun acc e => acc * 5 + u e) acc₂) :
    acc₁ = acc₂ := by
  by_contra hne
  rcases Nat.lt_or_ge acc₁ acc₂ with hlt | hge
  · have h₁ := oneHighNatKey_fold_upper l w hw acc₁
    have h₂ := oneHighNatKey_fold_lower l u acc₂
    have hle : (acc₁ + 1) * 5 ^ l.length ≤ acc₂ * 5 ^ l.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have hlt : acc₂ < acc₁ := by omega
    have h₁ := oneHighNatKey_fold_upper l u hu acc₂
    have h₂ := oneHighNatKey_fold_lower l w acc₁
    have hle : (acc₂ + 1) * 5 ^ l.length ≤ acc₁ * 5 ^ l.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- Equal bounded folds from equal accumulators force equal digits. -/
theorem oneHighNatKey_fold_inj (l : List OneHighRelevantPair)
    (w u : OneHighRelevantPair → Nat)
    (hw : ∀ e ∈ l, w e < 5) (hu : ∀ e ∈ l, u e < 5) :
    ∀ acc,
      l.foldl (fun acc e => acc * 5 + w e) acc =
        l.foldl (fun acc e => acc * 5 + u e) acc →
      ∀ e ∈ l, w e = u e := by
  induction l with
  | nil => intro _ _ e he; exact absurd he (List.not_mem_nil)
  | cons e rest ih =>
      intro acc hfold e' he'
      simp only [List.foldl_cons] at hfold
      have hwr := fun e'' he'' => hw e'' (List.mem_cons_of_mem e he'')
      have hur := fun e'' he'' => hu e'' (List.mem_cons_of_mem e he'')
      have hacc : acc * 5 + w e = acc * 5 + u e :=
        oneHighNatKey_fold_acc_inj rest w u hwr hur _ _ hfold
      have hwu : w e = u e := by omega
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hwu
      · exact ih hwr hur (acc * 5 + u e)
          (by rw [hacc] at hfold; exact hfold) e' he'

/-- On value-bounded tables the base-5 key is injective. -/
theorem oneHighNatKey_inj {w u : OneHighRelevantPair → Nat}
    (hw : ∀ e, w e < 5) (hu : ∀ e, u e < 5)
    (hkey : oneHighNatKey w = oneHighNatKey u) : w = u := by
  funext e
  exact oneHighNatKey_fold_inj oneHighRelevantPairList w u
    (fun e' _ => hw e') (fun e' _ => hu e') 0 hkey e
    (oneHighRelevantPairList_complete e)

end Erdos85
