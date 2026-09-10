import Mathlib

namespace Erdos85

/-- Boolean depth-first existence search with a prefix gate and a terminal test. -/
def finiteRowDFS {m : ℕ} {α : Type} (domain : Fin m → List α)
    (keep : ℕ → (Fin m → α) → Bool) (accept : (Fin m → α) → Bool) :
    ℕ → ℕ → (Fin m → α) → Bool
  | 0, _, rows => accept rows
  | fuel + 1, k, rows => if h : k < m then
      (domain ⟨k, h⟩).any fun row =>
        let next := Function.update rows ⟨k, h⟩ row
        keep (k + 1) next && finiteRowDFS domain keep accept fuel (k + 1) next
    else false

def finiteRowPrefix {m : ℕ} {α : Type} (base target : Fin m → α) (k : ℕ) : Fin m → α :=
  fun i => if i.val < k then target i else base i

private theorem finiteRowPrefix_update {m : ℕ} {α : Type}
    (base target : Fin m → α) (k : ℕ) (hk : k < m) :
    Function.update (finiteRowPrefix base target k) ⟨k, hk⟩ (target ⟨k, hk⟩) =
      finiteRowPrefix base target (k + 1) := by
  funext i
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    simp [finiteRowPrefix]
  · have hne : i.val ≠ k := fun h => hi (Fin.ext h)
    have he : (i.val < k + 1) ↔ i.val < k := by omega
    simp [Function.update_of_ne hi, finiteRowPrefix, he]

/-- Any witness whose prefixes pass the gate is found by the Boolean search. -/
theorem finiteRowDFS_witness {m : ℕ} {α : Type}
    (domain : Fin m → List α) (keep : ℕ → (Fin m → α) → Bool)
    (accept : (Fin m → α) → Bool) (base target : Fin m → α)
    (hdom : ∀ i, target i ∈ domain i)
    (hkeep : ∀ k, k ≤ m → keep k (finiteRowPrefix base target k) = true)
    (haccept : accept target = true) :
    finiteRowDFS domain keep accept m 0 base = true := by
  have aux : ∀ fuel k, k + fuel = m →
      finiteRowDFS domain keep accept fuel k (finiteRowPrefix base target k) = true := by
    intro fuel
    induction fuel with
    | zero =>
      intro k hk
      have hkm : k = m := by omega
      subst k
      have he : finiteRowPrefix base target m = target := by
        funext i
        exact if_pos i.isLt
      simpa only [finiteRowDFS, he] using haccept
    | succ fuel ih =>
      intro k hk
      have hkm : k < m := by omega
      rw [finiteRowDFS, dif_pos hkm]
      apply List.any_eq_true.mpr
      refine ⟨target ⟨k, hkm⟩, hdom _, ?_⟩
      dsimp only
      rw [finiteRowPrefix_update]
      simp only [Bool.and_eq_true]
      exact ⟨hkeep (k + 1) (by omega), ih (k + 1) (by omega)⟩
  have h := aux m 0 (by omega)
  have he : finiteRowPrefix base target 0 = base := by
    funext i
    simp only [finiteRowPrefix, Nat.not_lt_zero, if_false]
  simpa only [he] using h

end Erdos85
#print axioms Erdos85.finiteRowDFS_witness
