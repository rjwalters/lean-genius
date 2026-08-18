import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncoding

/-! # Structural lemmas for the outside-C pair generator -/

namespace Erdos85

/-- Both entries of a pair emitted by `listPairs` came from the source
list. -/
theorem mem_listPairs_components {xs : List α} {p : α × α}
    (hp : p ∈ listPairs xs) : p.1 ∈ xs ∧ p.2 ∈ xs := by
  induction xs with
  | nil => simp [listPairs] at hp
  | cons x xs ih =>
      simp only [listPairs, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨y, hy, rfl⟩ | hp
      · exact ⟨by simp, by simp [hy]⟩
      · obtain ⟨hfst, hsnd⟩ := ih hp
        exact ⟨by simp [hfst], by simp [hsnd]⟩

/-- A pair emitted from a noduplicate list has distinct entries. -/
theorem mem_listPairs_ne {xs : List α} (hxs : xs.Nodup)
    {p : α × α} (hp : p ∈ listPairs xs) : p.1 ≠ p.2 := by
  induction xs with
  | nil => simp [listPairs] at hp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [listPairs, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨y, hy, rfl⟩ | hp
      · intro hxy
        have hxy' : x = y := by simpa using hxy
        exact hxs.1 (hxy' ▸ hy)
      · exact ih hxs.2 hp

end Erdos85
