-- Scratch repair-validation for the two map-lemma failures in the
-- d=16 s=0 dispatch (gate RED at 81e1fe8ef4, errors [3]/[4]).
-- Untracked; proofs to be relayed to codex once green.
import Mathlib

namespace ScratchMapFix

theorem used_reducedOrder_mem_of_map_eq
    {α : Type*} [DecidableEq α] (E : Finset α) (K : α → ℕ)
    (L : List ℕ) (hmap : E.val.map K = (L : Multiset ℕ))
    {x : α} (hx : x ∈ E) : K x ∈ L := by
  have hm : K x ∈ (L : Multiset ℕ) := by
    rw [← hmap]
    exact Multiset.mem_map_of_mem K hx
  exact Multiset.mem_coe.mp hm

theorem used_reducedOrder_count_of_map_eq
    {α : Type*} [DecidableEq α] (E : Finset α) (K : α → ℕ)
    (L : List ℕ) (hmap : E.val.map K = (L : Multiset ℕ)) (k : ℕ) :
    (E.filter (fun x => K x = k)).card = L.count k := by
  have hc := congrArg (Multiset.count k) hmap
  rw [Multiset.count_map] at hc
  calc (E.filter (fun x => K x = k)).card
      = (Multiset.filter (fun x => K x = k) E.val).card := by
        rw [Finset.card_def, Finset.filter_val]
    _ = (Multiset.filter (fun a => k = K a) E.val).card := by
        rw [Multiset.filter_congr (fun x _ => by
          constructor <;> exact fun h => h.symm)]
    _ = Multiset.count k (L : Multiset ℕ) := hc
    _ = L.count k := by rw [Multiset.coe_count]

end ScratchMapFix
