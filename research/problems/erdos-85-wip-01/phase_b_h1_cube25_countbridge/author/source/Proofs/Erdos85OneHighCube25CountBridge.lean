import Proofs.Erdos85SequentialCounter
import Proofs.Erdos85SequentialCounterReverse
import Proofs.Erdos85OneHighCube25CnfCover

/-! Reindexing the full counter input count into its six five-item blocks.
The equivalence is explicit: callers must supply the actual input/block map. -/

namespace Erdos85

theorem seqPrefixTrue_eq_sum_fin {n : Nat} (x : Fin n → Bool) :
    seqPrefixTrue x n = ∑ i : Fin n, if x i then 1 else 0 := by
  rw [Finset.sum_fin_eq_sum_range]
  simp only [seqPrefixTrue, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  simp [hin]

theorem seqPrefixTrue_eq_block_counts
    (x : Fin 30 → Bool) (blocks : Fin 6 × Fin 5 ≃ Fin 30) :
    seqPrefixTrue x 30 =
      ∑ b : Fin 6, (Finset.univ.filter (fun i => x (blocks (b, i)) = true)).card := by
  rw [seqPrefixTrue_eq_sum_fin]
  rw [← Equiv.sum_comp blocks]
  rw [Fintype.sum_prod_type]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Two counter lower bounds give the 25-way cover after reindexing into
blocks whose negative pair clauses forbid simultaneous true inputs. -/
theorem oneHighCube25_cover_of_prefix_bounds
    (left right : Fin 30 → Bool)
    (left_blocks right_blocks : Fin 6 × Fin 5 ≃ Fin 30)
    (left_pairs : ∀ b i j, i ≠ j →
      left (left_blocks (b, i)) = false ∨ left (left_blocks (b, j)) = false)
    (right_pairs : ∀ b i j, i ≠ j →
      right (right_blocks (b, i)) = false ∨ right (right_blocks (b, j)) = false)
    (left_lower : 6 ≤ seqPrefixTrue left 30)
    (right_lower : 6 ≤ seqPrefixTrue right 30)
    (left_block right_block : Fin 6) :
    ∃ i j : Fin 5, left (left_blocks (left_block, i)) = true ∧
      right (right_blocks (right_block, j)) = true := by
  apply oneHighCube25_assignment_cover
    (fun b i => left (left_blocks (b, i)) = true)
    (fun b i => right (right_blocks (b, i)) = true)
  · intro b i j hi hj
    by_contra different
    rcases left_pairs b i j different with h | h <;> simp_all
  · intro b i j hi hj
    by_contra different
    rcases right_pairs b i j different with h | h <;> simp_all
  · rwa [← seqPrefixTrue_eq_block_counts]
  · rwa [← seqPrefixTrue_eq_block_counts]

/-- Compose arbitrary-auxiliary reverse-counter semantics with the block
occupancy proof. The actual CNF must still supply these schemas, pair clauses,
and the stated bijections between inputs and blocks. -/
theorem oneHighCube25_cover_of_counter_schemas
    (left right : Fin 30 → Bool)
    (left_blocks right_blocks : Fin 6 × Fin 5 ≃ Fin 30)
    (left_aux right_aux : Nat → Nat → Prop)
    (left_counter : SeqCounterReverseSchemas 30 24
      (fun i => if hi : i < 30 then seqNeg left ⟨i, hi⟩ = true else False) left_aux)
    (right_counter : SeqCounterReverseSchemas 30 24
      (fun i => if hi : i < 30 then seqNeg right ⟨i, hi⟩ = true else False) right_aux)
    (left_pairs : ∀ b i j, i ≠ j →
      left (left_blocks (b, i)) = false ∨ left (left_blocks (b, j)) = false)
    (right_pairs : ∀ b i j, i ≠ j →
      right (right_blocks (b, i)) = false ∨ right (right_blocks (b, j)) = false)
    (left_block right_block : Fin 6) :
    ∃ i j : Fin 5, left (left_blocks (left_block, i)) = true ∧
      right (right_blocks (right_block, j)) = true := by
  apply oneHighCube25_cover_of_prefix_bounds left right left_blocks right_blocks
    left_pairs right_pairs
  · exact seqCounterReverse_complement_lower_bound left left_counter (by decide)
  · exact seqCounterReverse_complement_lower_bound right right_counter (by decide)

end Erdos85

#print axioms Erdos85.seqPrefixTrue_eq_sum_fin
#print axioms Erdos85.seqPrefixTrue_eq_block_counts
#print axioms Erdos85.oneHighCube25_cover_of_prefix_bounds
#print axioms Erdos85.oneHighCube25_cover_of_counter_schemas
