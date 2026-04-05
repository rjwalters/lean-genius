/-
  Aristotle targets for erdos-1012-oq-03 (Directed Hamiltonian Threshold)
  Routine supporting lemmas for automated proof search.
  See Erdos1012OQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjectures (ghouila_houri, directed_hamiltonian_threshold)
  - A known combinatorial counting result with a clear proof sketch

  Main target: perm_arc_bad_card_le — bound on permutations with a given consecutive pair

  Proof strategy:
  - For each position i ∈ Fin n (n choices), fix σ(i) = a, σ((i+1)%n) = b.
  - The n-2 remaining values can be placed freely: (n-2)! permutations each.
  - Positions are disjoint (σ injective → σ(i)=a uniquely determines i).
  - Total count ≤ n * (n-2)! by summing over all n positions.
-/
import Mathlib

/-
Key combinatorial bound: the number of permutations σ : Perm(Fin n) such that
a directed arc (a → b) appears at some consecutive position in the cycle given by σ
is at most n * (n-2)!.
Proof sketch: for each position i (n choices), fixing σ(i)=a, σ((i+1)%n)=b leaves
(n-2)! permutations of the remaining n-2 values. Positions are disjoint (σ injective).
-/
theorem perm_arc_bad_card_le {n : ℕ} (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ i : Fin n, σ i = a ∧
        σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩ = b)).card ≤
    n * (n - 2).factorial := by
  have h_perm : Finset.filter (fun σ : Equiv.Perm (Fin n) => ∃ i : Fin n, σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ ⊆ Finset.biUnion Finset.univ (fun i : Fin n => Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) := by
    aesop_cat;
  -- Each set in the union has cardinality (n-2)! because fixing two values of a permutation leaves (n-2)! choices.
  have h_card : ∀ i : Fin n, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) ≤ (n - 2).factorial := by
    intro i
    have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) ≤ Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) / (n - 1) := by
      have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) = Finset.card (Finset.biUnion (Finset.univ.erase a) (fun b => Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ)) := by
        congr with σ;
        simp +decide [ Finset.mem_biUnion ];
        intro hi hj; have := σ.injective ( hj.trans hi.symm ) ; simp_all +decide [ Fin.ext_iff, Nat.mod_eq_of_lt ] ;
        have := Nat.mod_add_div ( i + 1 ) n; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        nlinarith [ show ( i : ℕ ) < n from i.2, show ( i + 1 : ℕ ) / n = 0 from by nlinarith [ show ( i : ℕ ) < n from i.2 ] ];
      rw [ h_card, Finset.card_biUnion ];
      · rw [ Nat.le_div_iff_mul_le ( Nat.sub_pos_of_lt ( by linarith ) ) ];
        have h_card : ∀ u ∈ Finset.univ.erase a, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = u) Finset.univ) ≥ Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) := by
          intros u hu;
          have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = u) Finset.univ) ≥ Finset.card (Finset.image (fun σ : Equiv.Perm (Fin n) => Equiv.swap u b * σ) (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ)) := by
            refine Finset.card_le_card ?_;
            simp +decide [ Finset.subset_iff ];
            grind +splitImp;
          rwa [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] at h_card;
        simpa [ mul_comm, Finset.card_erase_of_mem ( Finset.mem_univ a ) ] using Finset.sum_le_sum h_card;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun σ hσx hσy => hxy <| by aesop;
    have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) = (n - 1).factorial := by
      have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) * n = Finset.card (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
        have h_card : ∀ j : Fin n, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = j) Finset.univ) = Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) := by
          intro j
          have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = j) Finset.univ) = Finset.card (Finset.image (fun σ : Equiv.Perm (Fin n) => Equiv.swap a j * σ) (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ)) := by
            congr with σ ; aesop;
          rw [ h_card, Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
        have h_card : Finset.card (Finset.univ : Finset (Equiv.Perm (Fin n))) = ∑ j : Fin n, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = j) Finset.univ) := by
          simp +decide only [Finset.card_eq_sum_ones, Finset.sum_fiberwise];
        simp_all +decide [ mul_comm ];
      simp_all +decide [ Finset.card_univ, Fintype.card_perm ];
      cases n <;> simp_all +decide [ Nat.factorial_succ ];
      nlinarith;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.factorial ];
    · contradiction;
    · contradiction;
  exact le_trans ( Finset.card_le_card h_perm ) ( le_trans ( Finset.card_biUnion_le ) ( by simpa using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_card i ) )