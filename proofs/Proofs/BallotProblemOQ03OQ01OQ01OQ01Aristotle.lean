/-
  Aristotle solution for BallotProblemOQ03OQ01OQ01OQ01 (Jacobi-Trudi Identity)

  Proved by Aristotle (run 9ddf3174-34e1-44f5-8445-2ceae64d61f5).

  Closes the b = 1 branch of `JacobiTrudi.jdt_weight_sum` via a bijection
    ψ : {(P, Q) // ¬ColStrictSym a 1 P Q} ≃ Sym (Fin n) (a + 1)
  with weight preservation.
-/
import Mathlib
import Proofs.BallotProblemOQ03OQ01OQ01OQ01

open MvPolynomial Matrix Finset

namespace BallotProblemOQ03OQ01OQ01OQ01Aristotle

variable {R : Type*} [CommRing R]

/- ### Helper lemmas -/

/-
For b=1 with a ≥ 1, ¬ColStrictSym a 1 P Q iff the single element of Q
is ≤ the minimum element of P (i.e. P.sort[0]).
-/
lemma not_colStrict_b_one {α : Type*} [LinearOrder α] {a : ℕ} (ha : 1 ≤ a)
    (P : Sym α a) (Q : Sym α 1) :
    ¬ JacobiTrudi.ColStrictSym a 1 P Q ↔
    (Q.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, Q.2]; omega⟩ ≤
    (P.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, P.2]; exact ha⟩ := by
  unfold JacobiTrudi.ColStrictSym;
  grind

/-
Weight decomposition: wt(q ::ₛ P) = X(q) * wt(P).
-/
lemma cons_weight (n a : ℕ) (P : Sym (Fin n) a) (q : Fin n) :
    ((q ::ₛ P).1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    X q * (P.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod := by
  rw [ Sym.cons ];
  simp +decide [ mul_comm ]

/-
Main theorem: the sum of pair-weights over non-col-strict pairs equals h_{a+1}.
-/
theorem jdt_weight_sum_b_one_Aristotle (n a : ℕ) (ha : 1 ≤ a) :
    ∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) 1 //
              ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R (a + 1) := by
  -- We'll use the fact that if the condition holds for all elements in a finite set, then the sums are equal.
  have h_sum_eq : ∑ PQ : Sym (Fin n) a × Sym (Fin n) 1, (if ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 then (PQ.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod * (PQ.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod else 0) = ∑ S : Sym (Fin n) (a + 1), (S.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod := by
    have h_bij : ∀ S : Sym (Fin n) (a + 1), ∃! PQ : Sym (Fin n) a × Sym (Fin n) 1, ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 ∧ PQ.1.1 + PQ.2.1 = S.1 := by
      intro S
      obtain ⟨q, hq⟩ : ∃ q ∈ S.1, ∀ x ∈ S.1, q ≤ x := by
        exact ⟨ Finset.min' ( S.1.toFinset ) ⟨ _, Multiset.mem_toFinset.mpr ( Classical.choose_spec ( Multiset.card_pos_iff_exists_mem.mp ( by linarith [ S.2 ] ) ) ) ⟩, Multiset.mem_toFinset.mp ( Finset.min'_mem _ _ ), fun x hx => Finset.min'_le _ _ ( Multiset.mem_toFinset.mpr hx ) ⟩
      obtain ⟨P, hP⟩ : ∃ P : Sym (Fin n) a, P.1 + {q} = S.1 := by
        have h_erase : ∃ P : Multiset (Fin n), P + {q} = S.1 := by
          exact ⟨ S.1 - { q }, by rw [ tsub_add_cancel_of_le ( by aesop ) ] ⟩
        generalize_proofs at *;
        obtain ⟨ P, hP ⟩ := h_erase
        generalize_proofs at *;
        exact ⟨ ⟨ P, by simpa using congr_arg Multiset.card hP ⟩, hP ⟩
      use (P, ⟨{q}, by
        simp +decide⟩)
      generalize_proofs at *;
      refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
      · intro h;
        have := h 0 ( by simp +decide [ ha ] );
        simp_all +decide [ Multiset.sort_cons ];
        contrapose! this;
        have h_min : ∀ x ∈ P.1, q ≤ x := by
          exact fun x hx => hq.2 x <| hP ▸ Multiset.mem_add.mpr <| Or.inl hx;
        exact h_min _ ( Multiset.mem_sort ( α := Fin n ) ( · ≤ · ) |>.1 ( by simp +decide ) );
      · exact hP;
      · rintro ⟨ P', Q' ⟩ ⟨ h₁, h₂ ⟩
        have hQ' : Q'.1 = {q} := by
          have hQ' : q ∈ Q'.1 := by
            contrapose! h₁;
            have hQ' : q ∈ P'.1 := by
              replace h₂ := congr_arg ( fun s => q ∈ s ) h₂ ; aesop
            generalize_proofs at *;
            have hQ' : (Q'.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, Q'.2]; omega⟩ > q := by
              have hQ' : ∀ x ∈ Q'.1, q < x := by
                exact fun x hx => lt_of_le_of_ne ( hq.2 x ( h₂ ▸ Multiset.mem_add.2 ( Or.inr hx ) ) ) fun h => h₁ ( h ▸ hx )
              generalize_proofs at *;
              exact hQ' _ ( Multiset.mem_sort ( α := Fin n ) ( · ≤ · ) |>.1 ( by simp ) )
            generalize_proofs at *;
            intro i hi; rcases i with ( _ | i ) <;> simp_all +decide ;
            · have hP'_min : ∀ x ∈ P'.1, ((P'.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, P'.2]; omega⟩) ≤ x := by
                intro x hx; have := List.pairwise_iff_get.mp ( show List.Pairwise ( fun x1 x2 => x1 ≤ x2 ) ( P'.1.sort ( · ≤ · ) ) from by
                                                                grind +suggestions ) ; simp_all +decide [ List.get ] ;
                generalize_proofs at *;
                have hQ' : x ∈ P'.1.sort (· ≤ ·) := by
                  exact Multiset.mem_sort ( α := Fin n ) ( · ≤ · ) |>.2 hx
                generalize_proofs at *;
                obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hQ';
                by_cases hi0 : i = ⟨0, by rw [Multiset.length_sort, P'.2]; omega⟩;
                · aesop;
                · exact hi ▸ this ⟨ 0, by linarith ⟩ i ( lt_of_le_of_ne ( Nat.zero_le _ ) ( Ne.symm hi0 ) )
              generalize_proofs at *;
              exact lt_of_le_of_lt ( hP'_min _ ‹_› ) hQ';
            · omega
          generalize_proofs at *;
          exact Multiset.eq_of_le_of_card_le ( Multiset.singleton_le.mpr hQ' ) ( by simp +decide [ Q'.2 ] ) ▸ rfl
        generalize_proofs at *;
        have hP' : P'.1 = P.1 := by
          replace h₂ := congr_arg ( fun x => x - { q } ) h₂ ; simp_all +decide [ add_comm ] ;
          rw [ ← hP, Multiset.erase_cons_head ]
        generalize_proofs at *;
        cases P' ; cases P ; aesop;
    choose f hf₁ hf₂ using h_bij;
    have h_bij : Finset.image f Finset.univ = Finset.filter (fun PQ => ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2) (Finset.univ : Finset (Sym (Fin n) a × Sym (Fin n) 1)) := by
      ext PQ;
      simp +zetaDelta at *;
      constructor;
      · rintro ⟨ S, rfl ⟩ ; exact hf₁ S |>.1;
      · intro hPQ
        obtain ⟨S, hS⟩ : ∃ S : Sym (Fin n) (a + 1), PQ.1.1 + PQ.2.1 = S.1 := by
          exact ⟨ ⟨ PQ.1.1 + PQ.2.1, by simp +decide [ PQ.1.2, PQ.2.2 ] ⟩, rfl ⟩;
        exact ⟨ S, hf₂ S PQ.1 PQ.2 hPQ hS ▸ rfl ⟩;
    rw [ ← Finset.sum_filter, ← h_bij, Finset.sum_image ];
    · refine' Finset.sum_congr rfl fun S _ => _;
      rw [ ← Multiset.prod_add, ← Multiset.map_add, hf₁ S |>.2 ];
    · intro S hS T hT h_eq;
      have := hf₁ S; have := hf₁ T; simp_all +decide ;
  convert h_sum_eq using 1;
  simp +decide [ Finset.sum_ite ];
  refine' Finset.sum_bij ( fun x hx => x.val ) _ _ _ _ <;> simp +decide

end BallotProblemOQ03OQ01OQ01OQ01Aristotle
