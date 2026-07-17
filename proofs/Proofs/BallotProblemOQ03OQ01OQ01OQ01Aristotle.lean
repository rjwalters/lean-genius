/-
  Aristotle solution for BallotProblemOQ03OQ01OQ01OQ01 (Jacobi-Trudi Identity)

  Proved by Aristotle (run 9ddf3174-34e1-44f5-8445-2ceae64d61f5).

  Closes the b = 1 branch of `JacobiTrudi.jdt_weight_sum` via a bijection
    ψ : {(P, Q) // ¬ColStrictSym a 1 P Q} ≃ Sym (Fin n) (a + 1)
  with weight preservation.

  v4.31 migration note: the original helper lemmas quantified over a generic
  `{α : Type*} [LinearOrder α]`, but `JacobiTrudi.ColStrictSym` is hard-coded to
  `Fin n`, so those statements never actually type-checked against it (a stale
  metavariable `Fin ?m` could not unify with the free variable `α`). Rewritten
  here over the concrete `Fin n` (matching `JacobiTrudi.ColStrictSym`'s own
  signature) and the main proof re-derived following the same bijection
  strategy the (private, file-local) parent proof `jdt_weight_sum_b_one` uses.
-/
import Mathlib
import Proofs.BallotProblemOQ03OQ01OQ01OQ01

open MvPolynomial Matrix Finset

namespace BallotProblemOQ03OQ01OQ01OQ01Aristotle

variable {R : Type*} [CommRing R]

/- ### Helper lemmas -/

/-- For `Q : Sym (Fin n) 1`, the underlying multiset is the singleton `{q}` where `q` is the
    unique element of `Q`. -/
lemma sym_one_sort_head_singleton (n : ℕ) (Q : Sym (Fin n) 1) :
    ∃ q : Fin n, Q.1.sort (· ≤ ·) = [q] ∧ Q.1 = ({q} : Multiset (Fin n)) := by
  have hlen : (Q.1.sort (· ≤ ·)).length = 1 := (Multiset.length_sort (s := Q.1) _).trans Q.2
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨q, hq, ?_⟩
  have hcoe := congrArg (Multiset.ofList) hq
  rw [Multiset.sort_eq] at hcoe
  simpa using hcoe

/-- Positive form: with `a ≥ 1`, `ColStrictSym a 1 P Q` reduces to a single inequality
    on the heads of the sorted representatives. -/
lemma colStrictSym_a_one_iff_phead_lt_qhead {n a : ℕ} (ha : 1 ≤ a)
    (P : Sym (Fin n) a) (Q : Sym (Fin n) 1) :
    JacobiTrudi.ColStrictSym a 1 P Q ↔
      (P.1.sort (· ≤ ·))[0]'(by
        have h := (Multiset.length_sort (s := P.1) (· ≤ ·)).trans P.2; omega) <
      (Q.1.sort (· ≤ ·))[0]'(by
        have h := (Multiset.length_sort (s := Q.1) (· ≤ ·)).trans Q.2; omega) := by
  unfold JacobiTrudi.ColStrictSym
  have hmin : min a 1 = 1 := Nat.min_eq_right ha
  constructor
  · intro h
    exact h ⟨0, by omega⟩
  · intro h j
    have hp1 : 0 < min a 1 := by omega
    have hj0 : j.val = 0 := by
      have : j.val < min a 1 := j.isLt
      omega
    have hjeq : j = ⟨0, hp1⟩ := Fin.ext hj0
    subst hjeq
    exact h

/-
For b=1 with a ≥ 1, ¬ColStrictSym a 1 P Q iff the single element of Q
is ≤ the minimum element of P (i.e. P.sort[0]).
-/
lemma not_colStrict_b_one {n a : ℕ} (ha : 1 ≤ a)
    (P : Sym (Fin n) a) (Q : Sym (Fin n) 1) :
    ¬ JacobiTrudi.ColStrictSym a 1 P Q ↔
      (Q.1.sort (· ≤ ·))[0]'(by
        have h := (Multiset.length_sort (s := Q.1) (· ≤ ·)).trans Q.2; omega) ≤
      (P.1.sort (· ≤ ·))[0]'(by
        have h := (Multiset.length_sort (s := P.1) (· ≤ ·)).trans P.2; omega) := by
  rw [colStrictSym_a_one_iff_phead_lt_qhead ha P Q, not_lt]

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
  simp only [hsymm]
  -- Length helpers
  have plen : ∀ P : Sym (Fin n) a, (P.1.sort (· ≤ ·)).length = a :=
    fun P => (Multiset.length_sort (s := P.1) _).trans P.2
  have slen : ∀ S : Sym (Fin n) (a + 1), (S.1.sort (· ≤ ·)).length = a + 1 :=
    fun S => (Multiset.length_sort (s := S.1) _).trans S.2
  have plen_idx : ∀ P : Sym (Fin n) a, 0 < (P.1.sort (· ≤ ·)).length := fun P => by
    have := plen P; omega
  have slen_idx : ∀ S : Sym (Fin n) (a + 1), 0 < (S.1.sort (· ≤ ·)).length := fun S => by
    have := slen S; omega
  -- Sorted multiset minimum ≤ every element
  have sort_min_le_sym : ∀ (m : Sym (Fin n) (a + 1)) (x : Fin n), x ∈ m.1 →
      (m.1.sort (· ≤ ·))[0]'(slen_idx m) ≤ x := fun m x hx => by
    have hx_s := (Multiset.mem_sort (· ≤ ·)).mpr hx
    have hne := List.ne_nil_of_mem hx_s
    have hpw := (Multiset.pairwise_sort m.1 (· ≤ ·)).rel_head hx_s
    rwa [List.head_eq_getElem_zero hne] at hpw
  have sort_min_le_p : ∀ (P : Sym (Fin n) a) (x : Fin n), x ∈ P.1 →
      (P.1.sort (· ≤ ·))[0]'(plen_idx P) ≤ x := fun P x hx => by
    have hx_s := (Multiset.mem_sort (· ≤ ·)).mpr hx
    have hne := List.ne_nil_of_mem hx_s
    have hpw := (Multiset.pairwise_sort P.1 (· ≤ ·)).rel_head hx_s
    rwa [List.head_eq_getElem_zero hne] at hpw
  -- Extract unique element of Sym n 1
  let getq : Sym (Fin n) 1 → Fin n := fun Q => (sym_one_sort_head_singleton n Q).choose
  have getq_spec : ∀ Q : Sym (Fin n) 1, Q.1 = ({getq Q} : Multiset (Fin n)) :=
    fun Q => (sym_one_sort_head_singleton n Q).choose_spec.2
  have getq_eq : ∀ (Q : Sym (Fin n) 1) (q : Fin n), Q.1 = ({q} : Multiset (Fin n)) →
      getq Q = q := fun Q q hq => by
    have := getq_spec Q; rw [hq] at this
    exact Multiset.singleton_inj.mp this.symm
  -- Bijection ψ : {(P, Q) // ¬ColStrictSym a 1 P Q} ≃ Sym (Fin n) (a + 1)
  -- Forward: (P, Q) ↦ (getq Q) ::ₛ P   (prepend the unique element of Q)
  let Fψ : { PQ : Sym (Fin n) a × Sym (Fin n) 1 // ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 } →
      Sym (Fin n) (a + 1) := fun p => Sym.cons (getq p.1.2) p.1.1
  -- Inverse: S ↦ (S.erase S.sort[0], ⟨{S.sort[0]}, _⟩)   (peel off the minimum)
  let Gψ : Sym (Fin n) (a + 1) →
      { PQ : Sym (Fin n) a × Sym (Fin n) 1 // ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 } := fun S =>
    let qS := (S.1.sort (· ≤ ·))[0]'(slen_idx S)
    have hmem : qS ∈ S.1 :=
      (Multiset.mem_sort _).mp (List.getElem_mem (slen_idx S))
    let P' := Sym.erase S qS hmem
    have hP'len : (P'.1.sort (· ≤ ·)).length = a :=
      (Multiset.length_sort (s := P'.1) _).trans P'.2
    have hP'len_idx : 0 < (P'.1.sort (· ≤ ·)).length := by have := hP'len; omega
    ⟨(P', ⟨{qS}, Multiset.card_singleton qS⟩),
      (not_colStrict_b_one ha P'
        ⟨{qS}, Multiset.card_singleton qS⟩).mpr (by
        simp only [Multiset.sort_singleton, List.getElem_cons_zero]
        exact sort_min_le_sym S _
          (Multiset.mem_of_mem_erase
            ((Multiset.mem_sort _).mp (List.getElem_mem hP'len_idx))))⟩
  have hleft : ∀ p, Gψ (Fψ p) = p := fun ⟨(P, Q), h⟩ => by
    obtain ⟨q, hqsort, hqms⟩ := sym_one_sort_head_singleton n Q
    have hgq : getq Q = q := getq_eq Q q hqms
    -- The ¬ColStrict condition gives q ≤ P.sort[0]
    have hq_le : q ≤ (P.1.sort (· ≤ ·))[0]'(plen_idx P) := by
      have h' := (not_colStrict_b_one ha P Q).mp h
      simp only [hqsort, List.getElem_cons_zero] at h'
      exact h'
    -- Since q ≤ P.sort[0] ≤ every element of P.1, sort of q ::ₘ P.1 starts with q
    have hcons_sort : (q ::ₘ P.1).sort (· ≤ ·) = q :: P.1.sort (· ≤ ·) :=
      Multiset.sort_cons q P.1 (· ≤ ·)
        (fun b hb => hq_le.trans (sort_min_le_p P b hb))
    -- So the head of (Sym.cons q P).1.sort is q
    have hqS_q : ((Sym.cons q P).1.sort (· ≤ ·))[0]'(slen_idx _) = q := by
      have hsort2 : (Sym.cons q P).1.sort (· ≤ ·) = q :: P.1.sort (· ≤ ·) := by
        show (q ::ₘ P.1).sort (· ≤ ·) = q :: P.1.sort (· ≤ ·)
        exact hcons_sort
      rw [List.getElem_of_eq hsort2 (slen_idx _)]
      simp
    show Gψ (Sym.cons (getq Q) P) = ⟨(P, Q), h⟩
    simp only [Gψ, Fψ, hgq, hqS_q]
    -- Goal is now: ⟨(Sym.erase (Sym.cons q P) q _, ⟨{q},_⟩),_⟩ = ⟨(P,Q),h⟩
    apply Subtype.ext; apply Prod.ext
    · exact Sym.erase_cons_head P q
    · exact Subtype.ext hqms.symm
  have hright : ∀ S, Fψ (Gψ S) = S := fun S => by
    have hmem : (S.1.sort (· ≤ ·))[0]'(slen_idx S) ∈ S.1 :=
      (Multiset.mem_sort _).mp (List.getElem_mem (slen_idx S))
    show Fψ (Gψ S) = S
    simp only [Fψ, Gψ]
    rw [show getq ⟨{(S.1.sort (· ≤ ·))[0]'(slen_idx S)},
                    Multiset.card_singleton _⟩ =
            (S.1.sort (· ≤ ·))[0]'(slen_idx S) from
          getq_eq _ _ rfl]
    exact Sym.cons_erase hmem
  let ψ : { PQ : Sym (Fin n) a × Sym (Fin n) 1 // ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 } ≃
          Sym (Fin n) (a + 1) := ⟨Fψ, Gψ, hleft, hright⟩
  -- Weight preservation: wt(P) * wt(Q) = wt(ψ(P,Q)) under the bijection
  refine Fintype.sum_equiv ψ _ _ fun ⟨(P, Q), _⟩ => ?_
  show (P.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
       (Q.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
       ((getq Q ::ₘ P.1).map (X : Fin n → MvPolynomial (Fin n) R)).prod
  rw [getq_spec Q, Multiset.map_singleton, Multiset.prod_singleton,
      Multiset.map_cons, Multiset.prod_cons]
  ring

end BallotProblemOQ03OQ01OQ01OQ01Aristotle
