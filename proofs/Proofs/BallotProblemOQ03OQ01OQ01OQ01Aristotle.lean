/-
  Aristotle target for BallotProblemOQ03OQ01OQ01OQ01 (Jacobi-Trudi Identity)

  HARD bijection lemma: closes the b = 1 branch of `jdt_weight_sum`.

  ## Context

  In `BallotProblemOQ03OQ01OQ01OQ01.lean`, the private lemma `jdt_weight_sum n a b`
  (line 373) has one `sorry` (line 448) that covers the b ≥ 1 case. Extracting b = 1
  as a clean helper removes one branch of that sorry; the remaining b ≥ 2 case is
  the genuine frontier requiring the full JDT seam construction.

  Statement (b = 1):
    For a ≥ 1, the sum of pair-weights over non-col-strict (P, Q) pairs
    of shapes (a, 1) equals h_{a+1}.

  This is a known JDT-style identity that, combined with `Sym.oneEquiv`, reduces
  to a weight-preserving bijection
    ψ : {(P, q) : Sym n a × Fin n // q ≤ P.sort[0]} ≃ Sym (Fin n) (a + 1)
  with forward map (P, q) ↦ q ::ₛ P and inverse P' ↦ (P'.erase q', oneEquiv.symm q')
  where q' is the smallest element of P'.sort.

  ## Proof Recipe (verified Mathlib v4.26.0, session 14)

  Key lemmas — all confirmed present in current Mathlib:

  * `Sym.oneEquiv : α ≃ Sym α 1`   (Data/Sym/Basic.lean:477, @[simps apply])
      forward a ↦ ⟨{a}, _⟩
  * `Sym.cons_erase : a ::ₛ s.erase a h = s`   (Data/Sym/Basic.lean:219, simp)
  * `Sym.erase_cons_head : (a ::ₛ s).erase a _ = s`   (Data/Sym/Basic.lean:223, simp)
  * `Multiset.sort_cons` — `(∀ b ∈ s, r a b) → sort(a ::ₘ s) r = a :: sort s r`
      (Data/Multiset/Sort.lean:69)
  * `Multiset.prod_cons`, `Multiset.map_cons` — multiplicativity for weight preservation
  * `hsymm_zero : hsymm σ R 0 = 1`   (RingTheory/MvPolynomial/Symmetric/Defs.lean:318)

  ## Strategy outline (~80-100 lines expected)

  1. Set up Equiv between `{(P, Q : Sym n a × Sym n 1) // ¬ColStrictSym a 1 P Q}`
     and `{(P, q : Sym n a × Fin n) // q ≤ P.sort[0]}` via `Sym.oneEquiv` on Q.
     The negation of `ColStrictSym a 1` (with min a 1 = 1, given a ≥ 1) reduces to
     `P.sort[0] ≥ Q.sort[0]`, and `Q.sort[0] = q` when `Q = oneEquiv q`.

  2. Set up Equiv ψ between `{(P, q) // q ≤ P.sort[0]}` and `Sym (Fin n) (a + 1)`:
     forward (P, q) ↦ q ::ₛ P
     inverse P' ↦ ((P'.erase q' h, q')) where:
       L  := P'.1.sort (· ≤ ·)
       q' := L.head (List.length_pos_of_ne_nil ...) = smallest element of P'
       h  := List.head_mem  /  Multiset.sort_eq  to coerce q' ∈ P'.1
     Constraint q' ≤ (P'.erase q').sort[0] follows from sortedness of L:
       L = q' :: L.tail (List.head_cons_tail), so L.tail[0] = L[1] ≥ L[0] = q'.

  3. Show forward and inverse are mutual inverses using
     `Sym.cons_erase` and `Sym.erase_cons_head` simp lemmas.

  4. Weight preservation: under ψ,
       wt(P) * wt(Q)  =  (P.1.map X).prod * (oneEquiv q).1.map X .prod
                      =  (P.1.map X).prod * X q                          -- (oneEquiv q).1 = {q}
                      =  ((q ::ₘ P.1).map X).prod                        -- map_cons + prod_cons
                      =  wt(q ::ₛ P)
     so `Equiv.sum_comp ψ` finishes the equality with `∑ P', wt P' = hsymm (a+1)`.

  ## Status

  Aristotle-proved (job 9ddf3174, 2026-05-02). The proof was retrieved and
  integrated here. The companion target is now sorry-free.

  The main file's private lemma `jdt_weight_sum_b_one` also proves this independently
  via the same bijection construction (~95 lines).
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Proofs.BallotProblemOQ03OQ01OQ01OQ01

open MvPolynomial Matrix Finset

namespace BallotProblemOQ03OQ01OQ01OQ01Aristotle

variable {R : Type*} [CommRing R]

/-! ### Helper lemmas -/

lemma not_colStrict_b_one {α : Type*} [LinearOrder α] {a : ℕ} (ha : 1 ≤ a)
    (P : Sym α a) (Q : Sym α 1) :
    ¬ JacobiTrudi.ColStrictSym a 1 P Q ↔
    (Q.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, Q.2]; omega⟩ ≤
    (P.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, P.2]; exact ha⟩ := by
  unfold JacobiTrudi.ColStrictSym
  grind

lemma cons_weight (n a : ℕ) (P : Sym (Fin n) a) (q : Fin n) :
    ((q ::ₛ P).1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    X q * (P.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod := by
  rw [Sym.cons]
  simp [mul_comm]

theorem jdt_weight_sum_b_one_Aristotle (n a : ℕ) (ha : 1 ≤ a) :
    ∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) 1 //
              ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R (a + 1) := by
  have h_sum_eq : ∑ PQ : Sym (Fin n) a × Sym (Fin n) 1,
      (if ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2
        then (PQ.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
             (PQ.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod
        else 0) =
      ∑ S : Sym (Fin n) (a + 1), (S.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod := by
    have h_bij : ∀ S : Sym (Fin n) (a + 1), ∃! PQ : Sym (Fin n) a × Sym (Fin n) 1,
        ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 ∧ PQ.1.1 + PQ.2.1 = S.1 := by
      intro S
      obtain ⟨q, hq⟩ : ∃ q ∈ S.1, ∀ x ∈ S.1, q ≤ x :=
        ⟨Finset.min' (S.1.toFinset)
          ⟨_, Multiset.mem_toFinset.mpr (Classical.choose_spec
            (Multiset.card_pos_iff_exists_mem.mp (by linarith [S.2])))⟩,
         Multiset.mem_toFinset.mp (Finset.min'_mem _ _),
         fun x hx => Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hx)⟩
      obtain ⟨P, hP⟩ : ∃ P : Sym (Fin n) a, P.1 + {q} = S.1 := by
        have h_erase : ∃ P : Multiset (Fin n), P + {q} = S.1 :=
          ⟨S.1 - {q}, by rw [tsub_add_cancel_of_le (by aesop)]⟩
        obtain ⟨P, hP⟩ := h_erase
        exact ⟨⟨P, by simpa using congr_arg Multiset.card hP⟩, hP⟩
      use (P, ⟨{q}, by simp⟩)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro h
        have := h 0 (by simp [ha])
        simp_all [Multiset.sort_cons]
        contrapose! this
        have h_min : ∀ x ∈ P.1, q ≤ x := fun x hx =>
          hq.2 x (hP ▸ Multiset.mem_add.mpr (Or.inl hx))
        exact h_min _ (Multiset.mem_sort (α := Fin n) (· ≤ ·) |>.1 (by simp))
      · exact hP
      · rintro ⟨P', Q'⟩ ⟨h₁, h₂⟩
        have hQ' : Q'.1 = {q} := by
          have hQ' : q ∈ Q'.1 := by
            contrapose! h₁
            have hQ' : q ∈ P'.1 := by
              replace h₂ := congr_arg (fun s => q ∈ s) h₂; aesop
            have hQ' : (Q'.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, Q'.2]; omega⟩ > q := by
              have hQ' : ∀ x ∈ Q'.1, q < x := fun x hx =>
                lt_of_le_of_ne (hq.2 x (h₂ ▸ Multiset.mem_add.2 (Or.inr hx)))
                  fun h => h₁ (h ▸ hx)
              exact hQ' _ (Multiset.mem_sort (α := Fin n) (· ≤ ·) |>.1 (by simp))
            intro i hi
            rcases i with (_ | i) <;> simp_all
            · have hP'_min : ∀ x ∈ P'.1,
                  ((P'.1.sort (· ≤ ·)).get ⟨0, by rw [Multiset.length_sort, P'.2]; omega⟩) ≤ x := by
                intro x hx
                have hpw := show List.Pairwise (fun x1 x2 => x1 ≤ x2) (P'.1.sort (· ≤ ·))
                  from Multiset.pairwise_sort _ P'.1
                have hQ' : x ∈ P'.1.sort (· ≤ ·) := Multiset.mem_sort (α := Fin n) (· ≤ ·) |>.2 hx
                obtain ⟨⟨i, hi'⟩, higet⟩ := List.mem_iff_getElem.mp hQ'
                by_cases hi0 : i = 0
                · subst hi0; simp_all
                · have hpw' := List.pairwise_iff_getElem.mp hpw
                  exact higet ▸ hpw' (by omega) (by omega) (by omega)
              exact lt_of_le_of_lt (hP'_min _ ‹_›) hQ'
            · omega
          exact Multiset.eq_of_le_of_card_le (Multiset.singleton_le.mpr hQ')
            (by simp [Q'.2]) ▸ rfl
        have hP' : P'.1 = P.1 := by
          replace h₂ := congr_arg (fun x => x - {q}) h₂
          simp_all [add_comm]
          rw [← hP, Multiset.erase_cons_head]
        cases P'; cases P; aesop
    choose f hf₁ hf₂ using h_bij
    have h_bij' : Finset.image f Finset.univ =
        Finset.filter (fun PQ => ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2)
          (Finset.univ : Finset (Sym (Fin n) a × Sym (Fin n) 1)) := by
      ext PQ
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨S, rfl⟩; exact hf₁ S |>.1
      · intro hPQ
        obtain ⟨S, hS⟩ : ∃ S : Sym (Fin n) (a + 1), PQ.1.1 + PQ.2.1 = S.1 :=
          ⟨⟨PQ.1.1 + PQ.2.1, by simp [PQ.1.2, PQ.2.2]⟩, rfl⟩
        exact ⟨S, hf₂ S PQ.1 PQ.2 hPQ hS ▸ rfl⟩
    rw [← Finset.sum_filter, ← h_bij', Finset.sum_image]
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Multiset.prod_add, ← Multiset.map_add, hf₁ S |>.2]
    · intro S _ T _ h_eq
      have hS := hf₁ S; have hT := hf₁ T; simp_all
  convert h_sum_eq using 1
  simp [Finset.sum_ite]
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_ <;> simp

end BallotProblemOQ03OQ01OQ01OQ01Aristotle
