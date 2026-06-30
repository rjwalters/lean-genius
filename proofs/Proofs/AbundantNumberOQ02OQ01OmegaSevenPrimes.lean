/-
  **Prime-set characterisation of the open `ω = 7` residual case.**

  The exact-minimality problem for "the smallest odd abundant number not divisible by 3
  is `5391411025 = 5²·7·11·13·17·19·23·29`" has been reduced (companion files) to a single
  residual shape: an odd abundant number coprime to 3 strictly below `5391411025` must be
  **non-squarefree with exactly 7 distinct prime factors**.  That residual case was left
  open as an *unbounded* search over seven-prime numbers.

  This file closes the **prime-set half** of that residual case: it pins down *which* seven
  primes can occur.  The headline result is

      n odd, coprime to 3, abundant, ω(n) = 7
        ⟹  n.primeFactors ∈ { {5,7,11,13,17,19,23}, {5,7,11,13,17,19,29},
                               {5,7,11,13,17,19,31}, {5,7,11,13,17,19,37} }.

  In words: the six smallest prime factors are *forced* to be `5,7,11,13,17,19`, and the
  seventh is one of just four primes `23, 29, 31, 37`.  This turns the previously unbounded
  "seven distinct primes" family into a **finite, explicit** list of four prime supports —
  the remaining work is only to bound the exponents on each of these four supports.

  The argument is the Euler abundancy bound `∏_{p∣n} p/(p−1) > 2` (companion
  `abundant_imp_two_mul_prod_sub_one_lt`, recast over ℚ) combined with sharp numeric
  comparisons against the antitone weight `f p = p/(p−1)`:

  * If the sixth prime were `≥ 23`, the weight product would be
    `≤ (5/4)(7/6)(11/10)(13/12)(17/16)(23/22)(29/28) = 56751695/28385280 < 2` — contradiction.
    Hence the sixth prime is `19` and the first six are `5,7,11,13,17,19`.
  * If the seventh prime were `≥ 41`, the weight product would be
    `≤ (5/4)(7/6)(11/10)(13/12)(17/16)(19/18)(41/40) = 66281215/33177600 < 2` — contradiction.
    Hence the seventh prime is `≤ 37`, i.e. one of `23,29,31,37`.

  No enumeration of the `~5.4·10⁹` range is used; only the seven-fold weight product and the
  prime gaps `5→7→11→13→17→19→23→29` (reused verbatim from the companion files).

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01GeneralBound

namespace AbundantNumberOQ02OQ01OmegaSevenPrimes

open AbundantNumberOQ02OQ01Minimality
open AbundantNumberOQ02OQ01Unconditional
open AbundantNumberOQ02OQ01LowerBound
open AbundantNumberOQ02OQ01Squarefree
open AbundantNumberOQ02OQ01GeneralBound

/-- A list of length 7 is literally a 7-tuple cons-list. -/
private lemma length_eq_seven {α : Type*} {L : List α} (h : L.length = 7) :
    ∃ a0 a1 a2 a3 a4 a5 a6, L = [a0, a1, a2, a3, a4, a5, a6] := by
  rcases L with _ | ⟨a0, L⟩; · simp at h
  rcases L with _ | ⟨a1, L⟩; · simp at h
  rcases L with _ | ⟨a2, L⟩; · simp at h
  rcases L with _ | ⟨a3, L⟩; · simp at h
  rcases L with _ | ⟨a4, L⟩; · simp at h
  rcases L with _ | ⟨a5, L⟩; · simp at h
  rcases L with _ | ⟨a6, L⟩; · simp at h
  rcases L with _ | ⟨a7, L⟩
  · exact ⟨a0, a1, a2, a3, a4, a5, a6, rfl⟩
  · simp only [List.length_cons] at h; omega

/-- Monotonicity of a seven-fold (right-associated) product of nonnegative rationals. -/
private lemma mul7_le {a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : ℚ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4)
    (h5 : a5 ≤ b5) (h6 : a6 ≤ b6) (h7 : a7 ≤ b7)
    (n1 : 0 ≤ a1) (n2 : 0 ≤ a2) (n3 : 0 ≤ a3) (n4 : 0 ≤ a4)
    (n5 : 0 ≤ a5) (n6 : 0 ≤ a6) (n7 : 0 ≤ a7) :
    a1 * (a2 * (a3 * (a4 * (a5 * (a6 * a7))))) ≤
      b1 * (b2 * (b3 * (b4 * (b5 * (b6 * b7))))) := by
  have p67 : a6 * a7 ≤ b6 * b7 := mul_le_mul h6 h7 n7 (le_trans n6 h6)
  have p5 : a5 * (a6 * a7) ≤ b5 * (b6 * b7) :=
    mul_le_mul h5 p67 (mul_nonneg n6 n7) (le_trans n5 h5)
  have p4 : a4 * (a5 * (a6 * a7)) ≤ b4 * (b5 * (b6 * b7)) :=
    mul_le_mul h4 p5 (mul_nonneg n5 (mul_nonneg n6 n7)) (le_trans n4 h4)
  have p3 : a3 * (a4 * (a5 * (a6 * a7))) ≤ b3 * (b4 * (b5 * (b6 * b7))) :=
    mul_le_mul h3 p4 (mul_nonneg n4 (mul_nonneg n5 (mul_nonneg n6 n7))) (le_trans n3 h3)
  have p2 : a2 * (a3 * (a4 * (a5 * (a6 * a7)))) ≤ b2 * (b3 * (b4 * (b5 * (b6 * b7)))) :=
    mul_le_mul h2 p3 (mul_nonneg n3 (mul_nonneg n4 (mul_nonneg n5 (mul_nonneg n6 n7))))
      (le_trans n2 h2)
  exact mul_le_mul h1 p2
    (mul_nonneg n2 (mul_nonneg n3 (mul_nonneg n4 (mul_nonneg n5 (mul_nonneg n6 n7)))))
    (le_trans n1 h1)

/-- The weight product for the floor `[5,7,11,13,17,23,29]` (sixth prime `≥ 23`). -/
private lemma floorA_lt_two :
    f 5 * (f 7 * (f 11 * (f 13 * (f 17 * (f 23 * f 29))))) < 2 := by
  simp only [f]; norm_num

/-- The weight product for the floor `[5,7,11,13,17,19,41]` (seventh prime `≥ 41`). -/
private lemma floorB_lt_two :
    f 5 * (f 7 * (f 11 * (f 13 * (f 17 * (f 19 * f 41))))) < 2 := by
  simp only [f]; norm_num

/-- **Euler abundancy bound, weight form.**  For an odd abundant number coprime to 3 the
weighted product `∏_{p∣n} p/(p−1)` exceeds `2`.  This is the rational recasting of
`abundant_imp_two_mul_prod_sub_one_lt` carried out inside the `ω ≥ 7` theorem, isolated
here as a reusable entry point. -/
lemma euler_f_gt_two {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n) :
    2 < ∏ p ∈ n.primeFactors, f p := by
  set S := n.primeFactors with hS
  have hge5 : ∀ p ∈ S, 5 ≤ p := primeFactor_ge_five hodd h3
  have hineq : 2 * ∏ p ∈ S, (p - 1) < ∏ p ∈ S, p :=
    abundant_imp_two_mul_prod_sub_one_lt habund
  have hMpos : 0 < ∏ p ∈ S, ((p : ℚ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have h5p : 5 ≤ p := hge5 p hp
    have : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h5p
    linarith
  have hfprod_eq : (∏ p ∈ S, f p) = (∏ p ∈ S, (p : ℚ)) / (∏ p ∈ S, ((p : ℚ) - 1)) := by
    simp only [f]
    rw [Finset.prod_div_distrib]
  have hcastM : ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) = ∏ p ∈ S, ((p : ℚ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have h1p : 1 ≤ p := le_trans (by norm_num) (hge5 p hp)
    rw [Nat.cast_sub h1p, Nat.cast_one]
  have hcastN : ((∏ p ∈ S, p : ℕ) : ℚ) = ∏ p ∈ S, (p : ℚ) := by rw [Nat.cast_prod]
  have hineqQ : 2 * (∏ p ∈ S, ((p : ℚ) - 1)) < ∏ p ∈ S, (p : ℚ) := by
    have hc : ((2 * ∏ p ∈ S, (p - 1) : ℕ) : ℚ) < ((∏ p ∈ S, p : ℕ) : ℚ) := by exact_mod_cast hineq
    rwa [Nat.cast_mul, Nat.cast_ofNat, hcastM, hcastN] at hc
  have key : 2 * (∏ p ∈ S, ((p : ℚ) - 1)) < (∏ p ∈ S, f p) * (∏ p ∈ S, ((p : ℚ) - 1)) := by
    have heq : (∏ p ∈ S, f p) * (∏ p ∈ S, ((p : ℚ) - 1)) = ∏ p ∈ S, (p : ℚ) := by
      rw [hfprod_eq, div_mul_cancel₀]
      exact ne_of_gt hMpos
    rw [heq]; exact hineqQ
  exact lt_of_mul_lt_mul_right key (le_of_lt hMpos)

/-- **Prime-set characterisation of the `ω = 7` residual case.**  An odd abundant number
coprime to 3 with *exactly* seven distinct prime factors has prime support equal to one of
the four explicit seven-element sets

    {5,7,11,13,17,19,23}, {5,7,11,13,17,19,29}, {5,7,11,13,17,19,31}, {5,7,11,13,17,19,37}.

The six smallest prime factors are forced to be `5,7,11,13,17,19`; the seventh is one of
`23,29,31,37`.  This confines the open exact-minimality residual (`ω = 7`, non-squarefree)
to four explicit prime supports — only the prime-power exponents remain to be bounded. -/
theorem omega_seven_prime_support
    {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n)
    (hcard7 : n.primeFactors.card = 7) :
    n.primeFactors = ({5, 7, 11, 13, 17, 19, 23} : Finset ℕ) ∨
    n.primeFactors = ({5, 7, 11, 13, 17, 19, 29} : Finset ℕ) ∨
    n.primeFactors = ({5, 7, 11, 13, 17, 19, 31} : Finset ℕ) ∨
    n.primeFactors = ({5, 7, 11, 13, 17, 19, 37} : Finset ℕ) := by
  -- The sorted prime-factor list has length 7; destructure into seven entries.
  have hlen7 : (n.primeFactors.sort (· ≤ ·)).length = 7 := by
    rw [Finset.length_sort]; exact hcard7
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, hLeq⟩ := length_eq_seven hlen7
  -- Membership / primality / floor facts transported onto the destructured list.
  have hprime : ∀ x ∈ ([a0, a1, a2, a3, a4, a5, a6] : List ℕ), x.Prime := by
    rw [← hLeq]
    intro x hx
    rw [Finset.mem_sort] at hx
    exact Nat.prime_of_mem_primeFactors hx
  have hge5' : ∀ x ∈ ([a0, a1, a2, a3, a4, a5, a6] : List ℕ), 5 ≤ x := by
    rw [← hLeq]
    intro x hx
    rw [Finset.mem_sort] at hx
    exact primeFactor_ge_five hodd h3 x hx
  -- Strict monotonicity of the sorted list, peeled into consecutive inequalities.
  have hpw : ([a0, a1, a2, a3, a4, a5, a6] : List ℕ).Pairwise (· < ·) := by
    rw [← hLeq]
    have hsorted : List.Pairwise (· ≤ ·) (n.primeFactors.sort (· ≤ ·)) :=
      Finset.pairwise_sort n.primeFactors (· ≤ ·)
    have hnodup : (n.primeFactors.sort (· ≤ ·)).Nodup := Finset.sort_nodup n.primeFactors (· ≤ ·)
    exact (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  rw [List.pairwise_cons] at hpw; obtain ⟨h0, hpw⟩ := hpw
  rw [List.pairwise_cons] at hpw; obtain ⟨h1, hpw⟩ := hpw
  rw [List.pairwise_cons] at hpw; obtain ⟨h2, hpw⟩ := hpw
  rw [List.pairwise_cons] at hpw; obtain ⟨h3', hpw⟩ := hpw
  rw [List.pairwise_cons] at hpw; obtain ⟨h4, hpw⟩ := hpw
  rw [List.pairwise_cons] at hpw; obtain ⟨h5, _⟩ := hpw
  have l01 : a0 < a1 := h0 a1 (by simp)
  have l12 : a1 < a2 := h1 a2 (by simp)
  have l23 : a2 < a3 := h2 a3 (by simp)
  have l34 : a3 < a4 := h3' a4 (by simp)
  have l45 : a4 < a5 := h4 a5 (by simp)
  have l56 : a5 < a6 := h5 a6 (by simp)
  -- Primality and the basic `≥ 5` floor for each entry.
  have hp0 : a0.Prime := hprime a0 (by simp)
  have hp1 : a1.Prime := hprime a1 (by simp)
  have hp2 : a2.Prime := hprime a2 (by simp)
  have hp3 : a3.Prime := hprime a3 (by simp)
  have hp4 : a4.Prime := hprime a4 (by simp)
  have hp5 : a5.Prime := hprime a5 (by simp)
  have hp6 : a6.Prime := hprime a6 (by simp)
  have e0 : 5 ≤ a0 := hge5' a0 (by simp)
  -- Consecutive prime gaps lift the floor to `5,7,11,13,17,19,23`.
  have e1 : 7 ≤ a1 := gap5 a1 hp1 (by omega)
  have e2 : 11 ≤ a2 := gap7 a2 hp2 (by omega)
  have e3 : 13 ≤ a3 := gap11 a3 hp3 (by omega)
  have e4 : 17 ≤ a4 := gap13 a4 hp4 (by omega)
  have e5 : 19 ≤ a5 := gap17 a5 hp5 (by omega)
  have e6 : 23 ≤ a6 := gap19 a6 hp6 (by omega)
  -- Nonnegativity helper.
  have pf : ∀ x : ℕ, 2 ≤ x → (0 : ℚ) ≤ f x := fun x hx => le_of_lt (f_pos hx)
  -- The Euler weight bound transported to the destructured product (right-associated).
  have hgt : 2 < f a0 * (f a1 * (f a2 * (f a3 * (f a4 * (f a5 * f a6))))) := by
    have hprodF : ((n.primeFactors.sort (· ≤ ·)).map f).prod = ∏ p ∈ n.primeFactors, f p := by
      rw [← Finset.prod_map_toList n.primeFactors f]
      exact List.Perm.prod_eq ((Finset.sort_perm_toList n.primeFactors (· ≤ ·)).map f)
    have h := euler_f_gt_two hodd h3 habund
    rw [← hprodF, hLeq] at h
    simpa [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] using h
  -- STEP 1: the sixth prime factor is `19` (else the weight product drops below 2).
  have ha5 : a5 = 19 := by
    by_contra hne
    have e5' : 23 ≤ a5 := by
      by_contra hlt
      push_neg at hlt
      interval_cases a5
      · exact absurd rfl hne
      · exact absurd hp5 (by decide)
      · exact absurd hp5 (by decide)
      · exact absurd hp5 (by decide)
    have e6' : 29 ≤ a6 := gap23 a6 hp6 (by omega)
    have fa0 : f a0 ≤ f 5 := f_antitone (by norm_num) e0
    have fa1 : f a1 ≤ f 7 := f_antitone (by norm_num) e1
    have fa2 : f a2 ≤ f 11 := f_antitone (by norm_num) e2
    have fa3 : f a3 ≤ f 13 := f_antitone (by norm_num) e3
    have fa4 : f a4 ≤ f 17 := f_antitone (by norm_num) e4
    have fa5 : f a5 ≤ f 23 := f_antitone (by norm_num) e5'
    have fa6 : f a6 ≤ f 29 := f_antitone (by norm_num) e6'
    have hb := mul7_le fa0 fa1 fa2 fa3 fa4 fa5 fa6
      (pf a0 (by omega)) (pf a1 (by omega)) (pf a2 (by omega)) (pf a3 (by omega))
      (pf a4 (by omega)) (pf a5 (by omega)) (pf a6 (by omega))
    have := lt_of_le_of_lt hb floorA_lt_two
    linarith
  -- STEP 2: the seventh prime factor is `≤ 37` (else the weight product drops below 2).
  have ha6 : a6 = 23 ∨ a6 = 29 ∨ a6 = 31 ∨ a6 = 37 := by
    have hle40 : a6 ≤ 40 := by
      by_contra hgt40
      push_neg at hgt40
      have e6' : 41 ≤ a6 := by omega
      have fa0 : f a0 ≤ f 5 := f_antitone (by norm_num) e0
      have fa1 : f a1 ≤ f 7 := f_antitone (by norm_num) e1
      have fa2 : f a2 ≤ f 11 := f_antitone (by norm_num) e2
      have fa3 : f a3 ≤ f 13 := f_antitone (by norm_num) e3
      have fa4 : f a4 ≤ f 17 := f_antitone (by norm_num) e4
      have fa5 : f a5 ≤ f 19 := le_of_eq (by rw [ha5])
      have fa6 : f a6 ≤ f 41 := f_antitone (by norm_num) e6'
      have hb := mul7_le fa0 fa1 fa2 fa3 fa4 fa5 fa6
        (pf a0 (by omega)) (pf a1 (by omega)) (pf a2 (by omega)) (pf a3 (by omega))
        (pf a4 (by omega)) (pf a5 (by omega)) (pf a6 (by omega))
      have := lt_of_le_of_lt hb floorB_lt_two
      linarith
    interval_cases a6 <;>
      first
        | (exact absurd hp6 (by decide))
        | (left; rfl)
        | (right; left; rfl)
        | (right; right; left; rfl)
        | (right; right; right; rfl)
  -- STEP 3: with the sixth prime `= 19`, the first five are forced to be `5,7,11,13,17`.
  have ha4 : a4 = 17 := by
    have : a4 < 19 := by rw [← ha5]; exact l45
    interval_cases a4
    · rfl
    · exact absurd hp4 (by decide)
  have ha3 : a3 = 13 := by
    have : a3 < 17 := by rw [← ha4]; exact l34
    interval_cases a3
    · rfl
    · exact absurd hp3 (by decide)
    · exact absurd hp3 (by decide)
    · exact absurd hp3 (by decide)
  have ha2 : a2 = 11 := by
    have : a2 < 13 := by rw [← ha3]; exact l23
    interval_cases a2
    · rfl
    · exact absurd hp2 (by decide)
  have ha1 : a1 = 7 := by
    have : a1 < 11 := by rw [← ha2]; exact l12
    interval_cases a1
    · rfl
    · exact absurd hp1 (by decide)
    · exact absurd hp1 (by decide)
    · exact absurd hp1 (by decide)
  have ha0 : a0 = 5 := by
    have : a0 < 7 := by rw [← ha1]; exact l01
    interval_cases a0
    · rfl
    · exact absurd hp0 (by decide)
  -- Assemble: the sorted prime list is `[5,7,11,13,17,19,a6]`, hence the support set.
  have hsort_eq : n.primeFactors.sort (· ≤ ·) = [5, 7, 11, 13, 17, 19, a6] := by
    rw [hLeq, ha0, ha1, ha2, ha3, ha4, ha5]
  have hSset : n.primeFactors = ({5, 7, 11, 13, 17, 19, a6} : Finset ℕ) := by
    ext x
    rw [← Finset.mem_sort (· ≤ ·), hsort_eq]
    simp [List.mem_cons]
  rcases ha6 with h | h | h | h
  · left; rw [hSset, h]
  · right; left; rw [hSset, h]
  · right; right; left; rw [hSset, h]
  · right; right; right; rw [hSset, h]

#check @omega_seven_prime_support

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms omega_seven_prime_support

end AbundantNumberOQ02OQ01OmegaSevenPrimes
