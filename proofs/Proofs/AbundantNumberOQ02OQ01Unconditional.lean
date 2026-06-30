/-
  **Unconditional minimality lower bound.**

  Any odd abundant number coprime to 3 has at least 7 distinct prime factors.

  The companion file `AbundantNumberOQ02OQ01Minimality.lean` reduces the minimality
  half of "the smallest odd abundant number not divisible by 3 is 5391411025" to a
  single finite primorial inequality via the elementary Euler abundancy bound

      n abundant  ⟹  2 · ∏_{p∣n}(p−1)  <  ∏_{p∣n} p ,

  and records the **extremal / monotonicity step** ("∏ p/(p−1) is maximised by the
  smallest primes") as the only remaining open follow-up.  This file closes that gap.

  The engine is a clean list-recursion lemma `dom`:  for a strictly increasing list of
  primes whose i-th entry dominates the i-th entry of a *gap list* `C` (a list whose
  consecutive entries are forced apart by primality), the weighted product
  `∏ p/(p−1)` is bounded by the corresponding product over `C`.  Instantiated at the
  canonical gap list `[5,7,11,13,17,19]` (the six smallest primes ≥ 5), this gives

      |S| ≤ 6  ⟹  ∏_{p∈S} p/(p−1)  ≤  (5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2 ,

  contradicting the Euler bound `∏ p/(p−1) > 2`.  Hence `|S| ≥ 7` with no enumeration.

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01Minimality

namespace AbundantNumberOQ02OQ01Unconditional

open AbundantNumberOQ02OQ01Minimality
open scoped ArithmeticFunction.sigma

/-- The decreasing weight `f p = p/(p−1)` over ℚ (the per-prime factor of `σ(n)/n`). -/
def f (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

lemma f_pos {p : ℕ} (hp : 2 ≤ p) : 0 < f p := by
  have hpc : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  unfold f
  exact div_pos (by linarith) hden

lemma one_le_f {p : ℕ} (hp : 2 ≤ p) : 1 ≤ f p := by
  have hpc : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  unfold f
  rw [le_div_iff₀ hden]
  linarith

/-- `f` is antitone on `{p ≥ 2}`: larger primes give smaller weight `p/(p−1)`. -/
lemma f_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : f b ≤ f a := by
  have hac : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hbc : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  have hda : (0 : ℚ) < (a : ℚ) - 1 := by linarith
  have hdb : (0 : ℚ) < (b : ℚ) - 1 := by linarith
  unfold f
  rw [div_le_div_iff₀ hdb hda]
  nlinarith [hbc]

/-- The product of weights over a list of integers all `≥ 2` is `≥ 1`. -/
lemma one_le_listprod_f : ∀ {C : List ℕ}, (∀ c ∈ C, 2 ≤ c) → 1 ≤ (C.map f).prod
  | [], _ => by simp
  | c :: rest, h => by
      simp only [List.map_cons, List.prod_cons]
      have h1 : 1 ≤ f c := one_le_f (h c (List.mem_cons_self))
      have h2 : 1 ≤ (rest.map f).prod := one_le_listprod_f (fun x hx => h x (List.mem_cons_of_mem c hx))
      nlinarith [h1, h2]

/-- **Gap list predicate.**  `GapList C` holds when each entry is `≥ 2` and, for every
prime `p` strictly above an entry `c₀`, the *next* entry `c₁` already satisfies `c₁ ≤ p`.
For consecutive primes this is exactly the statement "there is no prime strictly between
`c₀` and `c₁`". -/
def GapList : List ℕ → Prop
  | [] => True
  | c0 :: rest => 2 ≤ c0 ∧ (∀ p : ℕ, p.Prime → c0 < p → ∀ c1 ∈ rest.head?, c1 ≤ p) ∧ GapList rest

lemma gapList_all_ge_two : ∀ {C : List ℕ}, GapList C → ∀ c ∈ C, 2 ≤ c
  | [], _ => by intro c hc; simp at hc
  | _ :: _, h => by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact h.1
      · exact gapList_all_ge_two h.2.2 c hc'

/-- **Domination lemma (the heart).**  If `L` is a strictly increasing list of primes,
every entry of `L` is at least the corresponding gap-list floor (`C.head?` advancing along
the gaps), and `L` is no longer than the gap list `C`, then the weighted product over `L`
is bounded by the weighted product over `C`. -/
lemma dom : ∀ (C L : List ℕ),
    L.Pairwise (· < ·) →
    (∀ x ∈ L, x.Prime) →
    (∀ x ∈ L, ∀ c0 ∈ C.head?, c0 ≤ x) →
    L.length ≤ C.length →
    GapList C →
    (L.map f).prod ≤ (C.map f).prod := by
  intro C L
  induction L generalizing C with
  | nil =>
      intro _ _ _ _ hG
      simp only [List.map_nil, List.prod_nil]
      exact one_le_listprod_f (gapList_all_ge_two hG)
  | cons a L' ih =>
      intro hpair hprime hfloor hlen hG
      cases C with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons c0 C1 =>
          obtain ⟨hc0, hgap, hG1⟩ := hG
          have hac0 : c0 ≤ a := hfloor a (List.mem_cons_self) c0 (by simp)
          have hfa : f a ≤ f c0 := f_antitone hc0 hac0
          have hpc := List.pairwise_cons.mp hpair
          have hlt : ∀ x ∈ L', a < x := hpc.1
          have hpair' : L'.Pairwise (· < ·) := hpc.2
          have hprime' : ∀ x ∈ L', x.Prime := fun x hx => hprime x (List.mem_cons_of_mem a hx)
          have hfloor' : ∀ x ∈ L', ∀ c1 ∈ C1.head?, c1 ≤ x := by
            intro x hx c1 hc1
            have hpx : x.Prime := hprime' x hx
            have hc0x : c0 < x := lt_of_le_of_lt hac0 (hlt x hx)
            exact hgap x hpx hc0x c1 hc1
          have hlen' : L'.length ≤ C1.length := by
            simp only [List.length_cons] at hlen; omega
          have hIH : (L'.map f).prod ≤ (C1.map f).prod := ih C1 hpair' hprime' hfloor' hlen' hG1
          have hnn : 0 ≤ (L'.map f).prod :=
            le_trans (by norm_num) (one_le_listprod_f (fun x hx => (hprime' x hx).two_le))
          have hfc0nn : 0 ≤ f c0 := le_of_lt (f_pos hc0)
          simp only [List.map_cons, List.prod_cons]
          exact mul_le_mul hfa hIH hnn hfc0nn

/-! ### Prime-gap facts for the canonical list `[5,7,11,13,17,19]` -/

lemma gap5 (p : ℕ) (hp : p.Prime) (h : 5 < p) : 7 ≤ p := by
  rcases Nat.lt_or_ge p 7 with h7 | h7
  · interval_cases p
    · exact absurd hp (by decide)
  · exact h7

lemma gap7 (p : ℕ) (hp : p.Prime) (h : 7 < p) : 11 ≤ p := by
  rcases Nat.lt_or_ge p 11 with h11 | h11
  · interval_cases p
    all_goals exact absurd hp (by decide)
  · exact h11

lemma gap11 (p : ℕ) (hp : p.Prime) (h : 11 < p) : 13 ≤ p := by
  rcases Nat.lt_or_ge p 13 with h13 | h13
  · interval_cases p
    all_goals exact absurd hp (by decide)
  · exact h13

lemma gap13 (p : ℕ) (hp : p.Prime) (h : 13 < p) : 17 ≤ p := by
  rcases Nat.lt_or_ge p 17 with h17 | h17
  · interval_cases p
    all_goals exact absurd hp (by decide)
  · exact h17

lemma gap17 (p : ℕ) (hp : p.Prime) (h : 17 < p) : 19 ≤ p := by
  rcases Nat.lt_or_ge p 19 with h19 | h19
  · interval_cases p
    all_goals exact absurd hp (by decide)
  · exact h19

/-- The six smallest primes `≥ 5` form a gap list. -/
lemma gapList_canon : GapList [5, 7, 11, 13, 17, 19] := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_,
          by norm_num, ?_, trivial⟩
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap5 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap7 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap11 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap13 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap17 p hp h
  · intro p hp h c1 hc1; simp at hc1

/-- The canonical product `(5/4)(7/6)(11/10)(13/12)(17/16)(19/18) = 1616615/829440 < 2`. -/
lemma canon_prod_lt_two : (([5, 7, 11, 13, 17, 19] : List ℕ).map f).prod < 2 := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, f]
  norm_num

/-- **Main theorem (unconditional).**  Every odd abundant number coprime to 3 has at
least 7 distinct prime factors.  No enumeration of the 5.4-billion range is used: the
bound comes from the Euler abundancy inequality plus the canonical primorial gap list. -/
theorem odd_abundant_coprime_three_seven_primeFactors
    {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n) :
    7 ≤ n.primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hcard6 : n.primeFactors.card ≤ 6 := by omega
  set S := n.primeFactors with hS
  -- every prime factor is ≥ 5 (odd ⟹ ≠ 2; coprime to 3 ⟹ ≠ 3; prime ≥ 2 ⟹ ≥ 5)
  have hge5 : ∀ p ∈ S, 5 ≤ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨m, hm⟩ := hpn
      omega
    have h3' : p ≠ 3 := by rintro rfl; exact h3 hpn
    have hp2 := hpp.two_le
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · interval_cases p
      · exact absurd rfl h2
      · exact absurd rfl h3'
      · exact absurd hpp (by decide)
    · exact h5
  -- the Euler bound from the companion file
  have hineq : 2 * ∏ p ∈ S, (p - 1) < ∏ p ∈ S, p :=
    abundant_imp_two_mul_prod_sub_one_lt habund
  -- ∏ p/(p-1) equals the product over the sorted list of prime factors
  have hprodF : ((S.sort (· ≤ ·)).map f).prod = ∏ p ∈ S, f p := by
    rw [← Finset.prod_map_toList S f]
    exact List.Perm.prod_eq ((Finset.sort_perm_toList S (· ≤ ·)).map f)
  -- sorted list is strictly increasing
  have hLpair : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
    have hsorted : List.Pairwise (· ≤ ·) (S.sort (· ≤ ·)) := Finset.pairwise_sort S (· ≤ ·)
    have hnodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
    exact (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hLprime : ∀ x ∈ S.sort (· ≤ ·), x.Prime := by
    intro x hx
    rw [Finset.mem_sort] at hx
    exact Nat.prime_of_mem_primeFactors (hS ▸ hx)
  have hLfloor : ∀ x ∈ S.sort (· ≤ ·), ∀ c0 ∈ ([5, 7, 11, 13, 17, 19] : List ℕ).head?, c0 ≤ x := by
    intro x hx c0 hc0
    simp only [List.head?_cons, Option.mem_some_iff] at hc0
    subst hc0
    rw [Finset.mem_sort] at hx
    exact hge5 x hx
  have hLlen : (S.sort (· ≤ ·)).length ≤ ([5, 7, 11, 13, 17, 19] : List ℕ).length := by
    rw [Finset.length_sort]
    simpa using hcard6
  have hdomprod : ((S.sort (· ≤ ·)).map f).prod ≤ (([5, 7, 11, 13, 17, 19] : List ℕ).map f).prod :=
    dom [5, 7, 11, 13, 17, 19] (S.sort (· ≤ ·)) hLpair hLprime hLfloor hLlen gapList_canon
  have hprodlt : (∏ p ∈ S, f p) < 2 := by
    rw [← hprodF]; exact lt_of_le_of_lt hdomprod canon_prod_lt_two
  -- the Euler bound forces the same product to exceed 2
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
  have hgt : 2 < ∏ p ∈ S, f p := lt_of_mul_lt_mul_right key (le_of_lt hMpos)
  linarith [hprodlt, hgt]

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms odd_abundant_coprime_three_seven_primeFactors

end AbundantNumberOQ02OQ01Unconditional
