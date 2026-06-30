/-
  **The smallest SQUAREFREE odd abundant number coprime to 3 — exactly resolved.**

  The companion files settle the general (not-necessarily-squarefree) case for odd
  abundant numbers coprime to 3:
  `AbundantNumberOQ02OQ01Unconditional.lean` proves `ω(n) ≥ 7` and
  `AbundantNumberOQ02OQ01LowerBound.lean` upgrades it to the *radical* magnitude bound
  `n ≥ 5·7·11·13·17·19·23 = 37182145`.  The true overall minimum, `5391411025 =
  5²·7·11·13·17·19·23·29`, is larger precisely because it is **not** squarefree: the
  repeated prime `5²` buys extra abundancy cheaply, letting the witness use only 8 primes.

  This file isolates the **squarefree boundary phenomenon** and resolves it *exactly*.
  Forbidding repeated prime factors removes the exponent-boosting trick, so the abundancy
  index of a squarefree `n` coprime to 6 is the strictly smaller product `∏_{p∣n}(p+1)/p`
  (rather than the Euler envelope `∏ p/(p−1)`).  The eight smallest primes `≥ 5` give

      (6/5)(8/7)(12/11)(14/13)(18/17)(20/19)(24/23)(30/29) = 2090188800/1078282205 ≈ 1.938 < 2,

  so **a squarefree odd abundant number coprime to 3 has at least 9 distinct prime factors**
  (`squarefree_odd_abundant_coprime_three_nine_primeFactors`) — strictly more than the
  general bound of 7.  Since for squarefree `n` the radical equals `n`, the magnitude bound
  is then sharp:

      n squarefree, odd, coprime to 3, abundant  ⟹  n ≥ 5·7·11·13·17·19·23·29·31 = 33426748355,

  and `33426748355` itself *is* squarefree, odd, coprime to 3 and abundant
  (`σ = 6·8·12·14·18·20·24·30·32 = 66886041600 > 66853496710 = 2n`).  Hence

      IsLeast { n | Squarefree n ∧ Odd n ∧ ¬3∣n ∧ Abundant n } 33426748355
        (`squarefree_odd_abundant_coprime_three_least`).

  Engine reuse: the abundancy/extremal machinery (`GapList`, `dom`-style domination,
  `domProd`, the prime-gap facts `gap5 … gap19`) comes verbatim from the companion files.
  The genuinely new ingredients are the squarefree divisor-sum identity
  `σ(n) = ∏_{p∣n}(p+1)`, the antitone weight `g p = (p+1)/p` with its own domination
  lemma `domg`, two further prime gaps (`gap23`, `gap29`), and the witness verification.

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01LowerBound

namespace AbundantNumberOQ02OQ01Squarefree

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma
open AbundantNumberOQ02OQ01Unconditional
open AbundantNumberOQ02OQ01LowerBound

/-! ### The squarefree divisor-sum identity `σ(n) = ∏_{p∣n}(p+1)` -/

/-- For squarefree `n`, the sum-of-divisors function factors as `σ(n) = ∏_{p∣n}(p+1)`.
Each prime power in `n` is a single prime (`vₚ(n) = 1`), whose `σ` is `1 + p = p + 1`. -/
theorem sigma_one_squarefree {n : ℕ} (hsf : Squarefree n) :
    σ 1 n = ∏ p ∈ n.primeFactors, (p + 1) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hsf.ne_zero]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hf1 : n.factorization p = 1 := Nat.factorization_eq_one_of_squarefree hsf hpp hpd
  rw [hf1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_one, pow_zero, pow_one, zero_add]
  ring

/-! ### The antitone abundancy weight `g p = (p+1)/p` -/

/-- The decreasing weight `g p = (p+1)/p` over ℚ (the per-prime factor of `σ(n)/n` for
squarefree `n`).  It is strictly smaller than the Euler weight `p/(p−1)`. -/
def g (p : ℕ) : ℚ := ((p : ℚ) + 1) / (p : ℚ)

lemma g_pos {p : ℕ} (hp : 2 ≤ p) : 0 < g p := by
  have hpc : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  unfold g
  exact div_pos (by linarith) (by linarith)

lemma one_le_g {p : ℕ} (hp : 2 ≤ p) : 1 ≤ g p := by
  have hpc : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hpos : (0 : ℚ) < (p : ℚ) := by linarith
  unfold g
  rw [le_div_iff₀ hpos]
  linarith

/-- `g` is antitone on `{p ≥ 2}`: larger primes give smaller weight `(p+1)/p`. -/
lemma g_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : g b ≤ g a := by
  have hac : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hbc : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  have hpa : (0 : ℚ) < (a : ℚ) := by linarith
  have hpb : (0 : ℚ) < (b : ℚ) := by linarith
  unfold g
  rw [div_le_div_iff₀ hpb hpa]
  nlinarith [hbc]

/-- The product of weights `g` over a list of integers all `≥ 2` is `≥ 1`. -/
lemma one_le_listprod_g : ∀ {C : List ℕ}, (∀ c ∈ C, 2 ≤ c) → 1 ≤ (C.map g).prod
  | [], _ => by simp
  | c :: rest, h => by
      simp only [List.map_cons, List.prod_cons]
      have h1 : 1 ≤ g c := one_le_g (h c (List.mem_cons_self))
      have h2 : 1 ≤ (rest.map g).prod := one_le_listprod_g (fun x hx => h x (List.mem_cons_of_mem c hx))
      nlinarith [h1, h2]

/-- **Domination lemma for the squarefree weight `g`** (mirror of the companion's `dom`).
If `L` is a strictly increasing list of primes dominating the floors of a gap list `C`, and
`L` is no longer than `C`, then `∏ g` over `L` is bounded above by `∏ g` over `C`. -/
lemma domg : ∀ (C L : List ℕ),
    L.Pairwise (· < ·) →
    (∀ x ∈ L, x.Prime) →
    (∀ x ∈ L, ∀ c0 ∈ C.head?, c0 ≤ x) →
    L.length ≤ C.length →
    GapList C →
    (L.map g).prod ≤ (C.map g).prod := by
  intro C L
  induction L generalizing C with
  | nil =>
      intro _ _ _ _ hG
      simp only [List.map_nil, List.prod_nil]
      exact one_le_listprod_g (gapList_all_ge_two hG)
  | cons a L' ih =>
      intro hpair hprime hfloor hlen hG
      cases C with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons c0 C1 =>
          obtain ⟨hc0, hgap, hG1⟩ := hG
          have hac0 : c0 ≤ a := hfloor a (List.mem_cons_self) c0 (by simp)
          have hga : g a ≤ g c0 := g_antitone hc0 hac0
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
          have hIH : (L'.map g).prod ≤ (C1.map g).prod := ih C1 hpair' hprime' hfloor' hlen' hG1
          have hnn : 0 ≤ (L'.map g).prod :=
            le_trans (by norm_num) (one_le_listprod_g (fun x hx => (hprime' x hx).two_le))
          have hgc0nn : 0 ≤ g c0 := le_of_lt (g_pos hc0)
          simp only [List.map_cons, List.prod_cons]
          exact mul_le_mul hga hIH hnn hgc0nn

/-! ### Two further prime gaps and the canonical gap lists -/

/-- No prime lies strictly between `23` and `29`. -/
lemma gap23 (p : ℕ) (hp : p.Prime) (h : 23 < p) : 29 ≤ p := by
  rcases Nat.lt_or_ge p 29 with h29 | h29
  · interval_cases p
    all_goals exact absurd hp (by decide)
  · exact h29

/-- No prime lies strictly between `29` and `31`. -/
lemma gap29 (p : ℕ) (hp : p.Prime) (h : 29 < p) : 31 ≤ p := by
  rcases Nat.lt_or_ge p 31 with h31 | h31
  · interval_cases p
    all_goals exact absurd hp (by decide)
  · exact h31

/-- The eight smallest primes `≥ 5` form a gap list. -/
lemma gapList8 : GapList [5, 7, 11, 13, 17, 19, 23, 29] := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_,
          by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, trivial⟩
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap5 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap7 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap11 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap13 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap17 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap19 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap23 p hp h
  · intro p hp h c1 hc1; simp at hc1

/-- The nine smallest primes `≥ 5` form a gap list. -/
lemma gapList9 : GapList [5, 7, 11, 13, 17, 19, 23, 29, 31] := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_,
          by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, trivial⟩
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap5 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap7 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap11 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap13 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap17 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap19 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap23 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap29 p hp h
  · intro p hp h c1 hc1; simp at hc1

/-- The canonical squarefree-abundancy product over the eight smallest primes `≥ 5`:
`(6/5)(8/7)(12/11)(14/13)(18/17)(20/19)(24/23)(30/29) = 2090188800/1078282205 < 2`. -/
lemma canon8_g_prod_lt_two :
    (([5, 7, 11, 13, 17, 19, 23, 29] : List ℕ).map g).prod < 2 := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, g]
  norm_num

/-- The product of the nine smallest primes `≥ 5` is `33426748355`. -/
lemma canon9_prod : ([5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).prod = 33426748355 := by
  decide

/-! ### Lower bound on the number of prime factors (the sharp count) -/

/-- **Main lower bound on `ω`.**  Every *squarefree* odd abundant number coprime to 3 has
at least **9** distinct prime factors — strictly more than the general bound of 7.  The
extra two come from squarefreeness: with no repeated primes the abundancy index is the
smaller product `∏ (p+1)/p`, and the eight smallest primes `≥ 5` already fall short of 2. -/
theorem squarefree_odd_abundant_coprime_three_nine_primeFactors
    {n : ℕ} (hsf : Squarefree n) (hodd : Odd n) (h3 : ¬ (3 ∣ n))
    (habund : Nat.Abundant n) :
    9 ≤ n.primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hcard8 : n.primeFactors.card ≤ 8 := by omega
  set S := n.primeFactors with hS
  -- every prime factor is ≥ 5 (odd ⟹ ≠ 2; coprime to 3 ⟹ ≠ 3)
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
  -- squarefree abundancy: `2 · ∏ p < ∏ (p+1)` over ℕ
  have hσeq : σ 1 n = ∏ p ∈ S, (p + 1) := sigma_one_squarefree hsf
  have hpe : ∏ p ∈ S, p = n := prod_primeFactors_of_squarefree hsf
  have h2lt : 2 * n < σ 1 n := by
    have : Nat.Abundant n ↔ 2 * n < σ 1 n := by
      rw [Nat.Abundant, sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
      omega
    exact this.mp habund
  have hNN : 2 * ∏ p ∈ S, p < ∏ p ∈ S, (p + 1) := by
    rw [hpe, ← hσeq]; exact h2lt
  -- cast to ℚ and assemble the abundancy index `∏ g`
  have hDpos : 0 < ∏ p ∈ S, (p : ℚ) := by
    apply Finset.prod_pos
    intro p hp
    have : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hge5 p hp
    linarith
  have hg_eq : (∏ p ∈ S, g p) = (∏ p ∈ S, ((p : ℚ) + 1)) / (∏ p ∈ S, (p : ℚ)) := by
    simp only [g]; rw [Finset.prod_div_distrib]
  have hcastNum : ((∏ p ∈ S, (p + 1) : ℕ) : ℚ) = ∏ p ∈ S, ((p : ℚ) + 1) := by
    rw [Nat.cast_prod]; refine Finset.prod_congr rfl (fun p _ => ?_); push_cast; ring
  have hcastDen : ((∏ p ∈ S, p : ℕ) : ℚ) = ∏ p ∈ S, (p : ℚ) := by rw [Nat.cast_prod]
  have hQ : 2 * (∏ p ∈ S, (p : ℚ)) < ∏ p ∈ S, ((p : ℚ) + 1) := by
    have hc : ((2 * ∏ p ∈ S, p : ℕ) : ℚ) < ((∏ p ∈ S, (p + 1) : ℕ) : ℚ) := by exact_mod_cast hNN
    rwa [Nat.cast_mul, Nat.cast_ofNat, hcastDen, hcastNum] at hc
  have key : 2 * (∏ p ∈ S, (p : ℚ)) < (∏ p ∈ S, g p) * (∏ p ∈ S, (p : ℚ)) := by
    have heq : (∏ p ∈ S, g p) * (∏ p ∈ S, (p : ℚ)) = ∏ p ∈ S, ((p : ℚ) + 1) := by
      rw [hg_eq, div_mul_cancel₀]; exact ne_of_gt hDpos
    rw [heq]; exact hQ
  have hgt : 2 < ∏ p ∈ S, g p := lt_of_mul_lt_mul_right key (le_of_lt hDpos)
  -- extremal upper bound via `domg`: `∏ g ≤ canon8 < 2`, contradiction
  have hprodF : ((S.sort (· ≤ ·)).map g).prod = ∏ p ∈ S, g p := by
    rw [← Finset.prod_map_toList S g]
    exact List.Perm.prod_eq ((Finset.sort_perm_toList S (· ≤ ·)).map g)
  have hLpair : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
    have hsorted : List.Pairwise (· ≤ ·) (S.sort (· ≤ ·)) := Finset.pairwise_sort S (· ≤ ·)
    have hnodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
    exact (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hLprime : ∀ x ∈ S.sort (· ≤ ·), x.Prime := by
    intro x hx
    rw [Finset.mem_sort] at hx
    exact Nat.prime_of_mem_primeFactors (hS ▸ hx)
  have hLfloor : ∀ x ∈ S.sort (· ≤ ·),
      ∀ c0 ∈ ([5, 7, 11, 13, 17, 19, 23, 29] : List ℕ).head?, c0 ≤ x := by
    intro x hx c0 hc0
    simp only [List.head?_cons, Option.mem_some_iff] at hc0
    subst hc0
    rw [Finset.mem_sort] at hx
    exact hge5 x hx
  have hLlen : (S.sort (· ≤ ·)).length ≤ ([5, 7, 11, 13, 17, 19, 23, 29] : List ℕ).length := by
    rw [Finset.length_sort]; simpa using hcard8
  have hdomprod :
      ((S.sort (· ≤ ·)).map g).prod ≤ (([5, 7, 11, 13, 17, 19, 23, 29] : List ℕ).map g).prod :=
    domg [5, 7, 11, 13, 17, 19, 23, 29] (S.sort (· ≤ ·)) hLpair hLprime hLfloor hLlen gapList8
  have hprodlt : (∏ p ∈ S, g p) < 2 := by
    rw [← hprodF]; exact lt_of_le_of_lt hdomprod canon8_g_prod_lt_two
  linarith [hprodlt, hgt]

/-! ### Sharp magnitude lower bound (radical = n for squarefree) -/

/-- **Sharp magnitude lower bound.**  Every squarefree odd abundant number coprime to 3 is
at least `5·7·11·13·17·19·23·29·31 = 33426748355`.  For squarefree `n` the radical equals
`n`, so the `≥ 9`-prime-factors bound translates directly into this magnitude bound — and it
is *attained* (see `squarefree_odd_abundant_coprime_three_least`). -/
theorem squarefree_odd_abundant_coprime_three_ge
    {n : ℕ} (hsf : Squarefree n) (hodd : Odd n) (h3 : ¬ (3 ∣ n))
    (habund : Nat.Abundant n) :
    33426748355 ≤ n := by
  have h9 := squarefree_odd_abundant_coprime_three_nine_primeFactors hsf hodd h3 habund
  set S := n.primeFactors with hS
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
  have hLpair : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
    have hsorted : List.Pairwise (· ≤ ·) (S.sort (· ≤ ·)) := Finset.pairwise_sort S (· ≤ ·)
    have hnodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
    exact (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hLprime : ∀ x ∈ S.sort (· ≤ ·), x.Prime := by
    intro x hx
    rw [Finset.mem_sort] at hx
    exact Nat.prime_of_mem_primeFactors (hS ▸ hx)
  have hLfloor : ∀ x ∈ S.sort (· ≤ ·),
      ∀ c0 ∈ ([5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).head?, c0 ≤ x := by
    intro x hx c0 hc0
    simp only [List.head?_cons, Option.mem_some_iff] at hc0
    subst hc0
    rw [Finset.mem_sort] at hx
    exact hge5 x hx
  have hLlen :
      ([5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).length ≤ (S.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; simpa using h9
  have hdom :
      ([5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).prod ≤ (S.sort (· ≤ ·)).prod :=
    domProd [5, 7, 11, 13, 17, 19, 23, 29, 31] (S.sort (· ≤ ·)) hLpair hLprime hLfloor hLlen gapList9
  rw [canon9_prod] at hdom
  have hprodList : (S.sort (· ≤ ·)).prod = ∏ p ∈ S, p := by
    have h1 : (S.sort (· ≤ ·)).prod = S.toList.prod :=
      List.Perm.prod_eq (Finset.sort_perm_toList S (· ≤ ·))
    have h2 : S.toList.prod = ∏ p ∈ S, p := by
      simpa using Finset.prod_map_toList S (fun p => p)
    rw [h1]; exact h2
  rw [hprodList] at hdom
  have hpe : ∏ p ∈ S, p = n := prod_primeFactors_of_squarefree hsf
  rw [hpe] at hdom
  exact hdom

/-! ### The witness `33426748355 = 5·7·11·13·17·19·23·29·31` -/

/-- The witness number `W = 5·7·11·13·17·19·23·29·31`. -/
abbrev W : ℕ := 33426748355

/-- `σ₁` of the nine small primes, by direct reduction of each divisor sum. -/
theorem sigma_5  : σ 1 5  = 6  := by rw [sigma_one_apply]; decide
theorem sigma_7  : σ 1 7  = 8  := by rw [sigma_one_apply]; decide
theorem sigma_11 : σ 1 11 = 12 := by rw [sigma_one_apply]; decide
theorem sigma_13 : σ 1 13 = 14 := by rw [sigma_one_apply]; decide
theorem sigma_17 : σ 1 17 = 18 := by rw [sigma_one_apply]; decide
theorem sigma_19 : σ 1 19 = 20 := by rw [sigma_one_apply]; decide
theorem sigma_23 : σ 1 23 = 24 := by rw [sigma_one_apply]; decide
theorem sigma_29 : σ 1 29 = 30 := by rw [sigma_one_apply]; decide
theorem sigma_31 : σ 1 31 = 32 := by rw [sigma_one_apply]; decide

/-- **The divisor sum of the witness.**  `σ(33426748355) = 66886041600`, computed from
the prime factorisation via multiplicativity of `σ` (no `native_decide`). -/
theorem sigma_W : σ 1 W = 66886041600 := by
  have e : (W : ℕ) = 5 * (7 * (11 * (13 * (17 * (19 * (23 * (29 * 31))))))) := by norm_num
  rw [e,
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    sigma_5, sigma_7, sigma_11, sigma_13, sigma_17, sigma_19, sigma_23, sigma_29, sigma_31]
  norm_num

/-- **`33426748355` is squarefree** (a product of distinct primes). -/
theorem squarefree_W : Squarefree W := by
  have e : (W : ℕ) = 5 * (7 * (11 * (13 * (17 * (19 * (23 * (29 * 31))))))) := by norm_num
  rw [e]
  have sp : ∀ p : ℕ, p.Prime → Squarefree p := fun p hp => hp.prime.squarefree
  refine (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 5 (by norm_num), ?_⟩
  refine (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 7 (by norm_num), ?_⟩
  refine (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 11 (by norm_num), ?_⟩
  refine (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 13 (by norm_num), ?_⟩
  refine (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 17 (by norm_num), ?_⟩
  refine (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 19 (by norm_num), ?_⟩
  refine (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 23 (by norm_num), ?_⟩
  exact (Nat.squarefree_mul (by norm_num)).mpr ⟨sp 29 (by norm_num), sp 31 (by norm_num)⟩

/-- **`33426748355` is odd.** -/
theorem odd_W : Odd W := by decide

/-- **`33426748355` is not divisible by 3.** -/
theorem not_three_dvd_W : ¬ (3 ∣ W) := by decide

/-- **`33426748355` is abundant.**  `σ(W) = 66886041600 > 66853496710 = 2W`. -/
theorem abundant_W : Nat.Abundant W := by
  have hiff : Nat.Abundant W ↔ 2 * W < σ 1 W := by
    rw [Nat.Abundant, sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega
  rw [hiff, sigma_W]
  norm_num

/-! ### The exact minimum -/

/-- **The smallest squarefree odd abundant number coprime to 3 is exactly `33426748355`.**
Combining the sharp lower bound with the witness gives the least element of the set of
squarefree odd abundant numbers coprime to 3 — the squarefree analogue of the (still open)
unrestricted minimum `5391411025`. -/
theorem squarefree_odd_abundant_coprime_three_least :
    IsLeast {n : ℕ | Squarefree n ∧ Odd n ∧ ¬ (3 ∣ n) ∧ Nat.Abundant n} 33426748355 := by
  constructor
  · exact ⟨squarefree_W, odd_W, not_three_dvd_W, abundant_W⟩
  · rintro m ⟨hsf, hodd, h3, hab⟩
    exact squarefree_odd_abundant_coprime_three_ge hsf hodd h3 hab

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms squarefree_odd_abundant_coprime_three_nine_primeFactors
#print axioms squarefree_odd_abundant_coprime_three_least

end AbundantNumberOQ02OQ01Squarefree
