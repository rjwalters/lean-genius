/-
  **A numeric magnitude lower bound for the smallest odd abundant number coprime to 3.**

  The companion `AbundantNumberOQ02OQ01Unconditional.lean` proves, with no enumeration,
  that every odd abundant number coprime to 3 has at least **7 distinct prime factors**
  (`odd_abundant_coprime_three_seven_primeFactors`).  That is a lower bound on the number
  of prime factors `ω(n)`; this file upgrades it to a lower bound on `n` **itself**:

      n odd, coprime to 3, abundant  ⟹  n ≥ 5·7·11·13·17·19·23 = 37182145.

  The argument is purely structural (no search over the ~5.4·10⁹ range):

  * `ω(n) ≥ 7` (companion) and every prime factor is `≥ 5` (odd ⟹ `≠ 2`, coprime to 3
    ⟹ `≠ 3`).
  * The **radical** `∏_{p∣n} p` divides `n` (`Nat.prod_primeFactors_dvd`), so `n` is at
    least its radical.
  * The radical is the product of `≥ 7` distinct primes, each `≥ 5`; the product of any
    `k` distinct primes `≥ 5` is **minimised** by the `k` smallest, by the same prime-gap
    domination used for the abundancy bound — only here applied to the *raw* product
    (monotone increasing) rather than the weight `p/(p−1)` (antitone).  The seven smallest
    primes `≥ 5` give `5·7·11·13·17·19·23 = 37182145`.

  The new engine `domProd` is the order-dual of the companion's `dom`: along a gap list
  `C` whose entries are forced apart by primality, a strictly increasing list of primes
  that dominates `C` entrywise has product **at least** `C.prod`.

  This is an honest *partial* lower bound: the true minimum `5391411025` is ~145× larger
  (it is not squarefree — the witness is `5²·7·11·13·17·19·23·29`), so closing the gap to
  exact minimality needs the size/exponent structure, not just the radical.  The radical
  bound is the natural structural milestone and is what the prime-count machinery delivers.

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01Unconditional

namespace AbundantNumberOQ02OQ01LowerBound

open AbundantNumberOQ02OQ01Unconditional

/-- The product of a list of primes is at least `1` (each factor is `≥ 2`). -/
lemma one_le_prime_prod : ∀ {L : List ℕ}, (∀ x ∈ L, x.Prime) → 1 ≤ L.prod
  | [], _ => by simp
  | a :: L', h => by
      have h1 : 1 ≤ a := le_trans (by norm_num) (h a (List.mem_cons_self)).two_le
      have h2 : 1 ≤ L'.prod := one_le_prime_prod (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp only [List.prod_cons]
      calc 1 = 1 * 1 := by ring
        _ ≤ a * L'.prod := Nat.mul_le_mul h1 h2

/-- **Raw-product domination (the order-dual of `dom`).**  If `L` is a strictly
increasing list of primes whose entries dominate the corresponding floors of a gap list
`C` (the floors advancing along the gaps), and `C` is no longer than `L`, then the plain
product over `C` is a **lower** bound for the product over `L`.

Where `dom` bounds the antitone weight `∏ p/(p−1)` from above by the *smallest* admissible
primes, `domProd` bounds the monotone product `∏ p` from below by them: the same gap
structure, read in the opposite order. -/
lemma domProd : ∀ (C L : List ℕ),
    L.Pairwise (· < ·) →
    (∀ x ∈ L, x.Prime) →
    (∀ x ∈ L, ∀ c0 ∈ C.head?, c0 ≤ x) →
    C.length ≤ L.length →
    GapList C →
    C.prod ≤ L.prod := by
  intro C L
  induction L generalizing C with
  | nil =>
      intro _ _ _ hlen _
      cases C with
      | nil => simp
      | cons c cs => simp only [List.length_cons, List.length_nil] at hlen; omega
  | cons a L' ih =>
      intro hpair hprime hfloor hlen hG
      cases C with
      | nil =>
          simp only [List.prod_nil]
          exact one_le_prime_prod hprime
      | cons c0 C1 =>
          obtain ⟨_, hgap, hG1⟩ := hG
          have hac0 : c0 ≤ a := hfloor a (List.mem_cons_self) c0 (by simp)
          have hpc := List.pairwise_cons.mp hpair
          have hlt : ∀ x ∈ L', a < x := hpc.1
          have hpair' : L'.Pairwise (· < ·) := hpc.2
          have hprime' : ∀ x ∈ L', x.Prime := fun x hx => hprime x (List.mem_cons_of_mem a hx)
          have hfloor' : ∀ x ∈ L', ∀ c1 ∈ C1.head?, c1 ≤ x := by
            intro x hx c1 hc1
            have hpx : x.Prime := hprime' x hx
            have hc0x : c0 < x := lt_of_le_of_lt hac0 (hlt x hx)
            exact hgap x hpx hc0x c1 hc1
          have hlen' : C1.length ≤ L'.length := by
            simp only [List.length_cons] at hlen; omega
          have hIH : C1.prod ≤ L'.prod := ih C1 hpair' hprime' hfloor' hlen' hG1
          simp only [List.prod_cons]
          exact Nat.mul_le_mul hac0 hIH

/-- The seventh prime gap: no prime lies strictly between `19` and `23`. -/
lemma gap19 (p : ℕ) (hp : p.Prime) (h : 19 < p) : 23 ≤ p := by
  rcases Nat.lt_or_ge p 23 with h23 | h23
  · interval_cases p
    all_goals exact absurd hp (by decide)
  · exact h23

/-- The seven smallest primes `≥ 5` form a gap list. -/
lemma gapList_canon7 : GapList [5, 7, 11, 13, 17, 19, 23] := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_, by norm_num, ?_,
          by norm_num, ?_, by norm_num, ?_, trivial⟩
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap5 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap7 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap11 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap13 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap17 p hp h
  · intro p hp h c1 hc1; simp only [List.head?_cons, Option.mem_some_iff] at hc1; subst hc1; exact gap19 p hp h
  · intro p hp h c1 hc1; simp at hc1

/-- The canonical radical lower bound `5·7·11·13·17·19·23 = 37182145`. -/
lemma canon7_prod : ([5, 7, 11, 13, 17, 19, 23] : List ℕ).prod = 37182145 := by decide

/-- **Main theorem.**  Every odd abundant number coprime to 3 is at least `37182145`
(the product of the seven smallest primes `≥ 5`).  Derived structurally from the
`≥ 7`-prime-factors bound and the radical-divides-`n` fact, with no enumeration. -/
theorem odd_abundant_coprime_three_ge
    {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n) :
    37182145 ≤ n := by
  have h7 := odd_abundant_coprime_three_seven_primeFactors hodd h3 habund
  -- `ω(n) ≥ 7 > 0`, so `n ≠ 0`.
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.primeFactors_zero, Finset.card_empty] at h7
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  set S := n.primeFactors with hS
  -- every prime factor is `≥ 5` (odd ⟹ `≠ 2`; coprime to 3 ⟹ `≠ 3`).
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
  -- the sorted prime-factor list is strictly increasing, all prime, ≥ 5, length ≥ 7.
  have hLpair : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
    have hsorted : List.Pairwise (· ≤ ·) (S.sort (· ≤ ·)) := Finset.pairwise_sort S (· ≤ ·)
    have hnodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
    exact (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hLprime : ∀ x ∈ S.sort (· ≤ ·), x.Prime := by
    intro x hx
    rw [Finset.mem_sort] at hx
    exact Nat.prime_of_mem_primeFactors (hS ▸ hx)
  have hLfloor : ∀ x ∈ S.sort (· ≤ ·), ∀ c0 ∈ ([5, 7, 11, 13, 17, 19, 23] : List ℕ).head?, c0 ≤ x := by
    intro x hx c0 hc0
    simp only [List.head?_cons, Option.mem_some_iff] at hc0
    subst hc0
    rw [Finset.mem_sort] at hx
    exact hge5 x hx
  have hLlen : ([5, 7, 11, 13, 17, 19, 23] : List ℕ).length ≤ (S.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]
    simpa using h7
  -- raw-product domination: radical ≥ product of the seven smallest primes ≥ 5.
  have hdom : ([5, 7, 11, 13, 17, 19, 23] : List ℕ).prod ≤ (S.sort (· ≤ ·)).prod :=
    domProd [5, 7, 11, 13, 17, 19, 23] (S.sort (· ≤ ·)) hLpair hLprime hLfloor hLlen gapList_canon7
  rw [canon7_prod] at hdom
  -- the sorted list product is the radical `∏_{p∣n} p`.
  have hprodList : (S.sort (· ≤ ·)).prod = ∏ p ∈ S, p := by
    have h1 : (S.sort (· ≤ ·)).prod = S.toList.prod :=
      List.Perm.prod_eq (Finset.sort_perm_toList S (· ≤ ·))
    have h2 : S.toList.prod = ∏ p ∈ S, p := by
      simpa using Finset.prod_map_toList S (fun p => p)
    rw [h1]; exact h2
  rw [hprodList] at hdom
  -- the radical divides `n`, so `n ≥ radical ≥ 37182145`.
  have hdvd : (∏ p ∈ S, p) ∣ n := hS ▸ Nat.prod_primeFactors_dvd n
  have hle : (∏ p ∈ S, p) ≤ n := Nat.le_of_dvd hnpos hdvd
  omega

#check @domProd
#check @odd_abundant_coprime_three_ge

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms odd_abundant_coprime_three_ge

end AbundantNumberOQ02OQ01LowerBound
