/-
  Abundant numbers OQ03-OQ03 satellite: infinitely many odd primitive
  abundant numbers with **least prime factor 3**.

  The parent entry (`AbundantNumberOQ03OQ03.lean`, PR #43297) proved
  `OddPrimitiveAbundant.Infinite` via first-crossing products of consecutive
  primes `p_a ⋯ p_{b-1}`.  That family is squarefree and its witnesses have
  *distinct* least prime factors (`p_a` grows with the start `a`), so it says
  nothing about how many odd primitive abundants share a FIXED least prime.
  The tracker recorded the natural follow-up: are there infinitely many with
  least prime factor `3` (the smallest possible, attained by `945 = 3³·5·7`)?
  This requires a **non-squarefree** family — with the least prime pinned,
  fresh witnesses must differ somewhere else, and the only lever left is the
  exponent of `3`.

  ## The construction

  For each `j ≥ 1`, take

      `N_j  =  3^j · p_a · p_{a+1} ⋯ p_{b-1}`,   `a = a(j) := 3·σ(3^j)`,

  where `p_i` is the `i`-th prime (`Nat.nth`-indexed) and `b` is the FIRST
  index at which the product becomes abundant (a crossing exists because
  `∑ 1/p` diverges — inherited from the parent's `exists_crossing`).  The two
  witness-shaping choices:

  * **Grow the head, not the tail**: the `3`-exponent `j` is the family
    parameter, so `v₃(N_j) = j` pins distinct witnesses with the same least
    prime `3`.
  * **Start the tail beyond `3·σ(3^j)`**: the delicate maximal divisor is now
    `N_j / 3` (absent in the squarefree case), whose abundancy deficit against
    `N_j` is only the factor `σ(3^j)/(3·σ(3^{j-1})) = 1 + 2/(3^{j+1}-3)`.
    First-crossing minimality bounds the overshoot of `N_j` by the last tail
    prime's factor `1 + 1/q`, so `N_j / 3` stays deficient exactly when
    `q ≥ 3·σ(3^{j-1})` — guaranteed by starting the tail at index
    `a = 3·σ(3^j) > 3·σ(3^{j-1})` (the `i`-th prime is `≥ i`).

  Primitivity then follows the parent's blueprint: the tail maximal divisors
  `N_j / p_i` are deficient by the swap argument (a smaller omitted prime only
  helps), `σ = 2n` is excluded at the predecessor (`4 ∣ σ` vs `2n ≡ 2 mod 4`
  for `≥ 2` tail primes; a direct arithmetic contradiction for `≤ 1`), and
  deficiency is divisor-inherited.

  ## Results

  * `two_mul_sum_divisors_pow_three`     — `2·σ(3^j) + 1 = 3^(j+1)`
    (subtraction-safe geometric closed form).
  * `sum_divisors_pow_three_mul_prod`    — `σ(3^j · ∏ p_i) = σ(3^j) · ∏ (p_i+1)`.
  * `sum_divisors_pow_three_mul_prod_ne_two_mul` — `σ ≠ 2n` for `3^j` times a
    product of nth-primes with indices `≥ 2` (the non-squarefree exclusion).
  * `head_shrink_deficient`              — the NEW maximal divisor `N_j / 3` is
    deficient (this is where `a(j) = 3·σ(3^j)` earns its keep).
  * `witnessThree_erase_deficient`       — the tail maximal divisors `N_j / p_i`
    are deficient (parent's swap argument with the `3^j` head riding along).
  * `witnessThree_spec`                  — `N_j` is odd primitive abundant with
    `minFac = 3`.
  * `witnessThree_injective`             — `j ↦ N_j` is injective (`v₃ = j`).
  * `oddPrimitiveAbundantLeastThree_infinite` — **headline**: the odd primitive
    abundant numbers with least prime factor `3` form an infinite set.

  All results are fully machine-checked (0 axioms, 0 sorries).  The one
  analytic input is Mathlib's divergence of `∑ 1/p`, reused through the
  parent's `exists_crossing`.

  Reference: OEIS A006038 (odd primitive abundant numbers).  Parent:
  `abundant-number-oq-03-oq-03` (infinitude, PR #43297); sibling satellite:
  `AbundantNumberOQ03OQ03OmegaThree.lean` (`ω(n) ≥ 3` for odd abundants).
-/
import Mathlib
import Proofs.AbundantNumberOQ03OQ03
import Proofs.AbundantNumberOQ03OQ03OmegaThree

namespace AbundantNumberOQ03OQ03

open Nat Finset

-- ============================================================
-- σ(3^j) arithmetic: the subtraction-safe geometric closed form
-- ============================================================

/-- **Closed form for `σ(3^j)`, subtraction-safe**: `2·σ(3^j) + 1 = 3^(j+1)`.
Specializes the sibling satellite's geometric-sum identity
`pred_mul_geom_sum_add_one` to `p = 3` through
`Nat.sum_divisors_prime_pow`. -/
theorem two_mul_sum_divisors_pow_three (j : ℕ) :
    2 * (∑ d ∈ ((3 : ℕ) ^ j).divisors, d) + 1 = 3 ^ (j + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_three]
  have h := pred_mul_geom_sum_add_one (p := 3) (by norm_num) j
  simpa using h

-- ============================================================
-- The tail: products of nth-primes with indices ≥ 2
-- ============================================================

/-- `3` does not divide a product of `nth`-indexed primes with all indices
`≥ 2`: `3 = p₁`, and `nth` is injective. -/
theorem three_not_dvd_prod_nth {s : Finset ℕ} (hs : ∀ i ∈ s, 2 ≤ i) :
    ¬ (3 : ℕ) ∣ ∏ i ∈ s, Nat.nth Nat.Prime i := by
  intro h
  obtain ⟨i, hi, hdvd⟩ := (Nat.prime_three.prime.dvd_finsetProd_iff _).mp h
  have heq : (3 : ℕ) = Nat.nth Nat.Prime i :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Nat.prime_nth_prime i)).mp hdvd
  have h1 : Nat.nth Nat.Prime 1 = Nat.nth Nat.Prime i := by
    rw [Nat.nth_prime_one_eq_three]; exact heq
  have := Nat.nth_injective Nat.infinite_setOf_prime h1
  have := hs i hi
  omega

/-- **σ closed form for `3^j` times a tail of nth-primes** (indices `≥ 2`,
so the tail is coprime to `3`): `σ(3^j · ∏ pᵢ) = σ(3^j) · ∏ (pᵢ + 1)`.
The non-squarefree extension of the parent's `sum_divisors_prod_nth`. -/
theorem sum_divisors_pow_three_mul_prod {j : ℕ} {s : Finset ℕ}
    (hs : ∀ i ∈ s, 2 ≤ i) :
    ∑ d ∈ ((3 : ℕ) ^ j * ∏ i ∈ s, Nat.nth Nat.Prime i).divisors, d
      = (∑ d ∈ ((3 : ℕ) ^ j).divisors, d) * ∏ i ∈ s, (Nat.nth Nat.Prime i + 1) := by
  have h3 : ¬ (3 : ℕ) ∣ ∏ i ∈ s, Nat.nth Nat.Prime i := three_not_dvd_prod_nth hs
  have hcop : Nat.Coprime ((3 : ℕ) ^ j) (∏ i ∈ s, Nat.nth Nat.Prime i) :=
    Nat.Coprime.pow_left _ (Nat.prime_three.coprime_iff_not_dvd.mpr h3)
  rw [hcop.sum_divisors_mul, sum_divisors_prod_nth]

/-- **`σ = 2n` is impossible for `3^j` times a tail of nth-primes** (indices
`≥ 2`).  Three cases on the tail size: empty — `σ(3^j) = 2·3^j` contradicts
the closed form; one prime `q` — the equation forces `3·3^j = 3^j·q + q + 1`,
impossible for `q ≥ 4`; two or more primes — `4 ∣ σ(n)` (two even factors
`pᵢ + 1`) while `2n ≡ 2 [MOD 4]` since `n` is odd.  The non-squarefree
analogue of the parent's `sum_divisors_prod_nth_ne_two_mul`, needed to
sharpen crossing minimality from `≤` to strict deficiency. -/
theorem sum_divisors_pow_three_mul_prod_ne_two_mul {j : ℕ} {s : Finset ℕ}
    (hs : ∀ i ∈ s, 2 ≤ i) :
    (∑ d ∈ ((3 : ℕ) ^ j).divisors, d) * ∏ i ∈ s, (Nat.nth Nat.Prime i + 1)
      ≠ 2 * ((3 : ℕ) ^ j * ∏ i ∈ s, Nat.nth Nat.Prime i) := by
  intro h
  have hid := two_mul_sum_divisors_pow_three j
  have hps : (3 : ℕ) ^ (j + 1) = 3 * 3 ^ j := by ring
  rw [hps] at hid
  have hx : 1 ≤ (3 : ℕ) ^ j := Nat.one_le_pow _ _ (by norm_num)
  rcases Nat.lt_or_ge s.card 2 with hcard | hcard
  · interval_cases hc : s.card
    · -- empty tail: σ(3^j) = 2·3^j against 2σ(3^j) + 1 = 3·3^j
      rw [Finset.card_eq_zero] at hc
      subst hc
      simp only [Finset.prod_empty, mul_one] at h
      omega
    · -- one tail prime q ≥ 4: forces 3·3^j = 3^j·q + q + 1, impossible
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      simp only [Finset.prod_singleton] at h
      have hi2 : 2 ≤ i := hs i (Finset.mem_singleton_self i)
      have hq4 : 4 ≤ Nat.nth Nat.Prime i := by
        have h13 : Nat.nth Nat.Prime 1 < Nat.nth Nat.Prime i :=
          (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (by omega)
        rw [Nat.nth_prime_one_eq_three] at h13
        omega
      set q := Nat.nth Nat.Prime i with hqdef
      set x := (3 : ℕ) ^ j with hxdef
      set σ3 := ∑ d ∈ ((3 : ℕ) ^ j).divisors, d with hσdef
      -- h : σ3·(q+1) = 2·(x·q), hid : 2σ3 + 1 = 3x
      have hsum : 4 * (x * q) + (q + 1) = 3 * x * (q + 1) := by
        have e1 : (2 * σ3 + 1) * (q + 1) = 3 * x * (q + 1) := by rw [hid]
        calc 4 * (x * q) + (q + 1)
            = 2 * (σ3 * (q + 1)) + (q + 1) := by rw [h]; ring
          _ = (2 * σ3 + 1) * (q + 1) := by ring
          _ = 3 * x * (q + 1) := e1
      have hxq : x * 4 ≤ x * q := Nat.mul_le_mul_left x hq4
      nlinarith [hsum, hxq, hx]
  · -- ≥ 2 tail primes: 4 ∣ σ(n) but 2n ≡ 2 [MOD 4]
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
    have hoddnth : ∀ w ∈ s, Odd (Nat.nth Nat.Prime w) := by
      intro w hw
      refine (Nat.prime_nth_prime w).odd_of_ne_two fun he => ?_
      have h0 : Nat.nth Nat.Prime 0 = Nat.nth Nat.Prime w := by
        rw [Nat.nth_prime_zero_eq_two, he]
      have := Nat.nth_injective Nat.infinite_setOf_prime h0
      have := hs w hw
      omega
    have h4 : 4 ∣ ∏ i ∈ s, (Nat.nth Nat.Prime i + 1) := by
      have hsub : ({u, v} : Finset ℕ) ⊆ s := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hu
        · exact Finset.mem_singleton.mp hw ▸ hv
      have hpair : ∏ i ∈ ({u, v} : Finset ℕ), (Nat.nth Nat.Prime i + 1)
          = (Nat.nth Nat.Prime u + 1) * (Nat.nth Nat.Prime v + 1) :=
        Finset.prod_pair huv
      have hdvd4 : 4 ∣ (Nat.nth Nat.Prime u + 1) * (Nat.nth Nat.Prime v + 1) := by
        obtain ⟨x, hx⟩ := hoddnth u hu
        obtain ⟨y, hy⟩ := hoddnth v hv
        exact ⟨(x + 1) * (y + 1), by rw [hx, hy]; ring⟩
      exact dvd_trans (hpair ▸ hdvd4) (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    have h4σ : 4 ∣ 2 * ((3 : ℕ) ^ j * ∏ i ∈ s, Nat.nth Nat.Prime i) := by
      rw [← h]
      exact h4.mul_left _
    have hodd : Odd ((3 : ℕ) ^ j * ∏ i ∈ s, Nat.nth Nat.Prime i) := by
      refine (Odd.pow (by decide : Odd 3)).mul (odd_prod_nth fun i hi => ?_)
      have := hs i hi; omega
    obtain ⟨w, hw⟩ := hodd
    omega

-- ============================================================
-- The witness family: 3^j times a first-crossing tail
-- ============================================================

/-- **The tail start index** `a(j) = 3·σ(3^j)`.  Starting the tail this far
out guarantees every tail prime exceeds `3·σ(3^(j-1))`, which is exactly the
bound making the `N/3` maximal divisor deficient (see
`head_shrink_deficient`). -/
def startIdx (j : ℕ) : ℕ := 3 * ∑ d ∈ ((3 : ℕ) ^ j).divisors, d

/-- The tail start is at least `3` (so tail indices are `≥ 2`: the tail
avoids the primes `2 = p₀` and `3 = p₁`, keeping the witness odd with its
`3`-part exactly `3^j`). -/
theorem three_le_startIdx (j : ℕ) : 3 ≤ startIdx j := by
  have h := two_mul_sum_divisors_pow_three j
  have h3 : 3 ≤ (3 : ℕ) ^ (j + 1) := by
    calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
    _ ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold startIdx
  omega

/-- **The crossing exists**: for every `j` there is a `b` making
`3^j · p_a ⋯ p_{b-1}` abundant (`a = startIdx j`).  Powered by the parent's
squarefree crossing (`exists_crossing`, divergence of `∑ 1/p`): once the tail
alone is abundant, the `3^j` head only helps, since `σ(3^j) ≥ 3^j`. -/
theorem exists_crossing_three (j : ℕ) :
    ∃ b, 2 * ((3 : ℕ) ^ j * ∏ i ∈ Finset.Ico (startIdx j) b, Nat.nth Nat.Prime i)
      < ∑ d ∈ ((3 : ℕ) ^ j
          * ∏ i ∈ Finset.Ico (startIdx j) b, Nat.nth Nat.Prime i).divisors, d := by
  obtain ⟨b, hb⟩ := exists_crossing (startIdx j)
  refine ⟨b, ?_⟩
  have hs : ∀ i ∈ Finset.Ico (startIdx j) b, 2 ≤ i := fun i hi => by
    have := three_le_startIdx j
    have := (Finset.mem_Ico.mp hi).1
    omega
  rw [sum_divisors_pow_three_mul_prod hs]
  rw [sum_divisors_prod_nth] at hb
  have hσ : (3 : ℕ) ^ j ≤ ∑ d ∈ ((3 : ℕ) ^ j).divisors, d := by
    have hid := two_mul_sum_divisors_pow_three j
    have hps : (3 : ℕ) ^ (j + 1) = 3 * 3 ^ j := by ring
    rw [hps] at hid
    have hx : 1 ≤ (3 : ℕ) ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega
  calc 2 * ((3 : ℕ) ^ j * ∏ i ∈ Finset.Ico (startIdx j) b, Nat.nth Nat.Prime i)
      = (3 : ℕ) ^ j * (2 * ∏ i ∈ Finset.Ico (startIdx j) b, Nat.nth Nat.Prime i) := by
        ring
    _ < (3 : ℕ) ^ j * ∏ i ∈ Finset.Ico (startIdx j) b, (Nat.nth Nat.Prime i + 1) :=
        mul_lt_mul_of_pos_left hb (pow_pos (by norm_num) j)
    _ ≤ (∑ d ∈ ((3 : ℕ) ^ j).divisors, d)
          * ∏ i ∈ Finset.Ico (startIdx j) b, (Nat.nth Nat.Prime i + 1) :=
        Nat.mul_le_mul_right _ hσ

/-- The first index `b` at which `3^j · p_a ⋯ p_{b-1}` becomes abundant. -/
noncomputable def crossingThree (j : ℕ) : ℕ := Nat.find (exists_crossing_three j)

/-- **The least-prime-3 witness for parameter `j`**:
`N_j = 3^j · p_a ⋯ p_{b-1}` with `a = startIdx j`, `b = crossingThree j`. -/
noncomputable def witnessThree (j : ℕ) : ℕ :=
  3 ^ j * ∏ i ∈ Finset.Ico (startIdx j) (crossingThree j), Nat.nth Nat.Prime i

/-- The crossing lies strictly beyond the tail start: with an empty tail the
number is `3^j`, which is deficient (`2·σ(3^j) = 3·3^j − 1 < 4·3^j`). -/
theorem startIdx_lt_crossingThree (j : ℕ) : startIdx j < crossingThree j := by
  by_contra h
  push_neg at h
  have hspec := Nat.find_spec (exists_crossing_three j)
  rw [show crossingThree j = Nat.find (exists_crossing_three j) from rfl] at h
  rw [Finset.Ico_eq_empty
    (by omega : ¬ startIdx j < Nat.find (exists_crossing_three j))] at hspec
  rw [Finset.prod_empty, mul_one] at hspec
  have hid := two_mul_sum_divisors_pow_three j
  have hps : (3 : ℕ) ^ (j + 1) = 3 * 3 ^ j := by ring
  rw [hps] at hid
  have hx : 1 ≤ (3 : ℕ) ^ j := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- **Crossing minimality, sharpened to strict deficiency**: for any `c` short
of the crossing, `σ(3^j)·∏_{[a,c)}(pᵢ+1) < 2·(3^j·∏_{[a,c)} pᵢ)` — minimality
gives `≤`, and `sum_divisors_pow_three_mul_prod_ne_two_mul` rules out
equality. -/
theorem head_tail_pred_strict (j : ℕ) {c : ℕ} (hc : c < crossingThree j) :
    (∑ d ∈ ((3 : ℕ) ^ j).divisors, d)
        * ∏ i ∈ Finset.Ico (startIdx j) c, (Nat.nth Nat.Prime i + 1)
      < 2 * ((3 : ℕ) ^ j * ∏ i ∈ Finset.Ico (startIdx j) c, Nat.nth Nat.Prime i) := by
  have hc' : c < Nat.find (exists_crossing_three j) := hc
  have hple := Nat.find_min (exists_crossing_three j) hc'
  have hs : ∀ i ∈ Finset.Ico (startIdx j) c, 2 ≤ i := fun i hi => by
    have := three_le_startIdx j
    have := (Finset.mem_Ico.mp hi).1
    omega
  rw [sum_divisors_pow_three_mul_prod hs] at hple
  exact lt_of_le_of_ne (Nat.not_lt.mp hple)
    (sum_divisors_pow_three_mul_prod_ne_two_mul hs)

-- ============================================================
-- The maximal divisors of the witness are deficient
-- ============================================================

/-- **Tail maximal divisors are deficient**: `N_j / pᵢ` for a tail index `i`.
The parent's swap argument (`erase_prod_deficient`) with the `3^j` head riding
along: for the top index this is crossing minimality; for a smaller omitted
index the inequality improves, since `pᵢ(p_c+1) ≤ p_c(pᵢ+1)`. -/
theorem witnessThree_erase_deficient {j i : ℕ}
    (hi : i ∈ Finset.Ico (startIdx j) (crossingThree j)) :
    ((3 : ℕ) ^ j * ∏ k ∈ (Finset.Ico (startIdx j) (crossingThree j)).erase i,
      Nat.nth Nat.Prime k).Deficient := by
  obtain ⟨c, hc⟩ : ∃ c, crossingThree j = c + 1 :=
    ⟨crossingThree j - 1, by have := startIdx_lt_crossingThree j; omega⟩
  have hac : startIdx j ≤ c := by have := startIdx_lt_crossingThree j; omega
  have hpred := head_tail_pred_strict j (c := c) (by omega)
  rw [deficient_iff_sum_divisors]
  rw [hc] at hi ⊢
  have hs2 : ∀ k ∈ (Finset.Ico (startIdx j) (c + 1)).erase i, 2 ≤ k := fun k hk => by
    have := three_le_startIdx j
    have := (Finset.mem_Ico.mp (Finset.mem_of_mem_erase hk)).1
    omega
  rw [sum_divisors_pow_three_mul_prod hs2]
  have hico : Finset.Ico (startIdx j) (c + 1) = insert c (Finset.Ico (startIdx j) c) :=
    Nat.Ico_succ_right_eq_insert_Ico hac
  rcases Finset.mem_Ico.mp hi with ⟨hai, hic1⟩
  rcases Nat.lt_or_ge i c with hilt | hige
  · -- i < c: erase i, keep the top prime p_c
    have herase : (Finset.Ico (startIdx j) (c + 1)).erase i
        = insert c ((Finset.Ico (startIdx j) c).erase i) := by
      rw [hico, Finset.erase_insert_of_ne (by omega : c ≠ i)]
    have hcnot : c ∉ (Finset.Ico (startIdx j) c).erase i := fun hmem =>
      absurd (Finset.mem_Ico.mp (Finset.mem_of_mem_erase hmem)).2 (lt_irrefl c)
    have himem : i ∈ Finset.Ico (startIdx j) c := Finset.mem_Ico.mpr ⟨hai, hilt⟩
    rw [herase, Finset.prod_insert hcnot, Finset.prod_insert hcnot]
    set S := ∑ d ∈ ((3 : ℕ) ^ j).divisors, d with hS
    set A := ∏ k ∈ (Finset.Ico (startIdx j) c).erase i, (Nat.nth Nat.Prime k + 1) with hA
    set B := ∏ k ∈ (Finset.Ico (startIdx j) c).erase i, Nat.nth Nat.Prime k with hB
    set pi := Nat.nth Nat.Prime i with hpi
    set pc := Nat.nth Nat.Prime c with hpc
    have hsplitσ : (pi + 1) * A
        = ∏ k ∈ Finset.Ico (startIdx j) c, (Nat.nth Nat.Prime k + 1) := by
      rw [hpi, hA]
      exact Finset.mul_prod_erase (Finset.Ico (startIdx j) c)
        (fun k => Nat.nth Nat.Prime k + 1) himem
    have hsplitn : pi * B = ∏ k ∈ Finset.Ico (startIdx j) c, Nat.nth Nat.Prime k := by
      rw [hpi, hB]
      exact Finset.mul_prod_erase (Finset.Ico (startIdx j) c)
        (fun k => Nat.nth Nat.Prime k) himem
    have hpred' : S * ((pi + 1) * A) < 2 * ((3 : ℕ) ^ j * (pi * B)) := by
      rw [hsplitσ, hsplitn]
      exact hpred
    have hpic : pi ≤ pc :=
      le_of_lt ((Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr hilt)
    have hkey : pi * (pc + 1) ≤ pc * (pi + 1) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.mul_comm pc pi]
      exact Nat.add_le_add_left hpic _
    refine Nat.lt_of_mul_lt_mul_left (a := pi + 1) ?_
    calc (pi + 1) * (S * ((pc + 1) * A))
        = (pc + 1) * (S * ((pi + 1) * A)) := by ring
      _ < (pc + 1) * (2 * ((3 : ℕ) ^ j * (pi * B))) :=
          mul_lt_mul_of_pos_left hpred' (by omega : 0 < pc + 1)
      _ = 2 * (3 : ℕ) ^ j * B * (pi * (pc + 1)) := by ring
      _ ≤ 2 * (3 : ℕ) ^ j * B * (pc * (pi + 1)) :=
          Nat.mul_le_mul_left _ hkey
      _ = (pi + 1) * (2 * ((3 : ℕ) ^ j * (pc * B))) := by ring
  · -- i = c: the erase IS the predecessor
    have hieq : i = c := by omega
    subst hieq
    have herase : (Finset.Ico (startIdx j) (i + 1)).erase i
        = Finset.Ico (startIdx j) i := by
      rw [hico, Finset.erase_insert (fun hmem =>
        absurd (Finset.mem_Ico.mp hmem).2 (lt_irrefl i))]
    rw [herase]
    exact hpred

/-- **The head-shrink maximal divisor `N/3` is deficient** — the genuinely
NEW obligation versus the squarefree parent, and the reason the tail starts
at `a = 3·σ(3^j)`.  Writing `T = σ(3^m)`, `S = σ(3^(m+1)) = 3T + 1` and
`q = p_c` for the top tail prime, crossing minimality bounds the σ-side by
the strict predecessor inequality, and `q ≥ a ≥ 3S > 3T` closes the
comparison `3T(q+1) ≤ Sq`. -/
theorem head_shrink_deficient (m : ℕ) :
    ((3 : ℕ) ^ m * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
      Nat.nth Nat.Prime i).Deficient := by
  obtain ⟨c, hc⟩ : ∃ c, crossingThree (m + 1) = c + 1 :=
    ⟨crossingThree (m + 1) - 1, by have := startIdx_lt_crossingThree (m + 1); omega⟩
  have hac : startIdx (m + 1) ≤ c := by
    have := startIdx_lt_crossingThree (m + 1); omega
  have hpred := head_tail_pred_strict (m + 1) (c := c) (by omega)
  rw [deficient_iff_sum_divisors, hc]
  have hs2 : ∀ k ∈ Finset.Ico (startIdx (m + 1)) (c + 1), 2 ≤ k := fun k hk => by
    have := three_le_startIdx (m + 1)
    have := (Finset.mem_Ico.mp hk).1
    omega
  rw [sum_divisors_pow_three_mul_prod hs2]
  rw [Nat.Ico_succ_right_eq_insert_Ico hac]
  have hcnot : c ∉ Finset.Ico (startIdx (m + 1)) c := fun hmem =>
    absurd (Finset.mem_Ico.mp hmem).2 (lt_irrefl c)
  rw [Finset.prod_insert hcnot, Finset.prod_insert hcnot]
  set T := ∑ d ∈ ((3 : ℕ) ^ m).divisors, d with hT
  set S := ∑ d ∈ ((3 : ℕ) ^ (m + 1)).divisors, d with hSdef
  set q := Nat.nth Nat.Prime c with hq
  set A := ∏ k ∈ Finset.Ico (startIdx (m + 1)) c, (Nat.nth Nat.Prime k + 1) with hAdef
  set B := ∏ k ∈ Finset.Ico (startIdx (m + 1)) c, Nat.nth Nat.Prime k with hBdef
  -- hpred : S * A < 2 * (3^(m+1) * B); goal : T * ((q+1) * A) < 2 * (3^m * (q * B))
  have hST : S = 3 * T + 1 := by
    have h1 := two_mul_sum_divisors_pow_three m
    have h2 := two_mul_sum_divisors_pow_three (m + 1)
    have h3 : (3 : ℕ) ^ (m + 1 + 1) = 3 * 3 ^ (m + 1) := by ring
    rw [h3] at h2
    omega
  have hstart : startIdx (m + 1) = 3 * S := by
    unfold startIdx
    rw [hSdef]
  have hcq : c ≤ q := by
    have hmono : StrictMono (Nat.nth Nat.Prime) := fun x y hxy =>
      (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr hxy
    exact hmono.le_apply
  have h3Tq : 3 * T ≤ q := by omega
  have hkey : 3 * (T * (q + 1)) ≤ S * q := by
    rw [hST]
    nlinarith [h3Tq]
  have hqpos : 0 < q := (Nat.prime_nth_prime c).pos
  refine Nat.lt_of_mul_lt_mul_left (a := 3) ?_
  calc 3 * (T * ((q + 1) * A))
      = (3 * (T * (q + 1))) * A := by ring
    _ ≤ (S * q) * A := Nat.mul_le_mul_right _ hkey
    _ = q * (S * A) := by ring
    _ < q * (2 * ((3 : ℕ) ^ (m + 1) * B)) :=
        mul_lt_mul_of_pos_left hpred hqpos
    _ = 3 * (2 * ((3 : ℕ) ^ m * (q * B))) := by
        rw [pow_succ]
        ring

-- ============================================================
-- The witness is odd primitive abundant with least prime 3
-- ============================================================

/-- **The witness `N_{m+1}` is odd primitive abundant with `minFac = 3`.**
Abundant by the crossing; odd since head and tail are odd; every proper
divisor divides a maximal divisor `N/3` (deficient by
`head_shrink_deficient`) or `N/pᵢ` (deficient by
`witnessThree_erase_deficient`), and deficiency is divisor-inherited; the
least prime factor is `3` because `3 ∣ N`, `N` is odd, and `minFac` is
prime. -/
theorem witnessThree_spec (m : ℕ) :
    witnessThree (m + 1) ∈ OddPrimitiveAbundant
      ∧ (witnessThree (m + 1)).minFac = 3 := by
  have hs1 : ∀ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)), 1 ≤ i :=
    fun i hi => by
      have := three_le_startIdx (m + 1)
      have := (Finset.mem_Ico.mp hi).1
      omega
  have hPodd : Odd (∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
      Nat.nth Nat.Prime i) := odd_prod_nth hs1
  have hPpos : 0 < ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
      Nat.nth Nat.Prime i := prod_nth_pos _
  have hNdef : witnessThree (m + 1)
      = 3 ^ (m + 1) * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
          Nat.nth Nat.Prime i := rfl
  have hNpos : 0 < witnessThree (m + 1) := by
    rw [hNdef]
    exact Nat.mul_pos (pow_pos (by norm_num) _) hPpos
  have hNodd : Odd (witnessThree (m + 1)) := by
    rw [hNdef]
    exact (Odd.pow (by decide : Odd 3)).mul hPodd
  have habund : (witnessThree (m + 1)).Abundant := by
    rw [Nat.abundant_iff_sum_divisors]
    exact Nat.find_spec (exists_crossing_three (m + 1))
  have hprim : ∀ d ∈ (witnessThree (m + 1)).properDivisors, d.Deficient := by
    intro d hd
    obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hNpos
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hk1 | hge
      · interval_cases k
        · rw [Nat.mul_zero] at hk
          exact absurd hk hNpos.ne'
        · rw [Nat.mul_one] at hk
          omega
      · exact hge
    have hrprime : k.minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨t, ht⟩ := Nat.minFac_dvd k
    have hNrt : witnessThree (m + 1) = k.minFac * (d * t) := by
      rw [hk, ht]; ring
    have hrN : k.minFac ∣ 3 ^ (m + 1)
        * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
            Nat.nth Nat.Prime i := by
      rw [← hNdef, hNrt]
      exact Dvd.intro _ rfl
    rcases (Nat.Prime.dvd_mul hrprime).mp hrN with h3 | hPdvd
    · -- the omitted prime is 3: d divides the deficient N/3 = 3^m · P
      have hr3 : k.minFac = 3 :=
        (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).mp
          (hrprime.dvd_of_dvd_pow h3)
      have hcancel : 3 ^ m * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
          Nat.nth Nat.Prime i = d * t := by
        have h1 : 3 * (3 ^ m * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
            Nat.nth Nat.Prime i) = 3 * (d * t) := by
          have hpow : (3 : ℕ) ^ (m + 1)
              * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
                  Nat.nth Nat.Prime i
              = 3 * (3 ^ m * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
                  Nat.nth Nat.Prime i) := by
            rw [pow_succ]; ring
          rw [← hpow, ← hNdef, hNrt, hr3]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
      exact deficient_of_dvd (head_shrink_deficient m) ⟨t, hcancel.symm⟩ hdpos.ne'
    · -- the omitted prime is a tail prime pᵢ: d divides the deficient N/pᵢ
      obtain ⟨i, hi, hdvd'⟩ := (hrprime.prime.dvd_finsetProd_iff _).mp hPdvd
      have hre : k.minFac = Nat.nth Nat.Prime i :=
        (Nat.prime_dvd_prime_iff_eq hrprime (Nat.prime_nth_prime i)).mp hdvd'
      have hsplit : Nat.nth Nat.Prime i
          * ∏ w ∈ (Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1))).erase i,
              Nat.nth Nat.Prime w
          = ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
              Nat.nth Nat.Prime i :=
        Finset.mul_prod_erase _ (fun w => Nat.nth Nat.Prime w) hi
      have hcancel : 3 ^ (m + 1)
          * ∏ w ∈ (Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1))).erase i,
              Nat.nth Nat.Prime w = d * t := by
        have h1 : Nat.nth Nat.Prime i * (3 ^ (m + 1)
            * ∏ w ∈ (Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1))).erase i,
                Nat.nth Nat.Prime w)
            = Nat.nth Nat.Prime i * (d * t) := by
          calc Nat.nth Nat.Prime i * (3 ^ (m + 1)
              * ∏ w ∈ (Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1))).erase i,
                  Nat.nth Nat.Prime w)
              = 3 ^ (m + 1) * (Nat.nth Nat.Prime i
                * ∏ w ∈ (Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1))).erase i,
                    Nat.nth Nat.Prime w) := by ring
            _ = witnessThree (m + 1) := by rw [hsplit, ← hNdef]
            _ = Nat.nth Nat.Prime i * (d * t) := by rw [hNrt, hre]
        exact Nat.eq_of_mul_eq_mul_left (Nat.prime_nth_prime i).pos h1
      exact deficient_of_dvd (witnessThree_erase_deficient hi) ⟨t, hcancel.symm⟩
        hdpos.ne'
  -- least prime factor is 3
  have h3dvd : 3 ∣ witnessThree (m + 1) := by
    rw [hNdef, pow_succ]
    exact ⟨3 ^ m * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
        Nat.nth Nat.Prime i, by ring⟩
  have hminle : (witnessThree (m + 1)).minFac ≤ 3 :=
    Nat.minFac_le_of_dvd (by norm_num) h3dvd
  have hN1 : witnessThree (m + 1) ≠ 1 := by
    intro h1
    rw [h1] at h3dvd
    norm_num at h3dvd
  have hmin2 : 2 ≤ (witnessThree (m + 1)).minFac := (Nat.minFac_prime hN1).two_le
  have hminne2 : (witnessThree (m + 1)).minFac ≠ 2 := by
    intro h2
    have hdvd2 : 2 ∣ witnessThree (m + 1) := h2 ▸ Nat.minFac_dvd _
    obtain ⟨w, hw⟩ := hNodd
    omega
  exact ⟨⟨hNodd, habund, hprim⟩, by omega⟩

/-- **Distinct parameters give distinct witnesses**: the tail is coprime to
`3`, so the `3`-adic valuation of `N_{m+1}` is exactly `m + 1`. -/
theorem witnessThree_injective :
    Function.Injective fun m : ℕ => witnessThree (m + 1) := by
  have hval : ∀ m : ℕ, (witnessThree (m + 1)).factorization 3 = m + 1 := by
    intro m
    have hs2 : ∀ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)), 2 ≤ i :=
      fun i hi => by
        have := three_le_startIdx (m + 1)
        have := (Finset.mem_Ico.mp hi).1
        omega
    have h3P : ¬ (3 : ℕ) ∣ ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
        Nat.nth Nat.Prime i := three_not_dvd_prod_nth hs2
    have hPpos : 0 < ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
        Nat.nth Nat.Prime i := prod_nth_pos _
    show ((3 : ℕ) ^ (m + 1) * ∏ i ∈ Finset.Ico (startIdx (m + 1)) (crossingThree (m + 1)),
        Nat.nth Nat.Prime i).factorization 3 = m + 1
    rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hPpos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd h3P,
      Nat.Prime.factorization_pow Nat.prime_three]
  intro m l h
  simp only at h
  have hm := hval m
  rw [h, hval l] at hm
  omega

-- ============================================================
-- Headline: infinitude with least prime factor 3
-- ============================================================

/-- The set of odd primitive abundant numbers whose least prime factor is `3`
— the least-prime-fixed slice of A006038 (the parent's witnesses realize each
least prime at most once; this slice needs the non-squarefree family). -/
def OddPrimitiveAbundantLeastThree : Set ℕ :=
  {n | n ∈ OddPrimitiveAbundant ∧ n.minFac = 3}

/-- `945 = 3³·5·7` is the least member of the slice: odd primitive abundant
(parent file) with least prime factor `3`. -/
theorem mem_oddPrimitiveAbundantLeastThree_945 :
    945 ∈ OddPrimitiveAbundantLeastThree := by
  refine ⟨mem_oddPrimitiveAbundant_945, ?_⟩
  have h3 : (3 : ℕ) ∣ 945 := by norm_num
  have hle := Nat.minFac_le_of_dvd (by norm_num) h3
  have hmin2 := (Nat.minFac_prime (by norm_num : (945 : ℕ) ≠ 1)).two_le
  have hne : (945 : ℕ).minFac ≠ 2 := by
    intro h2
    have : (2 : ℕ) ∣ 945 := h2 ▸ Nat.minFac_dvd _
    norm_num at this
  omega

/-- **MAIN RESULT — there are infinitely many odd primitive abundant numbers
with least prime factor `3`.**  The injective family
`m ↦ 3^(m+1) · p_a ⋯ p_{b-1}` (tail started at `a = 3·σ(3^(m+1))`, stopped at
the first abundance crossing) consists entirely of odd primitive abundant
numbers with `minFac = 3`.  Strengthens the parent's infinitude, whose
squarefree witnesses realize each least prime factor at most once. -/
theorem oddPrimitiveAbundantLeastThree_infinite :
    OddPrimitiveAbundantLeastThree.Infinite :=
  Set.infinite_of_injective_forall_mem witnessThree_injective
    fun m => witnessThree_spec m

/-- The headline restated without the named sets: infinitely many `n` are
odd, abundant, have all proper divisors deficient, and have least prime
factor `3`. -/
theorem infinitely_many_odd_primitive_abundant_least_prime_three :
    {n : ℕ | Odd n ∧ n.Abundant ∧ (∀ d ∈ n.properDivisors, d.Deficient)
      ∧ n.minFac = 3}.Infinite :=
  Set.infinite_of_injective_forall_mem witnessThree_injective fun m => by
    obtain ⟨⟨ho, ha, hd⟩, hm⟩ := witnessThree_spec m
    exact ⟨ho, ha, hd, hm⟩

end AbundantNumberOQ03OQ03
