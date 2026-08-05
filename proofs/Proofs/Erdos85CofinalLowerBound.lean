import Proofs.Erdos85PolarityAbsolute
import Proofs.Erdos85PolarityDeletion
import Proofs.Erdos85PolarityBand
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.Bertrand

/-!
# Cofinal lower bounds for Erdős Problem 85

Disjoint unions turn two consecutive polarity-graph orders into witnesses at
every sufficiently large order.  In particular `minDegreeForC4 n` tends to
infinity, not merely along the projective-plane subsequence.
-/

open SimpleGraph Filter

namespace Erdos85

/-- A four-cycle in a disjoint union lies wholly in one summand. -/
theorem not_containsC4_sum {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : ¬ containsC4 V G) (hH : ¬ containsC4 W H) :
    ¬ containsC4 (V ⊕ W) (G ⊕g H) := by
  rintro ⟨f, hf, hadj⟩
  have h01 := hadj 0 1 (by decide : C4.Adj 0 1)
  have h12 := hadj 1 2 (by decide : C4.Adj 1 2)
  have h23 := hadj 2 3 (by decide : C4.Adj 2 3)
  have h30 := hadj 3 0 (by decide : C4.Adj 3 0)
  cases h0 : f 0 with
  | inl v0 =>
      cases h1 : f 1 with
      | inr w1 => simp [h0, h1] at h01
      | inl v1 =>
          cases h2 : f 2 with
          | inr w2 => simp [h1, h2] at h12
          | inl v2 =>
              cases h3 : f 3 with
              | inr w3 => simp [h2, h3] at h23
              | inl v3 =>
                  apply hG
                  let g : Fin 4 → V := fun i => Sum.elim id (fun _ => v0) (f i)
                  have hfg : ∀ i, f i = (Sum.inl (g i) : V ⊕ W) := by
                    intro i
                    fin_cases i <;> simp [g, h0, h1, h2, h3]
                  refine ⟨g, ?_, ?_⟩
                  · intro i j hij
                    apply hf
                    rw [hfg i, hfg j, hij]
                  · intro i j hij
                    simpa [hfg i, hfg j] using hadj i j hij
  | inr w0 =>
      cases h1 : f 1 with
      | inl v1 => simp [h0, h1] at h01
      | inr w1 =>
          cases h2 : f 2 with
          | inl v2 => simp [h1, h2] at h12
          | inr w2 =>
              cases h3 : f 3 with
              | inl v3 => simp [h2, h3] at h23
              | inr w3 =>
                  apply hH
                  let g : Fin 4 → W := fun i => Sum.elim (fun _ => w0) id (f i)
                  have hfg : ∀ i, f i = (Sum.inr (g i) : V ⊕ W) := by
                    intro i
                    fin_cases i <;> simp [g, h0, h1, h2, h3]
                  refine ⟨g, ?_, ?_⟩
                  · intro i j hij
                    apply hf
                    rw [hfg i, hfg j, hij]
                  · intro i j hij
                    simpa [hfg i, hfg j] using hadj i j hij

/-- Minimum-degree lower bounds are preserved by disjoint union. -/
theorem le_minDegree_sum {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel (G ⊕g H).Adj] {d : ℕ}
    (hG : d ≤ G.minDegree) (hH : d ≤ H.minDegree) :
    d ≤ (G ⊕g H).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  rintro (v | w)
  · simp only [SimpleGraph.degree, SimpleGraph.neighborFinset]
    rw [← Set.ncard_eq_toFinset_card', neighborSet_sum_inl,
      Set.ncard_image_of_injective _ Sum.inl_injective,
      Set.ncard_eq_toFinset_card']
    exact hG.trans (G.minDegree_le_degree v)
  · simp only [SimpleGraph.degree, SimpleGraph.neighborFinset]
    rw [← Set.ncard_eq_toFinset_card', neighborSet_sum_inr,
      Set.ncard_image_of_injective _ Sum.inr_injective,
      Set.ncard_eq_toFinset_card']
    exact hH.trans (H.minDegree_le_degree w)

/-- Witness orders are closed under addition. -/
theorem C4FreeMinDegreeWitness.add {a b d : ℕ}
    (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : C4FreeMinDegreeWitness a d) (hb : C4FreeMinDegreeWitness b d) :
    C4FreeMinDegreeWitness (a + b) d := by
  letI : Nonempty (Fin a) := Fin.pos_iff_nonempty.mp ha0
  letI : Nonempty (Fin b) := Fin.pos_iff_nonempty.mp hb0
  rcases ha with ⟨G, hdecG, hminG, hfreeG⟩
  rcases hb with ⟨H, hdecH, hminH, hfreeH⟩
  letI := hdecG
  letI := hdecH
  letI : DecidableRel (G ⊕g H).Adj := Classical.decRel _
  apply c4FreeMinDegreeWitness_of_card_eq (G ⊕g H)
  · simp
  · exact le_minDegree_sum hminG hminH
  · exact not_containsC4_sum hfreeG hfreeH

/-- A witness may be weakened to any smaller minimum-degree certificate. -/
theorem C4FreeMinDegreeWitness.mono_degree {n d e : ℕ} (hde : d ≤ e)
    (hw : C4FreeMinDegreeWitness n e) : C4FreeMinDegreeWitness n d := by
  rcases hw with ⟨G, hdec, hmin, hfree⟩
  exact ⟨G, hdec, hde.trans hmin, hfree⟩

/-- A positive number of disjoint copies preserves the degree certificate. -/
theorem C4FreeMinDegreeWitness.nsmul {a d k : ℕ} (ha0 : 0 < a)
    (hk : 0 < k) (ha : C4FreeMinDegreeWitness a d) :
    C4FreeMinDegreeWitness (k * a) d := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa using ha
      · rw [Nat.succ_mul]
        exact C4FreeMinDegreeWitness.add (a := k * a) (b := a)
          (Nat.mul_pos (Nat.pos_of_ne_zero hk0) ha0) (by positivity)
          (ih (Nat.pos_of_ne_zero hk0)) ha

/-- Two consecutive positive witness orders generate every order beyond the
square of the smaller order. -/
theorem witness_of_consecutive_orders {a b d n : ℕ}
    (hb0 : 0 < b) (hab : a = b + 1)
    (ha : C4FreeMinDegreeWitness a d) (hb : C4FreeMinDegreeWitness b d)
    (hn : b * b ≤ n) : C4FreeMinDegreeWitness n d := by
  let r := n % b
  let k := n / b
  have hr : r < b := Nat.mod_lt n hb0
  have hk : b ≤ k := by
    rw [Nat.le_div_iff_mul_le hb0]
    simpa [Nat.mul_comm] using hn
  have hrk : r < k := lt_of_lt_of_le hr hk
  have hrepr : n = r * a + (k - r) * b := by
    have hsub : k - r + r = k := Nat.sub_add_cancel (Nat.le_of_lt hrk)
    calc
      n = k * b + r := by
        calc
          n = n % b + b * (n / b) := (Nat.mod_add_div n b).symm
          _ = k * b + r := by dsimp [r, k]; ac_rfl
      _ = r * (b + 1) + (k - r) * b := by
        calc
          k * b + r = (k - r + r) * b + r := by rw [hsub]
          _ = r * (b + 1) + (k - r) * b := by ring
      _ = r * a + (k - r) * b := by rw [hab]
  rw [hrepr]
  by_cases hr0 : r = 0
  · simp only [hr0, zero_mul, zero_add]
    exact C4FreeMinDegreeWitness.nsmul (a := b) (k := k) hb0 (by omega) hb
  · exact C4FreeMinDegreeWitness.add
      (Nat.mul_pos (Nat.pos_of_ne_zero hr0) (by omega))
      (Nat.mul_pos (Nat.sub_pos_of_lt hrk) hb0)
      (C4FreeMinDegreeWitness.nsmul (a := a) (k := r)
        (by omega) (Nat.pos_of_ne_zero hr0) ha)
      (C4FreeMinDegreeWitness.nsmul (a := b) (k := k - r) hb0
        (Nat.sub_pos_of_lt hrk) hb)

/-! ## Composing a whole interval of witness orders -/

/-- If every order from `A` through `A+L` carries a degree-`d` witness,
then `t` blocks realize every order `t*A+r` with `r ≤ t*L`. -/
theorem witness_nsmul_add_of_interval {A L d t r : ℕ}
    (hA0 : 0 < A)
    (hband : ∀ j ≤ L, C4FreeMinDegreeWitness (A + j) d)
    (ht : 0 < t) (hr : r ≤ t * L) :
    C4FreeMinDegreeWitness (t * A + r) d := by
  induction t generalizing r with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst t
        simpa using hband r (by simpa using hr)
      · let s := min r L
        have hsL : s ≤ L := min_le_right _ _
        have hsr : s ≤ r := min_le_left _ _
        have hrem : r - s ≤ t * L := by
          by_cases hrL : r ≤ L
          · have hs : s = r := min_eq_left hrL
            simp [hs]
          · have hs : s = L := min_eq_right (Nat.le_of_not_ge hrL)
            rw [hs]
            have hr' : r ≤ t * L + L := by
              simpa [Nat.succ_mul, Nat.add_comm] using hr
            omega
        have hleft := hband s hsL
        have hright := ih (r := r - s) (Nat.pos_of_ne_zero ht0) hrem
        have hright0 : 0 < t * A + (r - s) := by
          exact lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero ht0) hA0)
            (Nat.le_add_right _ _)
        have hadd := C4FreeMinDegreeWitness.add
          (Nat.add_pos_left hA0 s) hright0 hleft hright
        have hrs : r - s + s = r := Nat.sub_add_cancel hsr
        have heq : (t + 1) * A + r = (A + s) + (t * A + (r - s)) := by
          rw [Nat.succ_mul]
          omega
        rw [heq]
        exact hadd

/-- An interval of `L+1` consecutive witness orders has conductor at most
`(A/L+1)*A`.  This is the quantitative gain over using only `A,A+1`. -/
theorem eventually_witness_of_interval {A L d : ℕ}
    (hA0 : 0 < A) (hL0 : 0 < L)
    (hband : ∀ j ≤ L, C4FreeMinDegreeWitness (A + j) d) :
    ∀ n, (A / L + 1) * A ≤ n → C4FreeMinDegreeWitness n d := by
  intro n hn
  let t := n / A
  let r := n % A
  have htLower : A / L + 1 ≤ t := by
    exact (Nat.le_div_iff_mul_le hA0).2 hn
  have ht : 0 < t := lt_of_lt_of_le (Nat.zero_lt_succ (A / L)) htLower
  have hrA : r < A := Nat.mod_lt n hA0
  have hAL : A ≤ (A / L + 1) * L := by
    have hmod := Nat.mod_add_div A L
    have hmodlt := Nat.mod_lt A hL0
    calc
      A = A % L + L * (A / L) := hmod.symm
      _ ≤ L + L * (A / L) := Nat.add_le_add_right (Nat.le_of_lt hmodlt) _
      _ = (A / L + 1) * L := by ring
  have hr : r ≤ t * L := by
    exact (Nat.le_of_lt hrA).trans (hAL.trans (Nat.mul_le_mul_right L htLower))
  have hw := witness_nsmul_add_of_interval hA0 hband ht hr
  have heq : n = t * A + r := by
    calc
      n = n % A + A * (n / A) := (Nat.mod_add_div n A).symm
      _ = t * A + r := by dsimp [t, r]; ac_rfl
  rw [heq]
  exact hw

/-! ## Specialization to finite-field polarity graphs -/

/-- For every degree target, all sufficiently large orders admit a C4-free
graph meeting that target. -/
theorem eventually_c4FreeMinDegreeWitness (d : ℕ) :
    ∀ᶠ n in atTop, C4FreeMinDegreeWitness n d := by
  let e := d + 1
  let K := GaloisField 2 e
  letI : DecidableEq K := Classical.decEq K
  let q := Nat.card K
  let b := (q + 1) * q
  have he : e ≠ 0 := by simp [e]
  have hqcard : q = 2 ^ e := by
    exact GaloisField.card 2 e he
  have hqpos : 0 < q := by
    rw [hqcard]
    positivity
  have hdq : d ≤ q := by
    rw [hqcard]
    have hpow := Nat.mul_le_pow (a := 2) (by decide : 2 ≠ 1) e
    exact (by omega : d ≤ 2 * e).trans hpow
  have ha : C4FreeMinDegreeWitness (b + 1) d := by
    have ht := Polarity.tightC4Witness K
    have hw : C4FreeMinDegreeWitness ((q + 1) * q + 1) q := by
      simpa [TightC4Witness, K, q] using ht
    exact ⟨hw.choose, hw.choose_spec.choose,
      hdq.trans hw.choose_spec.choose_spec.1, hw.choose_spec.choose_spec.2⟩
  have hb : C4FreeMinDegreeWitness b d := by
    have hw := Polarity.c4FreeMinDegreeWitness_projectivePlane_pred (K := K)
    rcases hw with ⟨G, hdec, hmin, hfree⟩
    exact ⟨G, hdec, hdq.trans hmin, hfree⟩
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact witness_of_consecutive_orders (Nat.mul_pos (by omega) hqpos)
    rfl ha hb hn

/-- The forcing threshold tends to infinity along the full sequence of graph
orders, strengthening the earlier unbounded-subsequence result. -/
theorem minDegreeForC4_tendsto_atTop :
    Tendsto minDegreeForC4 atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro d
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_c4FreeMinDegreeWitness d)
  refine ⟨max N 4, fun n hn => ?_⟩
  have hw := hN n (le_trans (le_max_left N 4) hn)
  have hn4 : 4 ≤ n := le_trans (le_max_right N 4) hn
  exact le_of_lt ((c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn4).1 hw)

/-! ## A polynomial conductor from the full deletion band -/

/-- Bertrand's postulate and the polarity deletion band give an explicit
interval construction.  The base order is `p²+d`, the interval width is
`p-d`, and `p` lies between `2(d+2)` and `4(d+2)`. -/
theorem exists_prime_band_eventual_witness (d : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 2 * (d + 2) < p ∧ p ≤ 4 * (d + 2) ∧
      ∀ n,
        (((p * p + d) / (p - d) + 1) * (p * p + d) ≤ n) →
          C4FreeMinDegreeWitness n d := by
  obtain ⟨p, hp, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * (d + 2)) (by omega)
  have hdp : d ≤ p := by omega
  have hdp' : d < p := by omega
  have hL0 : 0 < p - d := Nat.sub_pos_of_lt hdp'
  letI : Fact p.Prime := ⟨hp⟩
  let K := ZMod p
  letI : DecidableEq K := Classical.decEq K
  have hcardK : Nat.card K = p := by
    simp [K, Nat.card_eq_fintype_card, ZMod.card]
  have hcardFK : Fintype.card K = p := by simp [K, ZMod.card]
  have hband : ∀ j ≤ p - d,
      C4FreeMinDegreeWitness (p * p + d + j) d := by
    intro j hj
    let k := p - d - j
    have hk : k ≤ p := by omega
    have hkK : k ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hcardFK]
      exact hk
    have hw := Polarity.c4FreeMinDegreeWitness_projectivePlane_free_delete_band
      K (k := k) hkK
    have hdeg : d ≤ Nat.card K - k := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
      dsimp [k]
      omega
    have hw' := hw.mono_degree hdeg
    convert hw' using 1
    change p * p + d + j = (Nat.card K + 1) * Nat.card K - k
    rw [hcardK]
    have hmul : (p + 1) * p = p * p + p := by ring
    rw [hmul]
    dsimp [k]
    omega
  refine ⟨p, hp, hlower, ?_, ?_⟩
  · omega
  · exact eventually_witness_of_interval
      (Nat.add_pos_left (Nat.mul_pos hp.pos hp.pos) d) hL0 hband

/-- A simple prime-free corollary: degree `d` witnesses exist at every order
at least `400(d+2)^3`.  Constants are deliberately relaxed; the point is the
cubic exponent. -/
theorem c4FreeMinDegreeWitness_of_cubic_order {d n : ℕ}
    (hn : 400 * (d + 2) ^ 3 ≤ n) : C4FreeMinDegreeWitness n d := by
  obtain ⟨p, hp, hlower, hupper, hw⟩ := exists_prime_band_eventual_witness d
  let x := d + 2
  let A := p * p + d
  let L := p - d
  have hx : 2 ≤ x := by simp [x]
  have hp4 : p ≤ 4 * x := by simpa [x] using hupper
  have hxL : x ≤ L := by dsimp [x, L]; omega
  have hL0 : 0 < L := lt_of_lt_of_le (by omega) hxL
  have hpSq : p * p ≤ 16 * x ^ 2 := by nlinarith
  have hdSq : d ≤ x ^ 2 := by dsimp [x]; nlinarith
  have hA : A ≤ 17 * x ^ 2 := by dsimp [A]; nlinarith
  have hdiv : A / L ≤ 17 * x := by
    apply Nat.div_le_of_le_mul
    have : A ≤ L * (17 * x) := by nlinarith
    simpa [Nat.mul_comm] using this
  have hconductor : (A / L + 1) * A ≤ 400 * x ^ 3 := by
    nlinarith [Nat.mul_le_mul hdiv hA]
  apply hw n
  dsimp [A, L, x] at hconductor ⊢
  exact hconductor.trans hn

end Erdos85
