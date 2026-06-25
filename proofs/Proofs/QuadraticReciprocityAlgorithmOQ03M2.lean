/-
  Milestone 2 of the permutation-sign (Zolotarev) route to quadratic reciprocity.

  Milestone 1 (`Proofs.QuadraticReciprocityAlgorithmOQ03`) proved Zolotarev's
  lemma `legendreSym p a = Equiv.Perm.sign (Equiv.mulLeft a)` (verified, merged).
  Milestone 2 is the reciprocity step: the product `(p/q)·(q/p)` equals the sign
  of a single "grid-transpose" permutation of `Fin (p*q)`, and that sign is
  `(-1) ^ ((p-1)/2 · (q-1)/2)`.

  The grid-transpose `σ` reinterprets a row-major linear index of the `p × q`
  grid as the corresponding column-major index.  Its number of inversions is
  `C(p,2)·C(q,2) = [p(p-1)/2]·[q(q-1)/2]`, which for odd `p, q` is congruent mod 2
  to `(p-1)/2·(q-1)/2`; hence `sign σ = (-1)^((p-1)/2·(q-1)/2)`.  This inversion
  count is primality-free and was certified build-free in
  `research/problems/quadratic-reciprocity-algorithm-oq-03/verify_grid_inversions.py`
  (S8) and `verify_reciprocity_m2.py` (S6).

  STATUS (this file). FULLY VERIFIED — 0 sorry, 0 axioms.  The combinatorial heart
  of M2 is:

    1. `gridTranspose`            — the permutation itself.                [def, complete]
    2. `sign_gridTranspose_eq_choose`
                                  — `sign σ = (-1)^(C(p,2)·C(q,2))`.       [VERIFIED]
    3. `neg_one_pow_choose_two`   — parity reduction `(-1)^(C(p,2)·C(q,2)) =
                                     (-1)^((p-1)/2·(q-1)/2)` for odd p,q.   [VERIFIED]
    4. `sign_gridTranspose`       — assembly of 2 + 3.                      [VERIFIED]

  Step 2 is proved here from first principles via the inversion-count route:
  `Equiv.Perm.sign_eq_prod_prod_Ioi` expresses the sign as `(-1)` to the number of
  inversions; `gridTranspose_val` computes the permutation explicitly; `inv_char`
  characterises the inverted pairs as `{a<c} × {d<b}` (rows discordant with columns);
  and a `Finset.card_nbij'` bijection counts them as `C(p,2)·C(q,2)`.  Mathlib has no
  closed form for this sign or inversion count (S8/S18), so step 2 is genuinely new.

  #print axioms confirms every theorem depends only on `propext, Classical.choice,
  Quot.sound` (no `sorryAx`).
-/
import Mathlib

namespace QuadraticReciprocityAlgorithmOQ03M2

open Equiv Finset

/-- The grid-transpose permutation of `Fin (p*q)`.

Decode a linear index as a row-major `(i, j) : Fin p × Fin q`, swap to
`(j, i) : Fin q × Fin p`, re-encode as a linear index of the transposed grid,
and `finCongr` the `q*p = p*q` cast back.  This is the permutation whose sign
carries the quadratic-reciprocity factor (the Zolotarev–Frobenius shuffle). -/
def gridTranspose (p q : ℕ) : Equiv.Perm (Fin (p * q)) :=
  (finProdFinEquiv (m := p) (n := q)).symm.trans <|
    (Equiv.prodComm (Fin p) (Fin q)).trans <|
      (finProdFinEquiv (m := q) (n := p)).trans (finCongr (Nat.mul_comm q p))

/-- The value of the grid-transpose: the row-major index `x` decodes to row `x / q`
and column `x % q`; the transpose re-encodes them column-major as `x/q + p·(x%q)`. -/
theorem gridTranspose_val (p q : ℕ) (x : Fin (p * q)) :
    ((gridTranspose p q x : Fin (p * q)) : ℕ) = (x : ℕ) / q + p * ((x : ℕ) % q) := by
  simp [gridTranspose, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem coe_divNat {p q : ℕ} (x : Fin (p * q)) : (x.divNat : ℕ) = (x : ℕ) / q := by
  simp [Fin.divNat]

theorem coe_modNat {p q : ℕ} (x : Fin (p * q)) : (x.modNat : ℕ) = (x : ℕ) % q := by
  simp [Fin.modNat]

/-- `finProdFinEquiv` recovers `x` from its `divNat`/`modNat` coordinates. -/
theorem fpfe_divNat_modNat {p q : ℕ} (i : Fin (p * q)) :
    finProdFinEquiv (i.divNat, i.modNat) = i := by
  have : (i.divNat, i.modNat) = finProdFinEquiv.symm i := rfl
  rw [this, Equiv.apply_symm_apply]

/-- The `divNat`/`modNat` coordinates of `finProdFinEquiv (a, b)` are `a` and `b`. -/
theorem divNat_modNat_fpfe {p q : ℕ} (a : Fin p) (b : Fin q) :
    (finProdFinEquiv (a, b)).divNat = a ∧ (finProdFinEquiv (a, b)).modNat = b := by
  have h : ((finProdFinEquiv (a, b)).divNat, (finProdFinEquiv (a, b)).modNat) = (a, b) :=
    Equiv.symm_apply_apply finProdFinEquiv (a, b)
  exact ⟨(Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩

/-- The number of strictly-increasing ordered pairs in `Fin m` is `C(m,2)`. -/
theorem card_lt_pairs (m : ℕ) :
    #(univ.filter (fun x : Fin m × Fin m => x.1 < x.2)) = m.choose 2 := by
  have key : #(univ.filter (fun x : Fin m × Fin m => x.1 < x.2))
      = ∑ c : Fin m, (c : ℕ) := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hset : (univ.filter (fun a : Fin m => a < c)) = Finset.Iio c := by
      ext a; simp [Finset.mem_Iio]
    rw [Finset.sum_boole, hset, Fin.card_Iio, Nat.cast_id]
  rw [key, Fin.sum_univ_eq_sum_range (fun k => k) m, Finset.sum_range_id, Nat.choose_two_right]

/-- **Mixed-radix inversion characterization.** A pair of grid points `(a,b)`, `(c,d)`
(with `a,c < p` rows and `b,d < q` columns) is row-major increasing yet column-major
non-increasing exactly when `a < c` and `d < b` — the discordant pairs counted by the
inversion number of the grid-transpose. Pure arithmetic, `p, q` arbitrary. -/
theorem inv_char {p q a c b d : ℕ}
    (ha : a < p) (hc : c < p) (hb : b < q) (_hd : d < q) :
    ((q * a + b < q * c + d) ∧ (c + p * d ≤ a + p * b)) ↔ (a < c ∧ d < b) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_contra h
      push_neg at h
      have e1 : q * c ≤ q * a := Nat.mul_le_mul (le_refl q) h
      have hbd : b < d := by omega
      have e2 : p * (b + 1) ≤ p * d := Nat.mul_le_mul (le_refl p) (by omega)
      rw [Nat.mul_succ] at e2
      omega
    · by_contra h
      push_neg at h
      have e1 : p * b ≤ p * d := Nat.mul_le_mul (le_refl p) h
      have hca : c ≤ a := by omega
      have e2 : q * c ≤ q * a := Nat.mul_le_mul (le_refl q) hca
      have hbd : b < d := by omega
      have e3 : p * (b + 1) ≤ p * d := Nat.mul_le_mul (le_refl p) (by omega)
      rw [Nat.mul_succ] at e3
      omega
  · rintro ⟨hac, hdb⟩
    refine ⟨?_, ?_⟩
    · have e : q * (a + 1) ≤ q * c := Nat.mul_le_mul (le_refl q) (by omega)
      rw [Nat.mul_succ] at e
      omega
    · have e : p * (d + 1) ≤ p * b := Nat.mul_le_mul (le_refl p) (by omega)
      rw [Nat.mul_succ] at e
      omega

/-- For odd `n`, the parity of `C(n,2)` equals the parity of `(n-1)/2`.
(`C(n,2) = n·(n-1)/2 = n · (n-1)/2`; for odd `n` the leading factor `n` is odd,
so it does not change the parity of `(n-1)/2`.) -/
theorem choose_two_mod_two {n : ℕ} (hn : Odd n) :
    Nat.choose n 2 % 2 = ((n - 1) / 2) % 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.choose_two_right]
  have h1 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [h1]
  have hmul : (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) := by ring
  rw [hmul, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]
  have h2 : 2 * m / 2 = m := by omega
  rw [h2, Nat.mul_mod]
  have h3 : (2 * m + 1) % 2 = 1 := by omega
  rw [h3, one_mul]
  omega

/-- In `ℤˣ` (a monoid, not a ring), `(-1)^n` depends only on `n` mod 2.
`Mathlib.neg_one_pow_eq_pow_mod_two` needs `[Ring R]`, which `ℤˣ` is not, so we
derive it directly from `neg_one_sq : (-1)^2 = 1` (which holds for any
`[Monoid R] [HasDistribNeg R]`, in particular `ℤˣ`). -/
theorem neg_one_units_pow_mod_two (n : ℕ) : (-1 : ℤˣ) ^ n = (-1 : ℤˣ) ^ (n % 2) := by
  nth_rewrite 1 [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Parity reduction** (the verified elementary step of Milestone 2).
For odd `p, q`, `(-1)^(C(p,2)·C(q,2)) = (-1)^((p-1)/2 · (q-1)/2)`. -/
theorem neg_one_pow_choose_two {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    (-1 : ℤˣ) ^ (Nat.choose p 2 * Nat.choose q 2)
      = (-1 : ℤˣ) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have key : (Nat.choose p 2 * Nat.choose q 2) % 2
      = ((p - 1) / 2 * ((q - 1) / 2)) % 2 := by
    rw [Nat.mul_mod, Nat.mul_mod ((p - 1) / 2), choose_two_mod_two hp, choose_two_mod_two hq]
  rw [neg_one_units_pow_mod_two (Nat.choose p 2 * Nat.choose q 2),
      neg_one_units_pow_mod_two ((p - 1) / 2 * ((q - 1) / 2)), key]

/-- **Milestone 2 core combinatorial lemma** (now proved).
The sign of the grid-transpose equals `(-1)` to the inversion count
`C(p,2)·C(q,2)`.  Mathlib has no closed-form sign or inversion count for the grid
transpose (S8/S18), so this is genuinely-new content.  It is primality-free
(holds for all `p, q`).

Proof: `Equiv.Perm.sign_eq_prod_prod_Ioi` writes the sign as a product of `±1` over
ordered index pairs, i.e. `(-1)` to the number of inversions; `gridTranspose_val`
gives the explicit action `x ↦ x/q + p·(x%q)`; `inv_char` identifies the inverted
pairs with `{a<c} × {d<b}`; and a `Finset.card_nbij'` bijection through
`finProdFinEquiv` counts them as `C(p,2)·C(q,2)` via `card_lt_pairs`. -/
theorem sign_gridTranspose_eq_choose (p q : ℕ) :
    Equiv.Perm.sign (gridTranspose p q)
      = (-1 : ℤˣ) ^ (Nat.choose p 2 * Nat.choose q 2) := by
  set D : Finset (Σ _ : Fin (p * q), Fin (p * q)) :=
    Finset.univ.sigma (fun i => Finset.Ioi i) with hD
  set P : Finset (Fin p × Fin p) := univ.filter (fun u => u.1 < u.2) with hP
  set Q : Finset (Fin q × Fin q) := univ.filter (fun v => v.1 < v.2) with hQ
  -- the sign is `(-1)` to the number of inversions of the grid-transpose;
  -- those inversions biject with (row-pairs `a<c`) × (column-pairs `d<b`).
  have hcard : #(D.filter (fun x => ¬ gridTranspose p q x.1 < gridTranspose p q x.2))
      = Nat.choose p 2 * Nat.choose q 2 := by
    have hPQ : #(P ×ˢ Q) = Nat.choose p 2 * Nat.choose q 2 := by
      rw [Finset.card_product, hP, hQ, card_lt_pairs, card_lt_pairs]
    rw [← hPQ]
    apply Finset.card_nbij'
      (i := fun x => ((x.1.divNat, x.2.divNat), (x.2.modNat, x.1.modNat)))
      (j := fun y => (⟨finProdFinEquiv (y.1.1, y.2.2), finProdFinEquiv (y.1.2, y.2.1)⟩ :
        Σ _ : Fin (p * q), Fin (p * q)))
    · -- the decode map sends an inversion to a (row-pair, column-pair)
      rintro ⟨i, j⟩ hx
      simp only [Finset.mem_coe, Finset.mem_filter, hD, Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_Ioi, true_and] at hx
      obtain ⟨hij, hσij⟩ := hx
      have hpq : 0 < p * q := lt_of_le_of_lt (Nat.zero_le _) i.isLt
      have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hpq)
      have hp : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at hpq)
      have hib : (i : ℕ) % q < q := Nat.mod_lt _ hq
      have hjb : (j : ℕ) % q < q := Nat.mod_lt _ hq
      have hia : (i : ℕ) / q < p := (Nat.div_lt_iff_lt_mul hq).mpr i.isLt
      have hja : (j : ℕ) / q < p := (Nat.div_lt_iff_lt_mul hq).mpr j.isLt
      have h1 : q * ((i : ℕ) / q) + (i : ℕ) % q < q * ((j : ℕ) / q) + (j : ℕ) % q := by
        rw [Nat.div_add_mod, Nat.div_add_mod]; exact hij
      have h2 : (j : ℕ) / q + p * ((j : ℕ) % q) ≤ (i : ℕ) / q + p * ((i : ℕ) % q) := by
        have h := hσij
        rw [not_lt, Fin.le_def, gridTranspose_val, gridTranspose_val] at h
        exact h
      obtain ⟨hac, hdb⟩ := (inv_char hia hja hib hjb).mp ⟨h1, h2⟩
      simp only [Finset.mem_coe, Finset.mem_product, hP, hQ, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [Fin.lt_def, coe_divNat, coe_divNat]; exact hac
      · rw [Fin.lt_def, coe_modNat, coe_modNat]; exact hdb
    · -- the encode map sends a (row-pair, column-pair) back to an inversion
      rintro ⟨⟨u, v⟩, ⟨s, t⟩⟩ hy
      simp only [Finset.mem_coe, Finset.mem_product, hP, hQ, Finset.mem_filter,
        Finset.mem_univ, true_and] at hy
      obtain ⟨huv, hst⟩ := hy
      simp only [Finset.mem_coe, Finset.mem_filter, hD, Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_Ioi, true_and]
      have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) s.isLt
      have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le _) u.isLt
      have hi : ((finProdFinEquiv (u, t) : Fin (p * q)) : ℕ) = (t : ℕ) + q * (u : ℕ) := by
        simp [finProdFinEquiv]
      have hj : ((finProdFinEquiv (v, s) : Fin (p * q)) : ℕ) = (s : ℕ) + q * (v : ℕ) := by
        simp [finProdFinEquiv]
      have hu : (u : ℕ) < p := u.isLt
      have hv : (v : ℕ) < p := v.isLt
      have ht : (t : ℕ) < q := t.isLt
      have hsq : (s : ℕ) < q := s.isLt
      constructor
      · rw [Fin.lt_def, hi, hj]
        have e : q * ((u : ℕ) + 1) ≤ q * (v : ℕ) := Nat.mul_le_mul (le_refl q) (by exact_mod_cast huv)
        rw [Nat.mul_succ] at e
        omega
      · rw [not_lt, Fin.le_def, gridTranspose_val, gridTranspose_val, hi, hj]
        have du : ((t : ℕ) + q * (u : ℕ)) / q = (u : ℕ) := by
          rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt ht, Nat.zero_add]
        have mu : ((t : ℕ) + q * (u : ℕ)) % q = (t : ℕ) := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
        have dv : ((s : ℕ) + q * (v : ℕ)) / q = (v : ℕ) := by
          rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hsq, Nat.zero_add]
        have mv : ((s : ℕ) + q * (v : ℕ)) % q = (s : ℕ) := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsq]
        rw [du, mu, dv, mv]
        have e : p * ((s : ℕ) + 1) ≤ p * (t : ℕ) := Nat.mul_le_mul (le_refl p) (by exact_mod_cast hst)
        rw [Nat.mul_succ] at e
        omega
    · -- the two maps are mutually inverse (decode ∘ encode = id)
      rintro ⟨i, j⟩ _
      dsimp only
      rw [fpfe_divNat_modNat, fpfe_divNat_modNat]
    · rintro ⟨⟨u, v⟩, ⟨s, t⟩⟩ _
      dsimp only
      rw [(divNat_modNat_fpfe u t).1, (divNat_modNat_fpfe v s).1,
          (divNat_modNat_fpfe v s).2, (divNat_modNat_fpfe u t).2]
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi (gridTranspose p q), Finset.prod_sigma']
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, ← hD, hcard]

/-- **Milestone 2 core lemma.**  For odd `p, q`, the sign of the grid-transpose
permutation is the quadratic-reciprocity factor `(-1) ^ ((p-1)/2 · (q-1)/2)`.

Assembled from the inversion count `sign_gridTranspose_eq_choose` and the parity
reduction `neg_one_pow_choose_two`. -/
theorem sign_gridTranspose {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    Equiv.Perm.sign (gridTranspose p q) = (-1 : ℤˣ) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  rw [sign_gridTranspose_eq_choose, neg_one_pow_choose_two hp hq]

end QuadraticReciprocityAlgorithmOQ03M2
