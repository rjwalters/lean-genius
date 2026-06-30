/-
  CANDIDATE (VERIFIED — see STATUS below) proof of the shared Zolotarev blocker

      sign (gridTranspose m n) = (-1) ^ (C(m,2) * C(n,2)).

  KEY BREAKTHROUGH (this session, researcher-9, 2026-06-23).
  Prior sessions (≥3, in both the elementary- and algorithm-QR lineages)
  concluded that "NO Mathlib lemma gives sign = (-1)^(#inversions) for a general
  permutation", so the only route was ~100 LOC of bespoke `signAux`/`finPairsLT`
  surgery.  THAT ASSESSMENT IS OUT OF DATE.  Mathlib now has

      Equiv.Perm.sign_eq_prod_prod_Iio (σ : Perm (Fin N)) :
        σ.sign = ∏ j, ∏ i ∈ Finset.Iio j, (if σ i < σ j then 1 else -1)

  (`Mathlib/GroupTheory/Perm/Fin.lean`, `section Sign`).  Each factor is `-1`
  exactly on an inversion `i < j ∧ σ i > σ j`, so `sign σ = (-1)^(#inversions)`
  with NO `signAux` surgery.  The blocker reduces to the elementary count

      #{ (I,J) : I < J ∧ T I > T J }  =  C(m,2) · C(n,2)

  via the bijection  (I,J) ↦ ((row I, row J), (col J, col I))  onto
  (strictly-increasing row pairs) × (strictly-increasing col pairs), each of
  cardinality `choose · 2`.

  STATUS: VERIFIED and PORTED (researcher-9, 2026-06-23, S4).  This candidate
  has been kernel-checked against pinned Mathlib (rev 2df2f0150c, Lean v4.26.0)
  via `lake env lean` over the restored Mathlib olean cache, and the proof is now
  the live definition of `ZolotarevQR.sign_gridTranspose` in
  `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
  (0 sorry; `#print axioms` = `[propext, Classical.choice, Quot.sound]`).
  Two small fixes were needed vs. this draft: `Finset.sum_product'` (HO-pattern
  rewrite) → `Finset.sum_product` + `dsimp only`, and `Finset.card_Iio` →
  `Fin.card_Iio`.  This file is retained as the standalone derivation record.

  ORIGINAL STATUS (pre-verification): written against Mathlib source, API audit
  COMPLETE, but not yet kernel-verified — Docker daemon was wedged and Aristotle
  MCP returned "Resource not found".

  API AUDIT (researcher-9, 2026-06-23, S3).  Every lemma name used below was
  checked against the pinned Mathlib source on disk (rev 2df2f0150c, Lean
  v4.26.0, `proofs/.lake/packages/mathlib`).  ALL are present with signatures
  compatible with the usage here:
    * `Equiv.Perm.sign_eq_prod_prod_Iio` — Mathlib/GroupTheory/Perm/Fin.lean:478;
      factor form `if σ i < σ j then 1 else -1` matches `inner` exactly.
    * `Finset.prod_pow_eq_pow_sum` — .../BigOperators/Group/Finset/Basic.lean:656;
      `∏ a^(f i) = a^(∑ f i)`, matches.
    * `finProdFinEquiv` — Mathlib/Logic/Equiv/Fin/Basic.lean:329; its `toFun`
      `⟨x.2 + n*x.1, _⟩` and `invFun (x.divNat, x.modNat)` make `fpe_val`
      (`val = c + q*a`) and `fpe_symm` (`symm = (divNat, modNat)`) hold by `rfl`.
    * `Fin.divNat`/`Fin.modNat` — Batteries/Data/Fin/Basic.lean:133/137,
      types `Fin (m*n) → Fin m` / `Fin n`.
    * `Fin.coe_cast` (alias `Fin.val_cast`), `finCongr_apply` (a `@[simp]`
      lemma used across Mathlib) — both present.
    * `Finset.card_bij'` — Mathlib/Data/Finset/Card.lean:366; argument order
      `(i, j, hi, hj, left_inv, right_inv)` matches the four `?_` obligations
      below in order.
    * supporting: `prod_ite`, `prod_const_one`, `prod_const`, `card_filter`,
      `sum_filter` (to_additive of `prod_filter`), `univ_product_univ`,
      `sum_product'`, `sum_comm`, `card_Iio`, `Fin.sum_univ_eq_sum_range`,
      `sum_range_id`, `Nat.choose_two_right`, `card_product` — all present.
  The two names flagged "best-effort" in the prior draft
  (`finProdFinEquiv_symm_apply`, `Fintype.sum_prod_type`) are NOT used in the
  proof body and were dropped.

  REMAINING RISK after this audit is purely term-level: whether each `rw`/`simp`
  step actually fires (defeq matching, `simp` set behaviour), which only a real
  build resolves.  Existence/signature of every lemma is no longer in doubt.
  DO NOT register or mark verified until this compiles.  This file lives outside
  the gallery on purpose.
-/
import Mathlib

set_option maxHeartbeats 1600000

namespace ZGScratch

open Equiv Equiv.Perm Finset

/-- The row-major ↔ column-major transpose (perfect-shuffle) permutation. -/
def gridTranspose (m n : ℕ) : Equiv.Perm (Fin (m * n)) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodComm (Fin m) (Fin n)).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm n m))))

@[simp] theorem gridTranspose_apply {m n : ℕ} (i : Fin m) (j : Fin n) :
    gridTranspose m n (finProdFinEquiv (i, j))
      = finCongr (Nat.mul_comm n m) (finProdFinEquiv (j, i)) := by
  simp [gridTranspose]

/-- Value of the canonical row-major encoding: `finProdFinEquiv (a,c)` has value
    `c + q * a` (row `a` weighted by the column count `q`). -/
theorem fpe_val {p q : ℕ} (a : Fin p) (c : Fin q) :
    (finProdFinEquiv (a, c) : Fin (p * q)).val = (c : ℕ) + q * (a : ℕ) := rfl

/-- `finProdFinEquiv.symm` is decode-by-div/mod. -/
theorem fpe_symm {p q : ℕ} (x : Fin (p * q)) :
    finProdFinEquiv.symm x = (x.divNat, x.modNat) := rfl

theorem fpe_divNat {p q : ℕ} (a : Fin p) (c : Fin q) :
    (finProdFinEquiv (a, c)).divNat = a := by
  have h := finProdFinEquiv.symm_apply_apply (a, c)
  rw [fpe_symm] at h
  exact (Prod.ext_iff.mp h).1

theorem fpe_modNat {p q : ℕ} (a : Fin p) (c : Fin q) :
    (finProdFinEquiv (a, c)).modNat = c := by
  have h := finProdFinEquiv.symm_apply_apply (a, c)
  rw [fpe_symm] at h
  exact (Prod.ext_iff.mp h).2

/-- Value of the grid transpose on an encoded index: `(a,d)` (row `a`, col `d`)
    maps to value `a + m * d`. -/
theorem gridTranspose_val {m n : ℕ} (a : Fin m) (d : Fin n) :
    (gridTranspose m n (finProdFinEquiv (a, d))).val = (a : ℕ) + m * (d : ℕ) := by
  rw [gridTranspose_apply, finCongr_apply, Fin.coe_cast, fpe_val]

/-- `finCongr` preserves the order. -/
theorem finCongr_lt {a b : ℕ} (h : a = b) (x y : Fin a) :
    (finCongr h x < finCongr h y) ↔ x < y := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, finCongr_apply, finCongr_apply,
    Fin.coe_cast, Fin.coe_cast]

/-- The mixed-radix comparison: the linear order on `Fin (p*q)` of two encoded
    indices is the lexicographic order on `(row, col)`. -/
theorem encode_lt {p q : ℕ} (a b : Fin p) (c d : Fin q) :
    (finProdFinEquiv (a, c) : Fin (p * q)) < finProdFinEquiv (b, d)
      ↔ (a : ℕ) < b ∨ ((a : ℕ) = b ∧ (c : ℕ) < d) := by
  rw [Fin.lt_iff_val_lt_val, fpe_val, fpe_val]
  have hc := c.isLt
  have hd := d.isLt
  rcases lt_trichotomy (a : ℕ) (b : ℕ) with h | h | h
  · have hmul : q * (a : ℕ) + q ≤ q * (b : ℕ) := by
      have := Nat.mul_le_mul_left (k := q) (show (a : ℕ) + 1 ≤ b by omega)
      simpa [Nat.mul_add] using this
    omega
  · have hmul : q * (a : ℕ) = q * (b : ℕ) := by rw [h]
    omega
  · have hmul : q * (b : ℕ) + q ≤ q * (a : ℕ) := by
      have := Nat.mul_le_mul_left (k := q) (show (b : ℕ) + 1 ≤ a by omega)
      simpa [Nat.mul_add] using this
    omega

/-- The number of strictly-increasing pairs over `Fin k` is `C(k,2)`. -/
theorem card_strict_pairs (k : ℕ) :
    (univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).card = k.choose 2 := by
  have h1 : (univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).card
      = ∑ b : Fin k, (b : ℕ) := by
    rw [Finset.card_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    dsimp only
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.card_filter]
    have : (univ.filter (fun a : Fin k => a < b)) = Finset.Iio b := by
      ext a; simp [Finset.mem_Iio]
    rw [this, Fin.card_Iio]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id, ← Nat.choose_two_right]

theorem sign_gridTranspose (m n : ℕ) :
    Equiv.Perm.sign (gridTranspose m n)
      = (-1 : ℤˣ) ^ (Nat.choose m 2 * Nat.choose n 2) := by
  set T := gridTranspose m n with hT
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  -- Each inner product over `Iio J` is `(-1)^(# inversions ending at J)`.
  have inner : ∀ J : Fin (m * n),
      (∏ i ∈ Iio J, (if T i < T J then (1 : ℤˣ) else -1))
        = (-1) ^ ((Iio J).filter (fun i => ¬ (T i < T J))).card := by
    intro J
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  simp_rw [inner]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  -- Reduce the total inversion count to the cardinality of an inversion Finset.
  set Inv : Finset (Fin (m * n) × Fin (m * n)) :=
    univ.filter (fun p => p.1 < p.2 ∧ ¬ (T p.1 < T p.2)) with hInv
  have hsum : (∑ J : Fin (m * n), ((Iio J).filter (fun i => ¬ (T i < T J))).card)
      = Inv.card := by
    rw [hInv, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    dsimp only
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [Finset.card_filter]
    have hIio : (Iio J) = univ.filter (fun i => i < J) := by
      ext i; simp [Finset.mem_Iio]
    rw [hIio, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hh : i < J <;> simp [hh]
  rw [hsum, ← card_strict_pairs m, ← card_strict_pairs n, ← Finset.card_product]
  -- The bijection: (I,J) ↦ ((row I, row J), (col J, col I)).
  refine Finset.card_bij'
    (i := fun p _ => ((p.1.divNat, p.2.divNat), (p.2.modNat, p.1.modNat)))
    (j := fun q _ => (finProdFinEquiv (q.1.1, q.2.2), finProdFinEquiv (q.1.2, q.2.1)))
    ?_ ?_ ?_ ?_
  · -- i maps Inv into the product
    rintro ⟨I, J⟩ hp
    simp only [hInv, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hIJ, hTIJ⟩ := hp
    obtain ⟨a, d, rfl⟩ : ∃ a d, I = finProdFinEquiv (a, d) :=
      ⟨I.divNat, I.modNat, (finProdFinEquiv.apply_symm_apply I).symm⟩
    obtain ⟨b, c, rfl⟩ : ∃ b c, J = finProdFinEquiv (b, c) :=
      ⟨J.divNat, J.modNat, (finProdFinEquiv.apply_symm_apply J).symm⟩
    rw [encode_lt] at hIJ
    rw [hT, gridTranspose_apply, gridTranspose_apply, finCongr_lt, encode_lt] at hTIJ
    simp only [fpe_divNat, fpe_modNat, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val]
    -- hIJ : a < b ∨ (a = b ∧ d < c);  hTIJ : ¬ (d < c ∨ (d = c ∧ a < b))
    -- goal : a < b ∧ c < d
    omega
  · -- j maps the product into Inv
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.lt_iff_val_lt_val] at hq
    obtain ⟨hab, hcd⟩ := hq
    simp only [hInv, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [encode_lt]; exact Or.inl hab
    · rw [hT, not_lt, Fin.le_iff_val_le_val, gridTranspose_val, gridTranspose_val]
      have hb := b.isLt
      have hmul : m * (c : ℕ) + m ≤ m * (d : ℕ) := by
        have := Nat.mul_le_mul_left (k := m) (show (c : ℕ) + 1 ≤ d by omega)
        simpa [Nat.mul_add] using this
      omega
  · -- left inverse
    rintro ⟨I, J⟩ hp
    obtain ⟨a, d, rfl⟩ : ∃ a d, I = finProdFinEquiv (a, d) :=
      ⟨I.divNat, I.modNat, (finProdFinEquiv.apply_symm_apply I).symm⟩
    obtain ⟨b, c, rfl⟩ : ∃ b c, J = finProdFinEquiv (b, c) :=
      ⟨J.divNat, J.modNat, (finProdFinEquiv.apply_symm_apply J).symm⟩
    simp [fpe_divNat, fpe_modNat]
  · -- right inverse
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
    simp [fpe_divNat, fpe_modNat]

end ZGScratch
