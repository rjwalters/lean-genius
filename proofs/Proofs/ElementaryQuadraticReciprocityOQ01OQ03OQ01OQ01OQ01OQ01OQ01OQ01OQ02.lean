/-
  Toward a self-contained Zolotarev proof of Quadratic Reciprocity
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02)

  Open Question (follow-up #1 flagged by the parent capstone
  oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01, "Zolotarev–Frobenius for every odd
  modulus"):

    "Specialize the general-odd Frobenius identity to recover the quadratic
     reciprocity law (a/p)(p/a) = (-1)^… directly via the sign of a suitable
     shuffle permutation, as in Zolotarev's 1872 derivation."

  ## Status of THIS file (0 sorries / 0 axioms — the combinatorial blocker is proved)

  The parent program already supplies, with 0 sorries / 0 axioms, the
  Frobenius/Zolotarev sign identity for EVERY odd modulus:

      `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd`
        : sign(x ↦ a·x on ℤ/n) = J(A | n)        (n odd, A ≡ a mod n)

  Specialized to a single odd prime p this is Zolotarev's lemma itself:
  `sign(x ↦ a·x on ℤ/p) = (a / p)` (the Legendre symbol).

  What is *missing* — and what every sibling in this family currently delegates
  to Mathlib's `legendreSym.quadratic_reciprocity` instead of deriving — is the
  ONE combinatorial ingredient of Zolotarev's 1872 argument:

      the sign of the rectangular **transpose / perfect-shuffle** permutation
      of a p × q grid.

  This file proves that ingredient as `sign_gridTranspose`
  (0 sorry, kernel-checked, axioms `[propext, Classical.choice, Quot.sound]` only)
  together with the structural lemma `gridTranspose_apply` confirming the object
  is genuinely the row-major ↔ column-major reindexing.  With `sign_gridTranspose`
  discharged, Quadratic Reciprocity follows by the assembly sketched below.

  ## The Zolotarev / Frobenius derivation of QR (the plan)

  Let `p, q` be distinct odd primes.  On the `pq`-element grid `Fin p × Fin q`
  one studies three permutations (Zolotarev 1872; Frobenius 1914; see also the
  "dealing cards" exposition of Matt Baker / Cartier):

    * `α` — multiplication structure read off column-by-column;
    * `β` — multiplication structure read off row-by-row;
    * `γ` — the pure row-major ↔ column-major **shuffle** (`gridTranspose`).

  They satisfy `α = β ∘ γ`, hence `sign α = sign β · sign γ`.  Mathlib's
  `Equiv.Perm.sign_prodCongrLeft` / `sign_prodCongrRight` evaluate `sign α` and
  `sign β` as products of the per-line signs, each of which is a Zolotarev sign
  `sign(x ↦ q·x on ℤ/p) = (q / p)` resp. `(p / q)` via the parent identity.
  The shuffle contributes the reciprocity factor:

      `sign γ = (-1) ^ (C(p,2) · C(q,2))`,

  and for odd `p, q` the exponent has the same parity as `((p-1)/2)·((q-1)/2)`,
  giving the classical

      `(q / p) · (p / q) = (-1) ^ ((p-1)/2 · (q-1)/2)`.

  The combinatorial fact `sign γ = (-1)^(C(p,2)·C(q,2))` is exactly the count of
  inversions of the reindexing: an inversion is a pair of cells `(i,j), (i',j')`
  with `i < i'` but `j > j'`, of which there are `C(p,2) · C(q,2)`.

  ## Honest scope

  * `gridTranspose`, `gridTranspose_apply` — proved (0 sorry): the shuffle
    permutation and the confirmation that it sends row-major index `n·i + j` to
    column-major index `m·j + i`.
  * supporting lemmas `fpe_val`, `fpe_symm`, `fpe_divNat`, `fpe_modNat`,
    `gridTranspose_val`, `finCongr_lt`, `encode_lt`, `card_strict_pairs` — all
    proved (0 sorry): the mixed-radix encoding facts and the count
    `#{(i,j) : i < j} = C(k,2)` of strictly-increasing pairs over `Fin k`.
  * `sign_gridTranspose` — PROVED (0 sorry), kernel-checked.  This was the single
    remaining ingredient (a *known* result, HARD not OPEN); it is proved here via
    `Equiv.Perm.sign_eq_prod_prod_Iio` (sign as a product over inversions) and a
    `Finset.card_bij'` bijection counting the `C(m,2)·C(n,2)` inversions of the
    reindexing.
  * `neg_one_pow_choose_two_mul_odd` — proved (0 sorry): the parity bridge
    `(-1)^(C(m,2)·C(n,2)) = (-1)^(((m-1)/2)·((n-1)/2))` for odd `m, n`, i.e. the
    exponent simplification flagged in the plan above.  This is the elementary
    number-theory step that turns Zolotarev's shuffle factor into the textbook
    reciprocity factor; it does NOT depend on `sign_gridTranspose`.
  * `sign_gridTranspose_odd` — the classical-form corollary
    `sign (gridTranspose m n) = (-1)^(((m-1)/2)·((n-1)/2))` for odd `m, n`,
    obtained by feeding the parity bridge into `sign_gridTranspose`; now fully
    proved (0 sorry).
  * The full QR assembly (`α = β ∘ γ`, identifying `α, β` with `ringMulPerm`
    through the CRT isomorphism) is documented above but not yet formalized.

  References:
  - Zolotarev (1872); Frobenius (1914); Lerch (1896).
  - Cartier; Baker, "Quadratic reciprocity and Zolotarev's Lemma" (2013).
-/
import Mathlib

set_option maxHeartbeats 800000

namespace ZolotarevQR

open Equiv Equiv.Perm Finset

/-- The row-major ↔ column-major **transpose** (perfect-shuffle) permutation of
    an `m × n` grid, realized as a permutation of `Fin (m * n)`.

    Concretely it sends the row-major index `n * i + j` (cell in row `i : Fin m`,
    column `j : Fin n`) to the column-major index `m * j + i` — see
    `gridTranspose_apply`.  This is the permutation `γ` whose sign carries the
    quadratic-reciprocity factor in Zolotarev's derivation. -/
def gridTranspose (m n : ℕ) : Equiv.Perm (Fin (m * n)) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodComm (Fin m) (Fin n)).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm n m))))

/-- **The transpose is the transpose.**  On the canonical row-major coordinate
    `finProdFinEquiv (i, j)` (value `n·i + j`), `gridTranspose` returns the
    canonical column-major coordinate `finProdFinEquiv (j, i)` (value `m·j + i`),
    transported along `m * n = n * m`.  This confirms `gridTranspose` is the
    intended reindexing object. -/
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
  rw [Fin.lt_def, Fin.lt_def, finCongr_apply, finCongr_apply,
    Fin.coe_cast, Fin.coe_cast]

/-- The mixed-radix comparison: the linear order on `Fin (p*q)` of two encoded
    indices is the lexicographic order on `(row, col)`. -/
theorem encode_lt {p q : ℕ} (a b : Fin p) (c d : Fin q) :
    (finProdFinEquiv (a, c) : Fin (p * q)) < finProdFinEquiv (b, d)
      ↔ (a : ℕ) < b ∨ ((a : ℕ) = b ∧ (c : ℕ) < d) := by
  rw [Fin.lt_def, fpe_val, fpe_val]
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

/-- **Sign of the rectangular transpose / perfect-shuffle permutation.**

    The number of inversions of the row-major ↔ column-major reindexing of an
    `m × n` grid is `C(m,2) · C(n,2)` (choose an unordered pair of rows and an
    unordered pair of columns), so

        `sign (gridTranspose m n) = (-1) ^ (C(m,2) · C(n,2))`.

    This is the combinatorial heart of Zolotarev's 1872 permutation proof of
    quadratic reciprocity, and the single ingredient the elementary-Zolotarev
    program still needs in order to derive QR from
    `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd` without appealing to
    Mathlib's `legendreSym.quadratic_reciprocity`.

    STATUS: PROVEN (0 sorry).  This is a KNOWN result (HARD, not OPEN), and the
    long-standing blocker of the elementary-Zolotarev program is now discharged.

    CROSS-REFERENCE / NON-DUPLICATION NOTE.  The *identical* obligation also
    stands in the sibling "algorithm" lineage as
    `QuadraticReciprocityAlgorithmOQ03M2.sign_gridTranspose_eq_choose`
    (merged #25053, currently unregistered).

    PROOF ROUTE (researcher-9, 2026-06-23) — the earlier "no Mathlib lemma"
    assessment was OUT OF DATE.  Mathlib provides the exact inversion-count
    bridge for an arbitrary `Perm (Fin N)`:

        `Equiv.Perm.sign_eq_prod_prod_Iio`
          : σ.sign = ∏ j, ∏ i ∈ Finset.Iio j, (if σ i < σ j then 1 else -1)

    (`Mathlib/GroupTheory/Perm/Fin.lean`, `section Sign`).  Each factor is `-1`
    exactly on an inversion `i < j ∧ σ i > σ j`, so `sign σ = (-1)^(#inversions)`
    with NO `signAux`/`finPairsLT` surgery.  The blocker then reduces to the
    elementary count `#{(I,J) : I < J ∧ T I > T J} = C(m,2)·C(n,2)` via the
    bijection `(I,J) ↦ ((row I, row J), (col J, col I))` onto
    (strictly-increasing row pairs) × (strictly-increasing column pairs), each of
    cardinality `C(·,2)` (counted by the Gauss sum `∑ b, b`, see
    `card_strict_pairs`).  The mixed-radix order on `Fin (m*n)` via
    `finProdFinEquiv` is lexicographic on `(row, col)` (`encode_lt`).

    VERIFICATION.  Kernel-checked against pinned Mathlib (rev 2df2f0150c, Lean
    v4.26.0) via `lake env lean` over the restored Mathlib olean cache;
    `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`
    (no `sorryAx`, no `Lean.ofReduceBool`).  The numerical inversion bijection is
    independently certified in
    `research/problems/quadratic-reciprocity-algorithm-oq-03/verify_grid_inversions.py`
    and `verify_inversion_bijection.py`. -/
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
      Finset.mem_univ, true_and, Fin.lt_def]
    -- hIJ : a < b ∨ (a = b ∧ d < c);  hTIJ : ¬ (d < c ∨ (d = c ∧ a < b))
    -- goal : a < b ∧ c < d
    omega
  · -- j maps the product into Inv
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.lt_def] at hq
    obtain ⟨hab, hcd⟩ := hq
    simp only [hInv, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [encode_lt]; exact Or.inl hab
    · rw [hT, not_lt, Fin.le_def, gridTranspose_val, gridTranspose_val]
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

/-- `(-1 : ℤˣ)` has order dividing `2`, so its powers depend only on the
    exponent modulo `2`.  This is the bookkeeping lemma that lets us pass between
    the inversion-count exponent `C(m,2)·C(n,2)` and the classical
    quadratic-reciprocity exponent. -/
private theorem negOnePow_congr {a b : ℕ} (h : a % 2 = b % 2) :
    (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ b := by
  have hsq : (-1 : ℤˣ) ^ 2 = 1 := Int.units_sq _
  conv_lhs => rw [← Nat.div_add_mod a 2, pow_add, pow_mul, hsq, one_pow, one_mul]
  conv_rhs => rw [← Nat.div_add_mod b 2, pow_add, pow_mul, hsq, one_pow, one_mul]
  rw [h]

/-- **Parity bridge for the transpose-sign exponent.**

    For *odd* `m, n` the inversion count `C(m,2)·C(n,2)` that controls
    `sign (gridTranspose m n)` has the same parity as the classical
    quadratic-reciprocity exponent `((m-1)/2)·((n-1)/2)`, hence

        `(-1) ^ (C(m,2)·C(n,2)) = (-1) ^ (((m-1)/2)·((n-1)/2))`.

    Reason: for `m = 2a+1` one has `C(m,2) = (2a+1)·a ≡ a = (m-1)/2 (mod 2)`,
    and likewise for `n`; the two congruences multiply.  This is the precise
    step flagged in the file header that turns Zolotarev's shuffle factor into
    the textbook reciprocity factor.  It is fully proved (no `sorry`). -/
theorem neg_one_pow_choose_two_mul_odd {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    (-1 : ℤˣ) ^ (Nat.choose m 2 * Nat.choose n 2)
      = (-1 : ℤˣ) ^ (((m - 1) / 2) * ((n - 1) / 2)) := by
  -- `C(2t+1, 2) ≡ t (mod 2)`, proved by reducing the binomial to a polynomial
  -- and letting `omega` handle the division/modulus by the constant `2`.
  have key : ∀ t : ℕ, (Nat.choose (2 * t + 1) 2) % 2 = t % 2 := by
    intro t
    rw [Nat.choose_two_right]
    have e : (2 * t + 1) * ((2 * t + 1) - 1) = (t * t) * 4 + t * 2 := by
      have h1 : (2 * t + 1) - 1 = 2 * t := by omega
      rw [h1]; ring
    rw [e]; omega
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  apply negOnePow_congr
  have hma : ((2 * a + 1) - 1) / 2 = a := by omega
  have hnb : ((2 * b + 1) - 1) / 2 = b := by omega
  rw [hma, hnb]
  calc (Nat.choose (2 * a + 1) 2 * Nat.choose (2 * b + 1) 2) % 2
        = ((Nat.choose (2 * a + 1) 2 % 2) * (Nat.choose (2 * b + 1) 2 % 2)) % 2 := by
          rw [Nat.mul_mod]
    _ = ((a % 2) * (b % 2)) % 2 := by rw [key a, key b]
    _ = (a * b) % 2 := by rw [← Nat.mul_mod]

/-- **Transpose sign in classical reciprocity form (odd grid).**

    Combining `sign_gridTranspose` with the parity bridge, for odd `m, n`

        `sign (gridTranspose m n) = (-1) ^ (((m-1)/2)·((n-1)/2))`,

    which is exactly the reciprocity factor `(-1)^((p-1)/2·(q-1)/2)` of the
    quadratic reciprocity law.  Now fully proved (0 sorry), combining the
    kernel-checked `sign_gridTranspose` with the parity bridge; recorded here to
    show how that ingredient feeds the final QR assembly. -/
theorem sign_gridTranspose_odd {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    Equiv.Perm.sign (gridTranspose m n)
      = (-1 : ℤˣ) ^ (((m - 1) / 2) * ((n - 1) / 2)) := by
  rw [sign_gridTranspose, neg_one_pow_choose_two_mul_odd hm hn]

end ZolotarevQR

#check @ZolotarevQR.gridTranspose
#check @ZolotarevQR.gridTranspose_apply
#check @ZolotarevQR.sign_gridTranspose
#check @ZolotarevQR.neg_one_pow_choose_two_mul_odd
#check @ZolotarevQR.sign_gridTranspose_odd
