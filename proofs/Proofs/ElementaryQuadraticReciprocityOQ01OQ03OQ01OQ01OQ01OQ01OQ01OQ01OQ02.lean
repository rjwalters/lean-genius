/-
  Toward a self-contained Zolotarev proof of Quadratic Reciprocity
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02)

  Open Question (follow-up #1 flagged by the parent capstone
  oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01, "Zolotarev–Frobenius for every odd
  modulus"):

    "Specialize the general-odd Frobenius identity to recover the quadratic
     reciprocity law (a/p)(p/a) = (-1)^… directly via the sign of a suitable
     shuffle permutation, as in Zolotarev's 1872 derivation."

  ## Status of THIS file (0 sorries — UNCONDITIONAL Zolotarev QR is now complete)

  The capstone `zolotarev_quadratic_reciprocity` derives the full law
  `(q/p)·(p/q) = (-1)^((p-1)/2·(q-1)/2)` for distinct odd primes `p, q` entirely
  from the sign-of-permutation calculus, with NO hypotheses and NO appeal to
  Mathlib's `legendreSym.quadratic_reciprocity` (axioms `[propext,
  Classical.choice, Quot.sound]` only).  The earlier sections build toward it:

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
  * **QR assembly skeleton (NEW, this file, §"Assembly" below).**  Following the
    "proof from the book" reworking of Zolotarev's argument (J. Shurman, after
    Baker 2013), QR is the single relation `sign τ_cd · sign τ_rd = sign τ_rc`
    among the three *order-transition* permutations of the `p × q` array
    (row-major `R`, column-major `C`, diagonal/CRT `D`):

        τ_rd = D⁻¹∘R,   τ_cd = D⁻¹∘C,   τ_rc = C⁻¹∘R,     with τ_cd⁻¹∘τ_rd = τ_rc.

    Shurman's signs are `sign τ_cd = (p/q)`, `sign τ_rd = (q/p)` (Zolotarev's
    lemma applied per residue line) and `sign τ_rc = (-1)^((p-1)/2·(q-1)/2)`
    (the inversion count — which is exactly `sign_gridTranspose` above, since
    `τ_rc` IS `gridTranspose p q` transported across `R`).  Substituting yields
    `(p/q)·(q/p) = (-1)^((p-1)/2·(q-1)/2)`.

    `quadratic_reciprocity_of_transition_signs` below formalizes this skeleton
    with **0 sorries**: the tautological composition `τ_cd⁻¹∘τ_rd = τ_rc`, the
    sign-product reduction, and the identification `sign τ_rc = sign gridTranspose`
    (`sign_transRC`) — reducing QR to the two per-line Zolotarev sign facts,
    supplied here as hypotheses.  (The PREVIOUS plan above mis-stated the assembly
    as "α = β∘γ identifying α,β with `ringMulPerm` via the CRT isomorphism"; the
    correct objects are the three transition permutations, and α,β are NOT
    `ringMulPerm` on `ℤ/pq` but per-line multiplication maps on `ℤ/q` resp `ℤ/p`.)

  ## What remains — NOTHING: the gap is now closed (`zolotarev_quadratic_reciprocity`)

  The two transition-sign hypotheses are now DISCHARGED for a concrete CRT order
  `crtOrder` (§"Closing the gap" below), and the capstone
  `zolotarev_quadratic_reciprocity` is **unconditional** (0 sorries, axioms
  `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no `ofReduceBool`,
  and no appeal to Mathlib's `legendreSym.quadratic_reciprocity`).

  The *per-line number-theoretic step* is `sign_affineLine_eq_legendreSym`
  (§"Per-line Zolotarev sign"): for an odd prime `m` the sign of the affine
  permutation `x ↦ a·x + b` of `ℤ/m` is the Legendre symbol `(a / m)`.  The
  translation summand `x ↦ x + b` is an *even* permutation — it has odd order on
  the odd-order group `ℤ/m`, so its sign is `+1` (`sign_addLeft_odd`, absent from
  Mathlib) — and the multiplication factor is Zolotarev's lemma in Frobenius form
  (`ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd = legendreSym` at a prime).

  The (previously open) COMBINATORIAL step is `sign_rowTransition` /
  `sign_colTransition`: the concrete order `crtOrder` transports the Chinese-
  remainder isomorphism `ℤ/pq ≃ ℤ/p × ℤ/q` across `ZMod.finEquiv`; conjugating
  `crtOrder⁻¹∘rowOrder` by `arrEquiv : Fin p × Fin q ≃ ℤ/p × ℤ/q` (and
  `crtOrder⁻¹∘colOrder` by the swap) realizes each transition LITERALLY as a
  `prodCongrLeft` of the per-line affine maps `x ↦ q·x + ↑j` (resp. `x ↦ p·x + ↑i`).
  `sign_prodCongrLeft_affineLine` then collapses the `q`-fold (resp. `p`-fold)
  product to the single Legendre symbol `(q/p)` (resp. `(p/q)`), and the
  three-transition skeleton assembles QR.  No further Zolotarev/Jacobi input.

  References:
  - Zolotarev (1872); Frobenius (1914); Lerch (1896).
  - Cartier; Baker, "Quadratic reciprocity and Zolotarev's Lemma" (2013).
  - J. Shurman, "Zolotarev's proof of quadratic reciprocity",
    https://people.reed.edu/~jerry/361/lectures/qrz.pdf (the three-transition
    "card trick" formulation used here).
-/
import Mathlib
-- Zolotarev's lemma in Frobenius form (`sign(x ↦ a·x on ℤ/n) = J(A|n)`, n odd),
-- used below to discharge the per-residue-line transition signs.
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01

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

/-! ## Assembly: quadratic reciprocity from the three transition signs

The Zolotarev/Shurman "card-trick" skeleton.  The three linear orders on the
`p × q` array are realized as bijections `Fin p × Fin q ≃ Fin (p*q)`: row-major
`rowOrder`, column-major `colOrder`, and the diagonal/CRT order (an abstract
parameter `D` below).  The transition permutations of the array are then
`τ_rd = D⁻¹∘rowOrder`, `τ_cd = D⁻¹∘colOrder`, `τ_rc = colOrder⁻¹∘rowOrder`, and
the tautology `τ_cd⁻¹∘τ_rd = τ_rc` is quadratic reciprocity once the three signs
are known. -/

/-- Row-major order on the `p × q` array: `(i, j) ↦ q·i + j`.  This is the same
    `finProdFinEquiv` underlying `gridTranspose`. -/
def rowOrder (p q : ℕ) : Fin p × Fin q ≃ Fin (p * q) := finProdFinEquiv

/-- Column-major order on the `p × q` array: `(i, j) ↦ i + p·j`.  This is exactly
    the codomain factor of `gridTranspose`, so `gridTranspose = rowOrder⁻¹ ∘ colOrder`
    holds definitionally (`gridTranspose_eq`). -/
def colOrder (p q : ℕ) : Fin p × Fin q ≃ Fin (p * q) :=
  (Equiv.prodComm (Fin p) (Fin q)).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm q p)))

/-- `gridTranspose p q` is the row→column transition read on linear indices. -/
theorem gridTranspose_eq (p q : ℕ) :
    gridTranspose p q = (rowOrder p q).symm.trans (colOrder p q) := rfl

/-- The **row→column transition** permutation of the array, `colOrder⁻¹ ∘ rowOrder`. -/
def transRC (p q : ℕ) : Equiv.Perm (Fin p × Fin q) :=
  (rowOrder p q).trans (colOrder p q).symm

/-- The array transition `transRC` and the linear-index shuffle `gridTranspose`
    are conjugate via `rowOrder`, hence share their sign. -/
theorem sign_transRC (p q : ℕ) :
    Equiv.Perm.sign (transRC p q) = Equiv.Perm.sign (gridTranspose p q) := by
  have h : ∀ x, (rowOrder p q) (transRC p q x)
      = (gridTranspose p q)⁻¹ ((rowOrder p q) x) := by
    intro x
    rw [gridTranspose_eq]
    simp only [transRC, Equiv.Perm.inv_def, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_symm]
  rw [Equiv.Perm.sign_eq_sign_of_equiv (transRC p q) (gridTranspose p q)⁻¹ (rowOrder p q) h,
    map_inv]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (gridTranspose p q)) with h2 | h2 <;> simp [h2]

/-- **Quadratic reciprocity via the Zolotarev/Shurman transition skeleton.**

    Let `p, q` be odd primes and `D : Fin p × Fin q ≃ Fin (p*q)` the diagonal
    (CRT) ordering of the array.  If the row→diagonal and column→diagonal
    transitions carry the Zolotarev signs `(q/p)` and `(p/q)` (Shurman §3 — each
    restricts to multiplication permutations on a single residue line, whose sign
    is a Legendre symbol by Zolotarev's lemma), then the quadratic reciprocity law

        `(p/q)·(q/p) = (-1)^((p-1)/2·(q-1)/2)`

    follows.  The proof is the tautological composition `τ_cd⁻¹∘τ_rd = τ_rc`, the
    sign-product reduction, the identification `sign τ_rc = sign (gridTranspose)`
    (`sign_transRC`), and the proven `sign_gridTranspose_odd`.  This reduces QR to
    the two per-line Zolotarev sign facts, supplied here as hypotheses. -/
theorem quadratic_reciprocity_of_transition_signs
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : Odd p) (hq : Odd q)
    (D : Fin p × Fin q ≃ Fin (p * q))
    (hrd : (Equiv.Perm.sign ((rowOrder p q).trans D.symm) : ℤ) = legendreSym p (q : ℤ))
    (hcd : (Equiv.Perm.sign ((colOrder p q).trans D.symm) : ℤ) = legendreSym q (p : ℤ)) :
    legendreSym q (p : ℤ) * legendreSym p (q : ℤ)
      = (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
  set τrd : Equiv.Perm (Fin p × Fin q) := (rowOrder p q).trans D.symm with hτrd
  set τcd : Equiv.Perm (Fin p × Fin q) := (colOrder p q).trans D.symm with hτcd
  -- Tautological composition: τ_cd⁻¹ ∘ τ_rd = τ_rc (the `D⁻¹`s cancel).
  have hcomp : τcd⁻¹ * τrd = transRC p q := by
    refine Equiv.ext fun z => ?_
    simp only [hτcd, hτrd, transRC, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.inv_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.trans_apply,
      Equiv.apply_symm_apply]
  -- Sign is multiplicative and `ℤˣ` has exponent 2, so signs multiply.
  have hsign : Equiv.Perm.sign τcd * Equiv.Perm.sign τrd
      = Equiv.Perm.sign (transRC p q) := by
    rw [← hcomp, map_mul, map_inv]
    have hself : (Equiv.Perm.sign τcd)⁻¹ = Equiv.Perm.sign τcd := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τcd) with h | h <;> simp [h]
    rw [hself]
  -- Evaluate `sign τ_rc` through `gridTranspose`.
  rw [sign_transRC, sign_gridTranspose_odd hp hq] at hsign
  -- Cast the `ℤˣ` identity to `ℤ` and substitute the two Zolotarev signs.
  have hZ : (Equiv.Perm.sign τcd : ℤ) * (Equiv.Perm.sign τrd : ℤ)
      = (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
    have hcast := congrArg (fun u : ℤˣ => (u : ℤ)) hsign
    push_cast at hcast
    simpa using hcast
  rwa [hcd, hrd] at hZ

/-! ### Per-line Zolotarev sign: discharging the transition-sign hypotheses

The two hypotheses of `quadratic_reciprocity_of_transition_signs` are *per residue
line* facts.  For the CRT order `D` (Shurman §3), the transition `D⁻¹∘rowOrder`
fixes each column `j` and acts on the row index by the **affine** map
`i ↦ q·i + j (mod p)`; dually `D⁻¹∘colOrder` acts per row by `j ↦ p·j + i (mod q)`.
The sign of one such affine permutation of `ZMod p` is the Legendre symbol `(q/p)`:
the translation summand is an *even* permutation — it has odd order on the
odd-order group `ZMod p`, hence sign `+1` — and the multiplication factor is
Zolotarev's lemma in Frobenius form
(`ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd`).  These lemmas supply the
remaining number-theoretic ingredient flagged in the file header; the only step
left to make `quadratic_reciprocity_of_transition_signs` unconditional is the
purely combinatorial identification of each transition with `prodCongrLeft` of
these affine maps (`sign_prodCongrLeft` then collapses the `q`-fold product since
`(q/p)^q = (q/p)`). -/

open ZolotarevCRT (ringMulPerm)

/-- `n • b = 0` in `ZMod n`: the additive group has exponent dividing `n`. -/
private theorem nsmul_self_zmod {n : ℕ} (b : ZMod n) : n • b = 0 := by
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- **Translation is an even permutation on an odd-order group.**  For odd `n`,
    the translation `x ↦ b + x` of `ZMod n` has sign `+1`: its order divides `n`
    (because `n • b = 0`), so the order is odd, while `sign` lands in the
    order-`2` group `ℤˣ`; thus an odd power of the sign equals the sign, and that
    power is `sign 1 = 1`.  (Absent from Mathlib.) -/
theorem sign_addLeft_odd {n : ℕ} [NeZero n] (hodd : Odd n) (b : ZMod n) :
    Equiv.Perm.sign (Equiv.addLeft b) = 1 := by
  set u : ℤˣ := Equiv.Perm.sign (Equiv.addLeft b) with hu
  have hpow : (Equiv.addLeft b) ^ n = 1 := by
    rw [pow_addLeft, nsmul_self_zmod, addLeft_zero]
  have hun : u ^ n = 1 := by rw [hu, ← map_pow, hpow, map_one]
  rw [← ZolotarevCRT.units_pow_odd u hodd]; exact hun

/-- **Affine sign = multiplication sign on an odd-order group.**  Composing any
    permutation `P` of `ZMod n` (odd `n`) with a translation leaves the sign
    unchanged. -/
theorem sign_addLeft_mul {n : ℕ} [NeZero n] (hodd : Odd n)
    (b : ZMod n) (P : Equiv.Perm (ZMod n)) :
    Equiv.Perm.sign (Equiv.addLeft b * P) = Equiv.Perm.sign P := by
  rw [map_mul, sign_addLeft_odd hodd, one_mul]

/-- **Per-line Zolotarev sign (prime modulus).**  For an odd prime `p`, a unit
    `a : (ℤ/p)ˣ`, any translation `b`, and any integer representative `A ≡ a
    (mod p)`, the sign of the affine permutation `x ↦ a·x + b` of `ℤ/p` is the
    Legendre symbol `(A / p)`.  This combines the translation-parity lemma above
    with Zolotarev's lemma in Frobenius form
    (`ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd`), and is exactly the
    sign of a single residue line of the CRT transition permutations `τ_rd`,
    `τ_cd`.  It discharges the *per-line* content of the two hypotheses of
    `quadratic_reciprocity_of_transition_signs`. -/
theorem sign_affineLine_eq_legendreSym {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (a : (ZMod p)ˣ) (b : ZMod p) (A : ℤ) (hA : (A : ZMod p) = (a : ZMod p)) :
    (Equiv.Perm.sign (Equiv.addLeft b * ringMulPerm a) : ℤ) = legendreSym p A := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  rw [sign_addLeft_mul hodd b (ringMulPerm a),
      ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd hodd a A hA,
      jacobiSym.legendreSym.to_jacobiSym]

/-- **Collapse of the per-line signs over a residue array.**

    Let `p` be an odd prime and `q` an odd number.  Consider a permutation of the
    array `ZMod p × ZMod q` that acts *fiberwise over the `ZMod q` factor* as the
    affine line map `x ↦ a·x + β k` on the `ZMod p` factor, i.e.

        `prodCongrLeft (fun k : ZMod q => addLeft (β k) * ringMulPerm a)`.

    Its total sign is the *single* per-line Legendre symbol `(A / p)`:
    `sign_prodCongrLeft` turns the sign into the product of the `q` fiber signs;
    each fiber sign is `(A/p)` (translation is even, `sign_affineLine_eq_legendreSym`);
    and the `q`-fold product `(A/p)^q` collapses to `(A/p)` because `q` is odd and
    the sign is a unit (`units_pow_odd`).

    This is exactly the "`sign_prodCongrLeft` collapses the `q`-fold product" step
    flagged at the end of the file header.  Together with the CRT identification of
    each transition `τ_rd`, `τ_cd` as such a fiberwise-affine permutation, it
    discharges the two hypotheses of `quadratic_reciprocity_of_transition_signs`;
    the *only* remaining gap is that purely combinatorial identification. -/
theorem sign_prodCongrLeft_affineLine {p q : ℕ} [hp : Fact p.Prime] [NeZero q]
    (hp2 : p ≠ 2) (hq : Odd q) (a : (ZMod p)ˣ) (β : ZMod q → ZMod p)
    (A : ℤ) (hA : (A : ZMod p) = (a : ZMod p)) :
    (Equiv.Perm.sign (Equiv.prodCongrLeft
        (fun k : ZMod q => Equiv.addLeft (β k) * ringMulPerm a)) : ℤ)
      = legendreSym p A := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  rw [Equiv.Perm.sign_prodCongrLeft]
  -- every fiber sign collapses (translation is even) to `sign (ringMulPerm a)`.
  have hfib : (fun k : ZMod q => Equiv.Perm.sign (Equiv.addLeft (β k) * ringMulPerm a))
      = fun _ : ZMod q => Equiv.Perm.sign (ringMulPerm a) :=
    funext fun k => sign_addLeft_mul hodd (β k) (ringMulPerm a)
  rw [hfib, Finset.prod_const, Finset.card_univ, ZMod.card q,
      ZolotarevCRT.units_pow_odd _ hq]
  -- the surviving single line is the `b = 0` instance of the affine-line sign.
  have h0 := sign_affineLine_eq_legendreSym hp2 a 0 A hA
  rwa [sign_addLeft_mul hodd 0 (ringMulPerm a)] at h0

/-! ### Closing the gap: the concrete CRT order and both transition signs

This section discharges the two hypotheses of
`quadratic_reciprocity_of_transition_signs` for a *concrete* diagonal/CRT order
`crtOrder`, yielding the fully unconditional Zolotarev derivation of quadratic
reciprocity `zolotarev_quadratic_reciprocity` (0 hypotheses beyond `p, q` distinct
odd primes).

The order transports the Chinese-remainder isomorphism
`ZMod (p*q) ≃+* ZMod p × ZMod q` across the canonical `Fin n ≃ ZMod n`
(`ZMod.finEquiv`):

    `crtOrder.symm : Fin (p*q) ≃ Fin p × Fin q`,  `z ↦ (z mod p, z mod q)`.

Conjugating the row→diagonal transition `crtOrder⁻¹ ∘ rowOrder` across
`arrEquiv : Fin p × Fin q ≃ ZMod p × ZMod q` turns it into the fiberwise-affine
permutation `(x, y) ↦ (q·x + ↑j, y)` of `ZMod p × ZMod q`, whose sign is `(q/p)`
by `sign_prodCongrLeft_affineLine`.  Dually the column transition has sign `(p/q)`
on `ZMod q × ZMod p`.  Substituting into the skeleton gives reciprocity. -/

/-- `ZMod.finEquiv` is the identity on the underlying `Fin`, so it preserves `val`. -/
private theorem finEquiv_val {n : ℕ} [NeZero n] (i : Fin n) :
    (ZMod.finEquiv n i).val = i.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rfl

/-- `ZMod.finEquiv n i` is the residue class of `i.val`. -/
private theorem finEquiv_eq_natCast {n : ℕ} [NeZero n] (i : Fin n) :
    (ZMod.finEquiv n i) = (i.val : ZMod n) := by
  have h := ZMod.natCast_rightInverse (n := n) (ZMod.finEquiv n i)
  rw [finEquiv_val] at h
  exact h.symm

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- The array `Fin p × Fin q` identified with `ZMod p × ZMod q` via `ZMod.finEquiv`. -/
private def arrEquiv : Fin p × Fin q ≃ ZMod p × ZMod q :=
  (ZMod.finEquiv p).toEquiv.prodCongr (ZMod.finEquiv q).toEquiv

@[simp] private theorem arrEquiv_apply (i : Fin p) (j : Fin q) :
    arrEquiv (i, j) = (ZMod.finEquiv p i, ZMod.finEquiv q j) := rfl

/-- The diagonal / CRT order on the `p × q` array: its inverse is the
    Chinese-remainder map `z ↦ (z mod p, z mod q)` read through `ZMod.finEquiv`. -/
noncomputable def crtOrder (hpq : p.Coprime q) [NeZero (p * q)] :
    Fin p × Fin q ≃ Fin (p * q) :=
  ((ZMod.finEquiv (p * q)).toEquiv.trans
    ((ZMod.chineseRemainder hpq).toEquiv.trans arrEquiv.symm)).symm

/-- The defining property of `crtOrder`: conjugating `crtOrder⁻¹` by `arrEquiv`
    recovers the Chinese-remainder isomorphism on linear indices. -/
private theorem arrEquiv_crtOrder_symm (hpq : p.Coprime q) [NeZero (p * q)]
    (z : Fin (p * q)) :
    arrEquiv ((crtOrder hpq).symm z)
      = (ZMod.chineseRemainder hpq) (ZMod.finEquiv (p * q) z) := by
  simp only [crtOrder, Equiv.symm_symm, Equiv.trans_apply, Equiv.apply_symm_apply,
    RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]

/-- **Row→diagonal transition sign.**  For distinct odd primes `p, q`, the row→CRT
    transition `crtOrder⁻¹ ∘ rowOrder` of the `p × q` array has sign equal to the
    Legendre symbol `(q / p)`.  Conjugating across `arrEquiv` makes it the
    fiberwise-affine permutation `(x, y) ↦ (q·x + ↑j, y)` of `ZMod p × ZMod q`,
    and `sign_prodCongrLeft_affineLine` evaluates its sign. -/
private theorem sign_rowTransition [Fact p.Prime] (hp2 : p ≠ 2) (hq : Odd q)
    (hpq : p.Coprime q) [NeZero (p * q)] :
    ((Equiv.Perm.sign ((rowOrder p q).trans (crtOrder hpq).symm) : ℤ))
      = legendreSym p (q : ℤ) := by
  have hqp : q.Coprime p := hpq.symm
  set a : (ZMod p)ˣ := ZMod.unitOfCoprime q hqp with ha
  set β : ZMod q → ZMod p := fun k => (((ZMod.finEquiv q).symm k).val : ZMod p) with hβ
  -- The conjugated permutation is fiberwise affine over `ZMod q`.
  have hconj : ∀ x : Fin p × Fin q,
      arrEquiv (((rowOrder p q).trans (crtOrder hpq).symm) x)
        = (Equiv.prodCongrLeft fun k : ZMod q => Equiv.addLeft (β k) * ringMulPerm a)
            (arrEquiv x) := by
    rintro ⟨i, j⟩
    rw [Equiv.trans_apply, arrEquiv_crtOrder_symm]
    have hidx : (ZMod.finEquiv (p * q) ((rowOrder p q) (i, j)))
        = ((j.val + q * i.val : ℕ) : ZMod (p * q)) := by
      rw [finEquiv_eq_natCast]; rfl
    rw [hidx, arrEquiv_apply, Equiv.prodCongrLeft_apply, Equiv.Perm.mul_apply,
      ZolotarevCRT.ringMulPerm_apply, Equiv.coe_addLeft]
    refine Prod.ext ?_ ?_
    · -- first coordinate (mod p)
      rw [ZolotarevFullOdd.chineseRemainder_fst, map_natCast, hβ, ha,
        ZMod.coe_unitOfCoprime]
      simp only [RingEquiv.symm_apply_apply]
      rw [finEquiv_eq_natCast]
      push_cast
      ring
    · -- second coordinate (mod q)
      rw [ZolotarevFullOdd.chineseRemainder_snd, map_natCast, finEquiv_eq_natCast]
      push_cast
      rw [ZMod.natCast_self]
      ring
  have hsign := Equiv.Perm.sign_eq_sign_of_equiv
    ((rowOrder p q).trans (crtOrder hpq).symm)
    (Equiv.prodCongrLeft fun k : ZMod q => Equiv.addLeft (β k) * ringMulPerm a)
    arrEquiv hconj
  have hA : ((q : ℤ) : ZMod p) = (a : ZMod p) := by
    rw [ha, ZMod.coe_unitOfCoprime]; push_cast; ring
  have key := sign_prodCongrLeft_affineLine (p := p) (q := q) hp2 hq a β (q : ℤ) hA
  rw [hsign]; exact key

/-- **Column→diagonal transition sign.**  Dual to `sign_rowTransition`: the
    column→CRT transition `crtOrder⁻¹ ∘ colOrder` has sign `(p / q)`.  Conjugating
    across `arrEquiv` composed with the coordinate swap makes it the
    fiberwise-affine permutation `(x, y) ↦ (p·x + ↑i, y)` of `ZMod q × ZMod p`. -/
private theorem sign_colTransition [Fact q.Prime] (hq2 : q ≠ 2) (hp : Odd p)
    (hpq : p.Coprime q) [NeZero (p * q)] :
    ((Equiv.Perm.sign ((colOrder p q).trans (crtOrder hpq).symm) : ℤ))
      = legendreSym q (p : ℤ) := by
  set a' : (ZMod q)ˣ := ZMod.unitOfCoprime p hpq with ha'
  set β' : ZMod p → ZMod q := fun k => (((ZMod.finEquiv p).symm k).val : ZMod q) with hβ'
  set ec : Fin p × Fin q ≃ ZMod q × ZMod p :=
    arrEquiv.trans (Equiv.prodComm (ZMod p) (ZMod q)) with hec
  have hconj : ∀ x : Fin p × Fin q,
      ec (((colOrder p q).trans (crtOrder hpq).symm) x)
        = (Equiv.prodCongrLeft fun k : ZMod p => Equiv.addLeft (β' k) * ringMulPerm a')
            (ec x) := by
    rintro ⟨i, j⟩
    have hidx : (ZMod.finEquiv (p * q) ((colOrder p q) (i, j)))
        = ((i.val + p * j.val : ℕ) : ZMod (p * q)) := by
      rw [finEquiv_eq_natCast]; rfl
    -- the swap-conjugating equiv sends `(i, j)` to the literal pair `(j mod q, i mod p)`.
    have hrhs : ec (i, j) = (ZMod.finEquiv q j, ZMod.finEquiv p i) := by
      rw [hec]; simp [Equiv.trans_apply, arrEquiv_apply, Equiv.prodComm_apply]
    rw [hrhs, Equiv.trans_apply, Equiv.trans_apply, arrEquiv_crtOrder_symm, hidx,
      Equiv.prodComm_apply, Equiv.prodCongrLeft_apply, Equiv.Perm.mul_apply,
      ZolotarevCRT.ringMulPerm_apply, Equiv.coe_addLeft]
    refine Prod.ext ?_ ?_
    · -- first coordinate (ZMod q): the `mod q` residue
      rw [Prod.fst_swap, ZolotarevFullOdd.chineseRemainder_snd, map_natCast, hβ', ha',
        ZMod.coe_unitOfCoprime]
      simp only [RingEquiv.symm_apply_apply]
      rw [finEquiv_eq_natCast]
      push_cast
      ring
    · -- second coordinate (ZMod p): the `mod p` residue
      rw [Prod.snd_swap, ZolotarevFullOdd.chineseRemainder_fst, map_natCast,
        finEquiv_eq_natCast]
      push_cast
      rw [ZMod.natCast_self]
      ring
  have hsign := Equiv.Perm.sign_eq_sign_of_equiv
    ((colOrder p q).trans (crtOrder hpq).symm)
    (Equiv.prodCongrLeft fun k : ZMod p => Equiv.addLeft (β' k) * ringMulPerm a')
    ec hconj
  have hA' : ((p : ℤ) : ZMod q) = (a' : ZMod q) := by
    rw [ha', ZMod.coe_unitOfCoprime]; push_cast; ring
  have key := sign_prodCongrLeft_affineLine (p := q) (q := p) hq2 hp a' β' (p : ℤ) hA'
  rw [hsign]; exact key

/-- **Quadratic reciprocity, à la Zolotarev (unconditional).**  For distinct odd
    primes `p, q`,

        `(q / p) · (p / q) = (-1) ^ ((p-1)/2 · (q-1)/2)`,

    proved entirely from the sign-of-permutation calculus: the parent program's
    Zolotarev/Frobenius lemma `sign(x ↦ a·x on ℤ/n) = J(a|n)` (per residue line),
    the inversion count of the grid transpose (`sign_gridTranspose_odd`), and the
    three-transition skeleton, with the concrete CRT order `crtOrder` discharging
    both transition-sign hypotheses (`sign_rowTransition`, `sign_colTransition`).
    No appeal to Mathlib's `legendreSym.quadratic_reciprocity`. -/
theorem zolotarev_quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hne : p ≠ q) :
    legendreSym q (p : ℤ) * legendreSym p (q : ℤ)
      = (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hq : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq2
  have hpq : p.Coprime q := (Nat.coprime_primes Fact.out Fact.out).mpr hne
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : NeZero q := ⟨(Fact.out : q.Prime).pos.ne'⟩
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩
  exact quadratic_reciprocity_of_transition_signs hp hq (crtOrder hpq)
    (sign_rowTransition hp2 hq hpq) (sign_colTransition hq2 hp hpq)

end ZolotarevQR

#check @ZolotarevQR.gridTranspose
#check @ZolotarevQR.gridTranspose_apply
#check @ZolotarevQR.sign_gridTranspose
#check @ZolotarevQR.neg_one_pow_choose_two_mul_odd
#check @ZolotarevQR.sign_gridTranspose_odd
#check @ZolotarevQR.gridTranspose_eq
#check @ZolotarevQR.sign_transRC
#check @ZolotarevQR.quadratic_reciprocity_of_transition_signs
#check @ZolotarevQR.sign_addLeft_odd
#check @ZolotarevQR.sign_addLeft_mul
#check @ZolotarevQR.sign_affineLine_eq_legendreSym
#check @ZolotarevQR.sign_prodCongrLeft_affineLine
#check @ZolotarevQR.crtOrder
#check @ZolotarevQR.sign_rowTransition
#check @ZolotarevQR.sign_colTransition
#check @ZolotarevQR.zolotarev_quadratic_reciprocity
