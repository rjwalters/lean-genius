/-
  Toward a self-contained Zolotarev proof of Quadratic Reciprocity
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02)

  Open Question (follow-up #1 flagged by the parent capstone
  oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01, "Zolotarev–Frobenius for every odd
  modulus"):

    "Specialize the general-odd Frobenius identity to recover the quadratic
     reciprocity law (a/p)(p/a) = (-1)^… directly via the sign of a suitable
     shuffle permutation, as in Zolotarev's 1872 derivation."

  ## Status of THIS file (honest WIP infrastructure — NOT a finished proof)

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

  This file pins that ingredient down precisely as `sign_gridTranspose`
  (currently a `sorry`, classified HARD-but-known — see the strategy note on it)
  and proves the structural lemma `gridTranspose_apply` confirming the object is
  genuinely the row-major ↔ column-major reindexing.  Once `sign_gridTranspose`
  is discharged, Quadratic Reciprocity follows by the assembly sketched below.

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
  * `sign_gridTranspose` — STATED, proof is `sorry`.  This is the single
    remaining ingredient; it is a *known* result (HARD, not OPEN), a good target
    for proof search (Aristotle) or an inductive `sign_prodCongr*` / `finRotate`
    argument.  Do NOT mark the gallery entry `verified` while this `sorry`
    stands.
  * `neg_one_pow_choose_two_mul_odd` — proved (0 sorry): the parity bridge
    `(-1)^(C(m,2)·C(n,2)) = (-1)^(((m-1)/2)·((n-1)/2))` for odd `m, n`, i.e. the
    exponent simplification flagged in the plan above.  This is the elementary
    number-theory step that turns Zolotarev's shuffle factor into the textbook
    reciprocity factor; it does NOT depend on `sign_gridTranspose`.
  * `sign_gridTranspose_odd` — the classical-form corollary
    `sign (gridTranspose m n) = (-1)^(((m-1)/2)·((n-1)/2))` for odd `m, n`,
    obtained by feeding the parity bridge into `sign_gridTranspose` (so it still
    rests on that single `sorry`).
  * The full QR assembly (`α = β ∘ γ`, identifying `α, β` with `ringMulPerm`
    through the CRT isomorphism) is documented above but not yet formalized.

  References:
  - Zolotarev (1872); Frobenius (1914); Lerch (1896).
  - Cartier; Baker, "Quadratic reciprocity and Zolotarev's Lemma" (2013).
-/
import Mathlib

set_option maxHeartbeats 800000

namespace ZolotarevQR

open Equiv Equiv.Perm

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

    STATUS: `sorry`.  This is a KNOWN result (HARD, not OPEN).

    CROSS-REFERENCE / NON-DUPLICATION NOTE.  The *identical* obligation already
    stands, isolated and build-verified-in-context, in the sibling "algorithm"
    lineage as `QuadraticReciprocityAlgorithmOQ03M2.sign_gridTranspose_eq_choose`
    (merged #25053, currently unregistered).  Multiple prior sessions there
    established that NO Mathlib lemma gives `sign = (-1)^(inversion count)` for a
    general (non-cycle, non-block-diagonal) permutation — `sign_prodCongr*` /
    `sign_sumCongr` do NOT apply because the transpose is a coordinate swap — so
    the only route is the explicit `Finset.card_bij`

        inversions of `gridTranspose m n`  ↔  {i < i' : Fin m} × {j > j' : Fin n}

    unfolded from `signAux = ∏_{finPairsLT}`, of cardinality `C(m,2)·C(n,2)`.
    This is ~100 intricate LOC; it is the single self-contained Aristotle target
    the moment that backend stops returning "Resource not found".  The numerical
    inversion bijection is certified in
    `research/problems/quadratic-reciprocity-algorithm-oq-03/verify_grid_inversions.py`
    and `verify_inversion_bijection.py`.

    Suggested routes (both attempted/assessed in the sibling thread):
      * induction on `m`, decomposing the insertion of a row as a block of
        `finRotate`-type cycles and using `Equiv.Perm.sign_prodCongrLeft`,
        `sign_prodCongrRight`, `Equiv.Perm.sign_finRotate`; or
      * a direct inversion count against the `signAux`/`finPairsLT` model
        (the cleaner of the two — see the certified Python bijection above). -/
theorem sign_gridTranspose (m n : ℕ) :
    Equiv.Perm.sign (gridTranspose m n)
      = (-1 : ℤˣ) ^ (Nat.choose m 2 * Nat.choose n 2) := by
  sorry

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
    quadratic reciprocity law.  This still rests on the single open ingredient
    `sign_gridTranspose` (a `sorry`); it is recorded here to show how that one
    lemma feeds the final QR assembly. -/
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
