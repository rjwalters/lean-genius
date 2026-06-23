# wilsons-theorem-oq-02-ext-oq-02 — Gauss-Wilson for rings of integers

## Problem

Does the Gauss-Wilson theorem extend from `(ℤ/n)ˣ` to the unit groups of
quotients `O_K / 𝔞`, where `O_K` is the ring of integers of a number field `K`
and `𝔞` is a nonzero ideal?

Classical Gauss-Wilson: `∏_{u ∈ (ℤ/n)ˣ} u = -1` iff `n ∈ {1, 2, 4, pᵏ, 2pᵏ}`,
and `= 1` otherwise.

## Answer: YES (immediate corollary of the abelian-group form)

The key realization is that **nothing in the proof is specific to number
fields, or even to rings of integers.** For any nonzero ideal `𝔞`, the quotient
`R = O_K / 𝔞` is a *finite commutative ring*, so `Rˣ` is a finite abelian
group. The general two-involution theorem

  `WilsonsTheoremOQ02ExtOQ01.prod_eq_one_or_unique_involution`
  (sibling problem `wilsons-theorem-oq-02-ext-oq-01`, PR #24250)

states that for **any** `[CommGroup G] [Fintype G] [DecidableEq G]`,
`∏ x : G, x` equals the unique element of order two if one exists, and `1`
otherwise. Specialising `G = Rˣ` gives Gauss-Wilson for every finite
commutative ring, hence for `O_K / 𝔞`.

So this problem reduces, in one line, to the previously proved general theorem.
The mathematical content of this session is (a) recognizing the reduction and
(b) the number-theoretic refinement below.

## Number-theoretic refinement (analogue of n ∈ {1,2,4,pᵏ,2pᵏ})

By CRT on the prime factorization `𝔞 = ∏ 𝔭ᵢ^{eᵢ}`,
`(O_K/𝔞)ˣ ≅ ∏ (O_K/𝔭ᵢ^{eᵢ})ˣ`. The number of order-≤2 elements is the product
of the local counts, so:

`∏ u = -1`  ⟺  `-1` is the **unique** involution of `(O_K/𝔞)ˣ`
            ⟺  exactly one local factor `(O_K/𝔭^e)ˣ` contributes an involution,
               and that contribution is `-1`.

Local structure (mirrors `(ℤ/pᵏ)ˣ` with `N(𝔭) = p^f` in place of `p`):
`(O_K/𝔭^e)ˣ` has order `N(𝔭)^{e-1}(N(𝔭) - 1)`; its cyclic residue-field part
`𝔽_{N(𝔭)}ˣ` contributes one involution iff `N(𝔭)` is odd (i.e. `𝔭` lies over an
odd prime), and its principal-unit `p`-part contributes involutions only when
`p = 2`.

## New phenomenon (not present for ℤ/n)

For `ℤ/n` the product of units is always `±1`. Over `O_K` this can fail when
`-1 = 1` in `R` (residue characteristic 2): in `R = ℤ[i]/(2)` the unit group is
`{1, i}` and `∏ u = i`, an element of order two that is **neither `1` nor
`-1`**. The abstract characterization (`= unique involution, else 1`) still
holds verbatim; only the `-1` packaging degenerates.

## Verification (exact, build-free)

`verification/wilsons_oq02_ext_oq02_number_rings.py` enumerates `O_K = ℤ[α]`
(`α² = Aα + B`) quotients `O_K/(β)` via Hermite-normal-form lattice reduction,
brute-forces the unit group, and compares `∏ u` against the abstract
prediction. Exact integer arithmetic throughout.

- Rings: `ℤ[i]`, `ℤ[ω]`, `ℤ[√-2]`, `ℤ[√2]`, `ℤ[(1+√5)/2]` (real + imaginary).
- **94 quotients tested, 94/94 match the prediction, 0 counterexamples.**
- 70 cases `∏ u = -1`; 21 cases `∏ u = +1`; remainder are char-2 degeneracies.
- Hand-checked anchors: `ℤ[i]/(1+2i)` (≅ 𝔽₅, `∏ = -1`) and `ℤ[i]/(2)`
  (`∏ = i`).

## Lean (build-pending under dual-backend blackout)

`proofs/Proofs/WilsonsTheoremOQ02ExtOQ02.lean` (unregistered, like the sibling
OQ01 file):

- `prod_units_eq_one_or_unique_involution` — one-line instantiation of the
  general theorem at `G = Rˣ` (the headline corollary; high confidence).
- `prod_units_coe_eq_neg_one` — classical `-1` packaging when `-1` is the unique
  involution; uses `map_prod (Units.coeHom R)` for the coercion of the product.

**Dependency:** imports `Proofs.WilsonsTheoremOQ02ExtOQ01`, which currently lives
only on PR #24250 (still open). The file is left unregistered in
`proofs/Proofs.lean`, so it cannot break `main`'s build regardless of merge
order; it compiles once #24250 lands and the backend is available.

## Mathlib gaps

- No general finite-abelian-group / finite-commutative-ring Gauss-Wilson exists
  upstream (only `FiniteField.prod_univ_units_id_eq_neg_one` for fields). The
  general theorem was supplied by sibling OQ01.

## Status

ORIENT/ACT — reduction identified and proved (modulo the open sibling PR),
classical refinement characterized, new char-2 phenomenon documented, 94-case
exact certificate passing. No open mathematical gap remains for the existence
question; the only follow-up is the explicit `-1`-vs-`+1` ideal classification.

## Next steps

- After #24250 merges + backend returns: register both Wilson OQ01/OQ02 files in
  `proofs/Proofs.lean` and build.
- Optional: formalize the CRT-based `-1`/`+1` classification of ideals as a
  decidable predicate on `O_K/𝔞`.

## Session log

### 2026-06-15 (Session 1) — FRESH, ORIENT/ACT
- Recognized this is a direct corollary of sibling OQ01's general abelian-group
  theorem (PR #24250); R = O_K/𝔞 is a finite commutative ring.
- Wrote `WilsonsTheoremOQ02ExtOQ02.lean` (abstract corollary + `-1` packaging).
- Wrote and ran exact-integer certificate over 5 rings of integers, 94 quotients
  (0 mismatches); surfaced the `ℤ[i]/(2) ⟹ ∏ = i` char-2 phenomenon.
- Aristotle backend down ("Resource not found"); Docker unavailable — file
  left build-pending/unregistered.
