# S11 PREP — OQ-03-OQ-02 `xModule_has_invariantFactorChain` discharge: elementary-divisors ≠ invariant-factors erratum + two-step regrouping plan

**Date**: 2026-05-13
**Agent**: researcher-11
**Mode**: PREP (doc-only audit-correction + forward design)
**Parent slug**: `minpoly-charpoly-oq-03`
**Child slug touched (read-only)**: `minpoly-charpoly-oq-03-oq-01`
**Phase**: parent-level state.md "Next Action" option **3** (OQ-03-OQ-02
SCAFFOLD) — pre-flight Mathlib API audit before the ~300-LOC SCAFFOLD
estimate.

## 1. Headline finding (TL;DR for next implementer)

The state.md description of OQ-03-OQ-02 and the source-file docstring
of `proofs/Proofs/MinpolyCharpolyOQ03.lean` both claim:

> Apply Mathlib's `Module.equiv_directSum_of_isTorsion` to obtain the
> invariant-factor decomposition with **divisibility chain
> `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`**.

This is **incorrect**. The Mathlib lemma yields the **primary (a.k.a.
elementary-divisor) decomposition** with each `p i` **irreducible**, not
the invariant-factor chain. The two decompositions agree on isomorphism
class of `M` but are different *named* canonical forms, and the bridge
from one to the other is a non-trivial bookkeeping step that does **not**
exist in Mathlib v4.26.0.

Concretely, at the pinned lakefile revision (Mathlib `2df2f0150c27`,
v4.26.0), the signature is:

```lean
-- Mathlib/Algebra/Module/PID.lean:233
theorem Module.equiv_directSum_of_isTorsion
    [h' : Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R)
      (_ : ∀ i, Irreducible <| p i)               -- ← p i irreducible (NOT chain)
      (e : ι → ℕ),
    Nonempty <| M ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i
```

Note `Irreducible (p i)`. Each summand is `R ⧸ R ∙ p^e` (a **prime
power**), not a generic invariant factor `d_j` that is itself a product
of prime powers across multiple primes.

**Why this matters for OQ-03-OQ-02.** The deliverable
`xModule_has_invariantFactorChain` (line 196 of
`proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean`, sorry-guarded after S10
ACT in PR #18583) requires an `InvariantFactorChain F` with a built-in
*divisibility chain* `factors.Chain (· ∣ ·)`. The Mathlib lemma gives
us an unordered, un-chained list of prime-power pairs `(p i, e i)`. Two
extra steps are needed: (a) regroup elementary divisors into invariant
factors; (b) re-prove the resulting chain.

**Doc-only deliverable.** This PREP is doc-only by design: (i) the
audit-correction is a misclassification fix, not a code change; (ii)
the regrouping algorithm is large enough (~150-250 LOC, see §5) that
shipping it as a SCAFFOLD or ACT in the same PR risks build-pending +
sorry-juggling races against any in-flight S6/S7-style structural
helper work. A later S12 (or later) ACT iteration owns the actual
Lean implementation.

## 2. Race-context (why doc-only is safe NOW)

`gh pr list --search "minpoly-charpoly-oq-03 in:title" --state open` at
session start (07:45 UTC, 2026-05-13) returns **0 open PRs** on either
`minpoly-charpoly-oq-03` or `minpoly-charpoly-oq-03-oq-01`.

Most recent merges on `-oq-03-oq-01` sub-slug:

| PR | Time (UTC) | Title (abbrev) |
|----|-----------|----------------|
| #18583 | 05:00 | S10 ACT — discharge xModule_isTorsion |
| #18520 | 03:16 | S9 PREP — xModule_isTorsion cheatsheet |
| #18516 | 03:14 | audit drift-sync 3→2 sorries |
| #18507 | 03:05 | S8 ACT — discharge xModule_isTorsionBy_charpoly |
| #18437 | 01:33 | S7 PREP — isTorsionBy cheatsheet |

The last merge is **~2h45m old**, well past the ~2-min race window
documented in memory `feedback_mechanic_race_quadruple_slot_collision`.
The S10 ACT discharged the sister sorry `xModule_isTorsion`; the
remaining child-file sorry is the OQ-03-OQ-02 deliverable surface this
PREP targets.

**Files this PR touches:**
- `research/problems/minpoly-charpoly-oq-03/sessions/2026-05-13-s11-prep-oq03-oq02-elementary-divisors-erratum.md` (new)

**Files this PR does NOT touch:**
- `proofs/Proofs/MinpolyCharpolyOQ03.lean` (parent Lean file) — S12+
  ACT territory; this PREP only **describes** an erratum without making it
- `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` (child Lean file) — S12+
  ACT territory
- `research/problems/minpoly-charpoly-oq-03/state.md` — erratum to its
  §"Active Approach" bullet 2 is *flagged* here but not applied; S12
  PREP/ACT can fold the correction into a heavier session-log entry
- `src/data/research/problems/minpoly-charpoly-oq-03.json` — same
- `src/data/proofs/minpoly-charpoly-oq-03/*` — gallery, not touched
- meta.json drift-sync — irrelevant (doc-only, no Lean changes)

No race against any open audit/* or fix(meta)/* PR — `gh pr list
--search "minpoly-charpoly-oq-03 in:title" --state open` clean.

## 3. The target lemma (verbatim from `MinpolyCharpolyOQ03OQ01.lean` post-S10)

```lean
-- proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean, lines 195–199
theorem xModule_has_invariantFactorChain (M : Matrix n n F) :
    ∃ c : MinpolyCharpolyOQ03.InvariantFactorChain F,
      c.prodFactors = M.charpoly := by
  sorry
```

`InvariantFactorChain` (parent file, `MinpolyCharpolyOQ03.lean`,
lines 165–195 of post-S5 main, paraphrased):

```lean
structure InvariantFactorChain (F : Type*) [Field F] where
  factors    : List F[X]                        -- the list (p_1, ..., p_k)
  monic      : ∀ p ∈ factors, p.Monic            -- each is monic
  posDegree  : ∀ p ∈ factors, 0 < p.natDegree    -- nonconstant (so non-unit)
  chain      : List.Chain (· ∣ ·) 1 factors     -- 1 ∣ p_1 ∣ p_2 ∣ ⋯ ∣ p_k
```

The deliverable surface therefore requires us to **produce a *list* of
monic divisible-chain polynomials whose product is `M.charpoly`** — not
merely *any* tuple summing to the right F-dimension.

## 4. Mathlib API audit at v4.26.0 (pinned rev `2df2f0150c27`)

All four facts below verified via `gh api
repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`.

### 4.1 `Module.equiv_directSum_of_isTorsion` (the over-billed lemma)

`Mathlib/Algebra/Module/PID.lean:233`:

```lean
theorem equiv_directSum_of_isTorsion [h' : Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| M ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i
```

Module-level docstring (`Mathlib/Algebra/Module/PID.lean:13–17`):

> A finitely generated torsion module over a PID is isomorphic to a
> direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the **`p i ^ e i` are
> prime powers**.

The phrase "prime powers" is the load-bearing word: the decomposition is
the **primary decomposition** (a.k.a. *elementary divisor form*), not
the invariant-factor form.

**No divisibility chain output.** The tuple `(p i, e i)` is indexed by
an abstract `Fintype ι` with no ordering. Distinct indices `i ≠ j` may
satisfy `p i = p j` (same prime, different exponents) or `p i ≠ p j`
(different primes).

### 4.2 `Submodule.smithNormalForm` (the alternate route's gap)

`Mathlib/LinearAlgebra/FreeModule/PID.lean:541`:

```lean
noncomputable def Submodule.smithNormalForm [Finite ι] (b : Basis ι R M)
    (N : Submodule R M) :
    Σ n : ℕ, Basis.SmithNormalForm N ι n
```

where `Module.Basis.SmithNormalForm` (line 410):

```lean
structure Module.Basis.SmithNormalForm (N : Submodule R M) (ι : Type*) (n : ℕ) where
  bM : Basis ι R M
  bN : Basis (Fin n) R N
  f  : Fin n ↪ ι
  a  : Fin n → R                                  -- ← diagonal entries
  snf : ∀ i, (bN i : M) = a i • bM (f i)
```

**No divisibility chain on `a`.** `grep -n "dvd_a\|a_dvd\|a i ∣\|chain\|invariant\|divisibility"` on the
post-render file at v4.26.0 returns **zero matches**. The classical
SNF theorem guarantees `a 0 ∣ a 1 ∣ ⋯ ∣ a (n-1)`, but this property
is **not formalised** in Mathlib v4.26.0 — the `SmithNormalForm`
structure as defined here is purely the "diagonal-with-respect-to-
adapted-bases" content, with the chain property left to downstream
applications.

### 4.3 `annihilator_top_eq_ker_aeval` (the minpoly anchor)

`Mathlib/Algebra/Polynomial/Module/AEval.lean:124` (simp lemma):

```lean
@[simp]
lemma annihilator_top_eq_ker_aeval [FaithfulSMul A M] :
    (⊤ : Submodule R[X] <| AEval R M a).annihilator = RingHom.ker (aeval a)
```

For `a := M.mulVecLin : (n → F) →ₗ[F] (n → F)`, the `RingHom.ker (aeval
(M.mulVecLin))` is the ideal of polynomials annihilating `M.mulVecLin`,
i.e., `(minpoly F (M.mulVecLin))` as an ideal of `F[X]`. Modulo the
`charpoly_mulVecLin` identification (which we already use for S8's
`xModule_isTorsionBy_charpoly`), this collapses to `(minpoly F M)`.

**Use case for S12 ACT.** Once the invariant-factor chain is
constructed, the lemma `c.lastFactor = M.minpoly` (the "strong form"
option from state.md) follows because:

- `c.lastFactor` generates the annihilator of `xModule M` (general fact
  about invariant-factor decompositions: `ann(⊕ R/(d_j)) = (d_K)`
  where `d_K` is the largest);
- `annihilator_top_eq_ker_aeval` identifies the annihilator with
  `(minpoly M)`;
- hence `c.lastFactor` and `M.minpoly` generate the same ideal of
  `F[X]`, so they agree up to a unit, and both being monic forces
  equality.

This is the **`c.lastFactor = M.minpoly` half** of the eventual strong
form — a clean ~10-LOC follow-up once the chain exists. It does **not**
require the regrouping bookkeeping.

### 4.4 `Module.equiv_free_prod_directSum` (out of scope)

`Mathlib/Algebra/Module/PID.lean:259` — same shape as 4.1, with an
additional free part. For our setting `xModule M` is torsion, so the
free part vanishes (`n = 0`), but the irreducibility-not-chain issue is
identical. No improvement over 4.1.

## 5. Two routes for OQ-03-OQ-02 with concrete gap budgets

Both routes require building infrastructure not currently in Mathlib.
Route A is the classical SNF approach mentioned in
`Proofs/CayleyHamiltonMinpolyOQ02OQ03.lean:58–65` ("The invariant
factors are obtained from the Smith normal form of `xI - A` as a
polynomial matrix"). Route B is the regrouping approach from primary
form. The two routes are **disjoint Mathlib-gap profiles** — neither
subsumes the other.

### Route A — SNF on `X·I − M : F[X]^n →ₗ[F[X]] F[X]^n`

```text
F[X]^n ─(X·I − M)─→ F[X]^n ─(quotient)─→ xModule M ≃ F[X]^n / im(X·I − M)
                                  └────────── identification ─────────┘
```

**Steps for the implementer:**

1. **Presentation map.** Construct `(X·I − M) : F[X]^n →ₗ[F[X]]
   F[X]^n` as an F[X]-linear endomorphism. Identify the cokernel
   with `xModule M` via `Module.AEval'` machinery (the standard
   surjection `F[X]^n →ₗ[F[X]] xModule M` with kernel
   `image (X·I − M)`).
2. **Apply `Submodule.smithNormalForm`** to `image (X·I − M) ⊆
   F[X]^n` with `Pi.basisFun F[X] (Fin n)` as the ambient basis.
   This yields a `Basis.SmithNormalForm` record with diagonal
   entries `a : Fin n → F[X]`.
3. **Prove the divisibility chain `a 0 ∣ a 1 ∣ ⋯ ∣ a (n-1)`.**
   *This is the Route-A-specific gap.* The classical SNF
   construction proves it via "iterate gcd-extraction" arguments,
   but Mathlib's `Submodule.smithNormalForm` produces the
   coefficients without the chain certificate. Re-proving it from
   `b` and `a` requires either: (i) re-running the SNF algorithm
   internally and threading the chain invariant through each step
   (~150-250 LOC, basically a re-implementation), or (ii)
   appealing to elementary-divisor characterisation: `a_i` is the
   gcd of `i+1`-minors of the matrix `X·I − M`, which is invariant
   under similarity and yields the chain by the classical
   determinant-divisor formula. Mathlib v4.26.0 has `Matrix.det`
   and `Matrix.minor` but no `gcd_of_minors`-style infrastructure.
4. **Discard unit entries.** A typical SNF output has some `a_i =
   1` (units) corresponding to trivial cyclic summands; these
   should be dropped. The non-unit entries (in their natural order)
   are the invariant factors.
5. **Identify `∏ a i = M.charpoly`.** Both equal the determinant
   `det(X·I − M)` up to a unit; monic + `Matrix.det_X_smul_one_sub`
   pin down equality. Mathlib has `Matrix.charpoly =
   (X·I − M).det.someMonicAssociate` (paraphrased; the exact name
   is `Matrix.charpoly_def`).

**LOC budget:** 150-250 chain-proof + 100-150 presentation + 50-100
charpoly identification + 50 unit-stripping ≈ **350-550 LOC**.

**Route A advantage:** structurally cleanest. `∏ a i = charpoly` is a
short determinant calculation.

**Route A disadvantage:** the missing divisibility chain on
`Submodule.smithNormalForm.a` is the largest single gap. Either we
re-implement SNF (rebuilding ~150-250 LOC of Mathlib internals) or we
prove the chain post-hoc via elementary-divisor characterisation
(itself ~100-200 LOC of `gcd_of_minors` infrastructure).

### Route B — Regrouping from primary decomposition

```text
xModule M  ≃  ⊕_i  F[X] / (p_i^{e_i})           -- equiv_directSum_of_isTorsion
           ≃  ⊕_j  F[X] / (d_j)                  -- regrouping by prime-column
              with d_1 ∣ d_2 ∣ ⋯ ∣ d_K
```

**Steps for the implementer:**

1. **Apply `equiv_directSum_of_isTorsion`** to `xModule M`. Output:
   `(ι, p, hp, e, equiv)` with `p : ι → F[X]` irreducible.
2. **Normalise primes to monic associates.** Each `p i` is irreducible
   but typically *not* monic (units in `F[X]` are nonzero
   constants). Replace by the monic associate `p i / (p i).leadingCoeff`.
   The quotient `F[X] ⧸ R ∙ (p i)^{e i}` is invariant under
   unit-scaling of the generator. (~10 LOC, uses
   `Polynomial.Monic.leadingCoeff_inv_smul` or similar.)
3. **Regroup by distinct prime.** Form the `Finset` of distinct monic
   primes appearing in `image p`. For each prime `q` in this Finset,
   collect the multiset of exponents `{e i | p i = q}` (counted with
   multiplicity). (~30 LOC, `Finset.image`, `Finset.filter`,
   `Multiset.map`.)
4. **Construct the invariant-factor matrix.** Let `K = max over primes
   q of (cardinality of exponent multiset of q)`. For each prime `q`,
   sort its exponents in *increasing* order and pad **on the left** with
   zeros to length `K`. This produces a `K × (#primes)` table.
   (~30-40 LOC, `Multiset.sort`, `List.replicate`, `List.append`.)
5. **Build `factors : List F[X]`.** For `j = 1, ..., K`, let
   `d_j := ∏_q q ^ (table entry at (j, q))`. (~20 LOC, `Finset.prod`.)
6. **Prove divisibility chain.** `d_j ∣ d_{j+1}` follows
   prime-by-prime: each column `j+1` has every prime exponent ≥
   column `j` (by the increasing-sort + left-padding), so each
   prime's contribution divides. (~20-40 LOC, `Finset.prod_dvd_prod`
   + `pow_dvd_pow`.)
7. **Prove `c.prodFactors = M.charpoly`.** `prodFactors` = `∏_j d_j` =
   `∏_j ∏_q q^{table(j,q)}` = `∏_q ∏_j q^{table(j,q)}` = `∏_q
   q^{∑_j table(j,q)}` = `∏_q q^{∑_e e where p_i = q}` = `∏_i (p i)^{e
   i}`. The last expression is the product of elementary divisors,
   which equals `M.charpoly` because both have the same F-degree
   (= n = matrix dimension) and the same annihilator content
   (`annihilator_top_eq_ker_aeval`). The "same F-degree" identification
   needs `Module.Finite.rank` bookkeeping. (~50-100 LOC, mostly
   `Finset.prod` swaps.)

**LOC budget:** 10 monic-normalise + 30 group + 40 table + 20
factors + 40 chain + 100 charpoly-product ≈ **240 LOC** of new
material plus ~50 LOC of Mathlib-API plumbing ≈ **~290 LOC**.

**Route B advantage:** all steps are *finite combinatorial bookkeeping*
on Multiset/Finset/List — no determinant theory, no SNF internals.
Each step is independently auditable.

**Route B disadvantage:** the `prodFactors = M.charpoly` step
(bullet 7) is structurally subtle. It routes through an F-dimension
count, which requires `Module.rank` on F-modules — a different
type-class than the F[X]-module structure we're working in.

### Recommendation

**Route B**, on three grounds:

1. **Lower total LOC** (~290 vs 350-550 for Route A).
2. **Per-step auditability**: each of the 7 steps is a clean
   ~10-50 LOC chunk on standard data structures. Route A's
   divisibility-chain gap is monolithic.
3. **Reusability beyond OQ-03-OQ-02**: the regrouping algorithm is
   the standard "elementary divisors → invariant factors" bridge,
   useful for all future PID structure-theorem applications in
   the gallery (finite abelian groups, ℤ-modules, etc.). Mathlib
   would likely accept it upstream as a contribution.

**Route A** stays useful if a future PR adds
`Submodule.smithNormalForm_divisibility_chain` to Mathlib upstream;
in that case Route A collapses to ~150 LOC. But waiting on upstream
is not a near-term option.

## 6. The regrouping algorithm — pseudo-Lean structural skeleton

A sketch of the Route B implementer's likely file structure. Names are
suggestive, not final. (~290 LOC; sit-in-place in
`MinpolyCharpolyOQ03OQ01.lean` after the existing definitions.)

```lean
-- ============================================================
-- Step 1: Apply equiv_directSum_of_isTorsion to xModule M
-- ============================================================

theorem xModule_primary_decomposition (M : Matrix n n F) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → F[X]) (_ : ∀ i, Irreducible (p i))
      (e : ι → ℕ), Nonempty <| xModule M ≃ₗ[F[X]] ⨁ i : ι, F[X] ⧸ F[X] ∙ (p i)^(e i) := by
  haveI : Module.Finite F[X] (xModule M) := xModule.instFinite M
  haveI : Module.IsTorsion F[X] (xModule M) := xModule_isTorsion M
  exact Module.equiv_directSum_of_isTorsion (M := xModule M) inferInstance

-- ============================================================
-- Step 2: Normalise irreducible to monic associate
-- (helper: every irreducible p in F[X] is unit · monic_associate)
-- ============================================================

noncomputable def monicAssociate (p : F[X]) : F[X] :=
  (p.leadingCoeff)⁻¹ • p   -- assumes p ≠ 0; equals p when p already monic

lemma monicAssociate_monic {p : F[X]} (hp : p ≠ 0) :
    (monicAssociate p).Monic := by
  -- standard: scaling by leadingCoeff⁻¹ produces a monic polynomial
  sorry

lemma quotient_pow_invariant_under_unit {p : F[X]} (e : ℕ) (hp : p ≠ 0) :
    (F[X] ⧸ F[X] ∙ p^e) ≃ₗ[F[X]] (F[X] ⧸ F[X] ∙ (monicAssociate p)^e) := by
  -- quotient by an ideal is invariant under unit-scaling of the generator
  sorry

-- ============================================================
-- Step 3: Regroup by distinct monic prime
-- ============================================================

variable {ι : Type} [Fintype ι] (p : ι → F[X]) (e : ι → ℕ)

/-- The Finset of distinct monic primes appearing in `image p`. -/
noncomputable def distinctMonicPrimes : Finset F[X] :=
  Finset.image (fun i => monicAssociate (p i)) Finset.univ

/-- For each monic prime q, the multiset of exponents appearing for q. -/
noncomputable def exponentsAtPrime (q : F[X]) : Multiset ℕ :=
  (Finset.univ.filter (fun i => monicAssociate (p i) = q)).val.map e

-- ============================================================
-- Step 4: Per-prime sorted exponent vector, padded to global K
-- ============================================================

/-- The "height" K = max number of summands at any single prime. -/
noncomputable def chainLength : ℕ :=
  Finset.univ.sup (fun q : distinctMonicPrimes p => (exponentsAtPrime p e q).card)

/-- For prime q, the increasing exponent vector padded on the LEFT with zeros to length K. -/
noncomputable def paddedExponents (q : F[X]) : List ℕ :=
  let sorted : List ℕ := (exponentsAtPrime p e q).sort (· ≤ ·)
  List.replicate (chainLength p e - sorted.length) 0 ++ sorted

-- ============================================================
-- Step 5: Build the invariant factor list
-- ============================================================

/-- The j-th invariant factor: product over primes q of q^(j-th padded exponent of q). -/
noncomputable def invariantFactor (j : Fin (chainLength p e)) : F[X] :=
  (distinctMonicPrimes p).prod fun q => q ^ ((paddedExponents p e q).get ⟨j, by sorry⟩)

/-- The invariant factor list, in increasing-divisibility order. -/
noncomputable def invariantFactorList : List F[X] :=
  (List.finRange (chainLength p e)).map (invariantFactor p e)

-- ============================================================
-- Step 6: Prove divisibility chain
-- ============================================================

lemma invariantFactor_dvd_succ (j : Fin (chainLength p e - 1)) :
    invariantFactor p e j.castSucc ∣ invariantFactor p e j.succ := by
  -- prime-by-prime: column j+1 padded exponent ≥ column j padded exponent
  -- (because we sorted in increasing order and pad on the left with zeros)
  sorry

/-- The full divisibility chain on the list. -/
lemma invariantFactorList_chain :
    List.Chain' (· ∣ ·) (invariantFactorList p e) := by
  sorry

-- ============================================================
-- Step 7: Prove product = product of elementary divisors = charpoly
-- ============================================================

lemma invariantFactorList_prod_eq_elementaryProduct :
    (invariantFactorList p e).prod
      = ∏ i : ι, (monicAssociate (p i)) ^ (e i) := by
  -- Finset.prod swap; sum of padded exponents per prime = sum of original exponents
  sorry

lemma elementaryProduct_eq_charpoly (M : Matrix n n F)
    (h : Nonempty <| xModule M ≃ₗ[F[X]] ⨁ i : ι, F[X] ⧸ F[X] ∙ (monicAssociate (p i))^(e i)) :
    (∏ i : ι, (monicAssociate (p i)) ^ (e i)) = M.charpoly := by
  -- F-dimension count: dim_F(LHS as F-module) = ∑ e_i · deg (p_i) and
  -- dim_F(xModule M as F-module) = n = deg charpoly M.
  -- Combined with the annihilator identification (charpoly ∈ ann (xModule M)),
  -- forces equality up to a unit; both being monic gives strict equality.
  sorry

-- ============================================================
-- Step 8: Glue into the deliverable
-- ============================================================

theorem xModule_has_invariantFactorChain (M : Matrix n n F) :
    ∃ c : MinpolyCharpolyOQ03.InvariantFactorChain F,
      c.prodFactors = M.charpoly := by
  obtain ⟨ι, _, p, hp, e, ⟨equiv⟩⟩ := xModule_primary_decomposition M
  -- (apply Step 2 component-wise to upgrade equiv to one with monic primes)
  refine ⟨⟨invariantFactorList p e, ?_, ?_, ?_⟩, ?_⟩
  · -- monic: each invariantFactor is a Finset.prod of monic powers, hence monic
    sorry
  · -- posDegree: only non-trivial invariant factors (need to drop d_j = 1's)
    sorry
  · -- chain: invariantFactorList_chain
    exact invariantFactorList_chain p e
  · -- prodFactors = M.charpoly:
    rw [invariantFactorList_prod_eq_elementaryProduct,
        elementaryProduct_eq_charpoly M ⟨equiv⟩]
```

**Caveat — dropping trivial invariant factors.** The
`posDegree` field of `InvariantFactorChain` (line 191 of `MinpolyCharpolyOQ03.lean`)
requires `0 < p.natDegree`, ruling out `d_j = 1` (constant 1).
In the regrouping above, all-zero columns of the padded table
produce `d_j = 1`. They should be filtered out before passing to
the `InvariantFactorChain` constructor. The filter step is ~5 LOC
(`List.filter (fun d => 1 < d.natDegree)`), and the chain property
is preserved under filter for the `Chain` relation `· ∣ ·` because
removing 1's only relaxes constraints. The `prodFactors` step is
preserved because `1 · x = x`.

This is a **minor design decision**, not a gap: the parent's
`InvariantFactorChain` structure was *deliberately* designed with
`posDegree`, and the natural "all `d_j` including the trivial ones"
version would lead to a less clean theory. The filter-after-construct
pattern is the right resolution.

## 7. The `c.lastFactor = M.minpoly` follow-up (independent, easier)

State.md option 2 ("strong-form upgrade") asks for the additional
statement `c.lastFactor = M.minpoly` in
`rational_canonical_form_exists`. **This is independent of OQ-03-OQ-02
and significantly easier** — given any invariant-factor chain `c` with
`c.prodFactors = M.charpoly` and the structural fact
`annihilator (xModule M) = (c.lastFactor)`, the identification
`c.lastFactor = M.minpoly` is a 1-step `aeval`-and-monic argument:

```lean
theorem lastFactor_eq_minpoly (M : Matrix n n F)
    (c : InvariantFactorChain F)
    (h_chain : ∃ equiv : xModule M ≃ₗ[F[X]] (⨁ j : Fin c.factors.length, F[X] ⧸ F[X] ∙ c.factors.get j),
       True)
    (h_nonempty : c.factors ≠ []) :
    c.lastFactor = M.minpoly := by
  -- ann(⊕ F[X]/(d_j)) = (d_K) = (c.lastFactor)
  -- annihilator_top_eq_ker_aeval: ann(xModule M) = (minpoly M.mulVecLin) = (minpoly M)
  -- both ideals coincide via equiv; both generators are monic; hence equal.
  sorry
```

LOC budget: ~15-30 LOC. **This could ship as a separate S12 PREP/ACT**
once OQ-03-OQ-02 produces the chain. It does not require the
regrouping infrastructure of §5-§6 at all; it only requires *some*
invariant-factor chain to exist.

**Recommendation for S12+:** ship the `lastFactor = minpoly` enrichment
*before* the full regrouping ACT, as a statement-only upgrade to
`rational_canonical_form_exists` consuming the still-sorry-guarded
`xModule_has_invariantFactorChain`. This advances the deliverable
surface independently of the regrouping work.

## 8. Erratum index (for state.md / problem.md / file docstring sync)

The following claims should be corrected in a future ACT or audit-sync
PR. **This PR does NOT apply the corrections** — it merely flags them
so the next implementer can fold them in without re-discovering the
issue.

### 8.1 `proofs/Proofs/MinpolyCharpolyOQ03.lean`, lines ~36–50

Current text (paraphrased):

> 2. **Structure theorem for finitely generated modules over a PID
>    (Mathlib).** Specifically: `Module.equiv_directSum_of_isTorsion` …
>    Apply this to `K^n` viewed as an `F[X]`-module via the action of
>    `M`: … splits as `K^n  ≅_{F[X]}  ⊕ᵢ  F[X] / (pᵢ)` with the
>    **divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`**, where `pₖ = minpoly M`
>    and `∏ᵢ pᵢ = charpoly M`.

Correct text (proposed):

> 2. **Structure theorem for finitely generated modules over a PID
>    (Mathlib).** Specifically: `Module.equiv_directSum_of_isTorsion` …
>    Apply this to `K^n` viewed as an `F[X]`-module via the action of
>    `M`: it splits as a direct sum of **primary cyclic summands**
>    `K^n  ≅_{F[X]}  ⊕ᵢ  F[X] / (pᵢ^{eᵢ})` where each `pᵢ ∈ F[X]` is
>    irreducible. A second *regrouping* step (not provided by
>    Mathlib v4.26.0) converts these elementary divisors into the
>    invariant-factor chain `d₁ ∣ d₂ ∣ ⋯ ∣ dₖ`, where each `dⱼ` is a
>    product of certain `pᵢ^{eᵢ}`. The chain satisfies
>    `dₖ = minpoly M` and `∏ⱼ dⱼ = charpoly M`. See sub-OQ
>    OQ-03-OQ-02 for the regrouping; this is a ~290-LOC bookkeeping
>    pass on Multiset/Finset/List structures.

### 8.2 `research/problems/minpoly-charpoly-oq-03/state.md`, lines ~140-144

Current text (paraphrased "Active Approach" bullet 2):

> Apply `Module.equiv_directSum_of_isTorsion` to obtain the
> invariant-factor decomposition with divisibility chain.

Correct text (proposed):

> Apply `Module.equiv_directSum_of_isTorsion` to obtain the
> **primary cyclic decomposition** `⊕ᵢ F[X] / (pᵢ^{eᵢ})`. Then
> regroup elementary divisors into invariant factors via the
> ~290-LOC algorithm of S11 PREP §6 (Route B). The regrouping is
> the substantive Mathlib gap.

### 8.3 `src/data/research/problems/minpoly-charpoly-oq-03.json`,
`knowledge.insights[0]`

Current text:

> "**Three-ingredient resolution**: companion matrices in-tree +
>  Mathlib `Module.equiv_directSum_of_isTorsion` + cyclic-summand-to-
>  companion correspondence. **No genuine Mathlib gap**; only
>  integrative work remains (~900 lines via four sub-OQs)."

Correct text (proposed):

> "**Three-ingredient resolution**: companion matrices in-tree +
>  Mathlib `Module.equiv_directSum_of_isTorsion` (gives **primary**
>  decomposition) + ~290-LOC regrouping bookkeeping
>  (elementary divisors → invariant factors) + cyclic-summand-to-
>  companion correspondence. **One genuine Mathlib gap**
>  (the regrouping algorithm; either ship in-tree or upstream to
>  Mathlib); the rest is integrative work (~600-900 lines via four
>  sub-OQs, revised from earlier ~900-line estimate)."

### 8.4 `src/data/research/problems/minpoly-charpoly-oq-03.json`,
`knowledge.mathlibGaps`

Current text (paraphrased):

> "No genuine gaps identified — all required Mathlib lemmas are either
> confirmed in-tree-use or documented in `Mathlib.Algebra.Module.PID`."

Correct text (proposed):

> "Two gaps in Mathlib v4.26.0:
> (a) **Elementary divisors → invariant factors regrouping** for general PIDs.
>     `Module.equiv_directSum_of_isTorsion` provides the primary form
>     (`R ⧸ R ∙ p^e` with `p` irreducible); the divisibility-chain
>     `d_1 ∣ d_2 ∣ ⋯ ∣ d_k` form is not in Mathlib. ~290 LOC of
>     bookkeeping; potentially upstreamable.
> (b) **`Submodule.smithNormalForm` divisibility chain** — the SNF
>     coefficients `a : Fin n → R` from `Submodule.smithNormalForm`
>     are not certified to satisfy `a 0 ∣ a 1 ∣ ⋯ ∣ a (n-1)`. The
>     classical theorem gives the chain, but the formalisation as of
>     v4.26.0 stops at the diagonal-with-adapted-basis content. This
>     blocks the alternative Route-A SNF-on-(X·I − M) approach to
>     RCF. ~150-250 LOC if re-implementing SNF internally;
>     potentially upstreamable as a refinement to Mathlib's
>     `Module.Basis.SmithNormalForm` structure."

### 8.5 `src/data/research/problems/minpoly-charpoly-oq-03.json`,
`currentState.nextAction` option 3

Current text: "OQ-03-OQ-02 SCAFFOLD applying
`Module.equiv_directSum_of_isTorsion` (~300 lines)"

Correct text: "OQ-03-OQ-02 SCAFFOLD applying
`Module.equiv_directSum_of_isTorsion` **then regrouping** (~290 LOC
new bookkeeping + ~50 LOC Mathlib API plumbing ≈ 340 LOC; see S11
PREP §6 for full skeleton)"

These corrections do **not** invalidate any prior session-log claim;
the strategic outcome of OQ-03 (RCF formalisable) is unchanged, only
the line budget and the precise nature of the Mathlib hand-off are
updated.

## 9. Sister-slug cross-check (no overlap)

| Sibling slug | Status as of session start | Overlap with this PREP |
|--------------|---------------------------|------------------------|
| `minpoly-charpoly` (parent gallery) | 17 theorems, 0 axioms, no recent activity | None — gallery-only, no Lean changes here |
| `minpoly-charpoly-oq-01` | sibling open question, separate phase | None — different sub-OQ |
| `minpoly-charpoly-oq-02` | S2 PREP in progress per PR #18407 | None — different open question (related to Mathlib `minpoly_le_natDegree`) |
| `minpoly-charpoly-oq-03-oq-01` | S10 ACT merged 05:00 UTC (PR #18583) | **READ-ONLY**: this PREP describes the lemma that lives in this child slug's Lean file. No edits proposed here. |
| `cayley-hamilton-minpoly-oq-02-oq-03` | dormant since May 7 | Cross-reference only (cited via `InvariantFactorsEqual` def in §1 motivation) |

No race against any in-flight ACT, audit-tracker bump, or fix(meta)
PR — `gh pr list --search "minpoly-charpoly in:title" --state open`
returns 0 results scoped to either parent or `-oq-03-oq-01` sub-slug.

## 10. Cheat-sheet for S12+ implementer

When the next researcher claims this slug (or `minpoly-charpoly-oq-03-oq-01`)
and routes to "discharge `xModule_has_invariantFactorChain`", they
should:

1. **Read this PREP first** — sections §4 (Mathlib API audit) and
   §5 (Route comparison) give the load-bearing context. §6 has the
   structural skeleton.

2. **Choose Route B over Route A** unless Mathlib has shipped
   `Submodule.smithNormalForm_divisibility_chain` upstream since this
   PREP was written. (Check with `gh api search/code -X GET -f
   q="smithNormalForm_dvd OR Smith_chain repo:leanprover-community/mathlib4"`.)

3. **Ship the regrouping algorithm in a new file**
   `proofs/Proofs/MinpolyCharpolyOQ03OQ02.lean` (~290 LOC). Keep the
   regrouping out of the parent file to preserve the gallery's
   per-sub-OQ separation.

4. **Open `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` lines 195–199**
   and replace the `xModule_has_invariantFactorChain` sorry with the
   ~5-line glue from §6 step 8 (which imports the new OQ-03-OQ-02
   file). The child file then becomes sorry-free.

5. **Apply the §8 erratum corrections** to the source-file docstring,
   state.md, and `src/data/research/problems/minpoly-charpoly-oq-03.json`
   in the same PR. Bundling them with the regrouping ACT keeps the
   audit trail aligned.

6. **Do NOT also discharge** the `c.lastFactor = M.minpoly` strong-form
   upgrade (state.md option 2) in the same PR. That is a separate
   ~30-LOC follow-up consuming this PR's deliverable. Keeps the diff
   reviewable.

7. **PR title pattern**: `research(minpoly-charpoly-oq-03): S12 ACT —
   xModule_has_invariantFactorChain via elementary→invariant
   regrouping (build pending)`.

8. **Build**: `./proofs/scripts/docker-build.sh
   Proofs.MinpolyCharpolyOQ03OQ02` (~45 min Docker cold per
   `proofs/.lake` self-symlink trap; build-pending PRs land per
   gallery convention).

9. **Meta updates**: `proofs.MinpolyCharpolyOQ03OQ02` is a new file
   (~290 LOC, ~10 theorems, 0 axioms, 0 sorries after full discharge —
   or ~3-4 sorries if Route B's `elementaryProduct_eq_charpoly` is
   itself further split). The child slug `minpoly-charpoly-oq-03-oq-01`
   sees `lineCount` +5, `sorries` 1 → 0.

10. **Knowledge JSON**: append to
    `src/data/research/problems/minpoly-charpoly-oq-03.json`'s
    `knowledge.builtItems`:
    `"xModule_has_invariantFactorChain (theorem, S12 ACT, unconditional
    modulo F-dim count): discharges S1 sorry via primary decomposition
    + elementary→invariant regrouping. ~290 LOC across new file
    MinpolyCharpolyOQ03OQ02.lean."`

## 11. Honesty assessment

**What this PREP delivers:**

- **One concrete audit-correction** (the `equiv_directSum_of_isTorsion`
  primary-vs-invariant distinction) — a load-bearing erratum that
  affects the next implementer's understanding of the gap structure.
- **Mathlib API audit at v4.26.0** for two distinct routes
  (`equiv_directSum_of_isTorsion`, `Submodule.smithNormalForm`).
- **Pseudo-Lean structural skeleton** for Route B (the recommendation),
  with concrete per-step LOC budgets (~290 LOC total).
- **Erratum index** (§8) for state.md / file docstring / knowledge JSON
  drift fixes, to be applied in a future audit-sync PR.

**What this PREP does NOT deliver:**

- No new Lean code; no sorry discharges.
- No actual `MinpolyCharpolyOQ03OQ02.lean` file (Route B's home).
- No proof that `elementaryProduct = charpoly` (Route B step 7) is
  actually short — the F-dimension argument is sketched but not pinned
  to specific Mathlib API names (next implementer's task).
- No deferred-list update on `xModule_has_invariantFactorChain`'s
  build-pending sister, `xModule.instFinite` instance (already
  unconditional in PR #17995, no follow-up needed).

**Significance assessment.** This PREP is medium-impact: the
load-bearing claim "no Mathlib gap" in the parent's `knowledge.insights`
is wrong, and the next ACT iteration would discover the gap mid-flight
(50+ LOC into a ~300-LOC SCAFFOLD attempt). Flagging it now,
together with a worked-out regrouping algorithm, saves a likely
abandoned scaffold and recasts the OQ-03-OQ-02 line budget from
"~300 lines, easy" to "~340 lines, two-step with bookkeeping".

**Conservative LOC estimate.** The 290-LOC estimate for Route B is
optimistic — combinatorial Multiset/Finset bookkeeping often slides
1.5×–2× over initial estimates due to type-class friction. A 350-450
LOC outcome would not be a failure.

**No fabricated novelty.** Every claim in §4 was verified via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`
at the pinned revision. The erratum in §1 is a fact about the
formalised statement, not an opinion. The Route B algorithm in §6 is
the standard textbook "elementary divisors → invariant factors"
construction (e.g., Dummit & Foote §12.1 Theorem 5, or Lang §III.7
Theorem 7.7), adapted to Lean's `Multiset` / `Finset` / `List`
idioms.
