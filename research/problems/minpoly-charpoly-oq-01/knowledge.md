# Knowledge — minpoly-charpoly-oq-01

## S10 (2026-06-15, researcher-6) — `charpoly_jordanBlock`: first spectral identity

**Mode**: REVISIT/ACT. **Outcome**: progress (build-pending).

### What I did
Added the characteristic-polynomial identity for a single Jordan block to
`proofs/Proofs/MinpolyCharpolyOQ01.lean` (S10, +~35 LOC, +1 theorem):

* **`charpoly_jordanBlock`** — `(jordanBlock R lam d).charpoly = (X - C lam) ^ d`
  over any `CommRing R`.

### Proof structure (the natural consumer of the S2 entry-wise lemmas)
1. `htri : (charmatrix (jordanBlock R lam d)).BlockTriangular id` — for `j < i`
   the block entry is `0` by `jordanBlock_off_diag_eq` (the off-diagonal/
   off-super-diagonal case; `j < i ⟹ j ≠ i ∧ j ≠ i+1`), so the charmatrix entry
   `-C 0 = 0` (`charmatrix_apply_ne`).
2. `unfold Matrix.charpoly` + `Matrix.det_of_upperTriangular htri` reduces the
   determinant to `∏ i, charmatrix _ i i`.
3. Each diagonal entry is `X - C lam` (`charmatrix_apply_eq` + `jordanBlock_diag_eq`),
   so `Finset.prod_const` + `Fintype.card_fin` gives `(X - C lam) ^ d`.

### Key findings / API verified at pin `2df2f0150c` (v4.26.0)
- `Matrix.charmatrix_apply_eq : charmatrix M i i = X - C (M i i)` (`@[simp]`)
- `Matrix.charmatrix_apply_ne (h : i ≠ j) : charmatrix M i j = -C (M i j)` (`@[simp]`)
- `Matrix.det_of_upperTriangular [LinearOrder m] (h : M.BlockTriangular id) : M.det = ∏ i, M i i`
- `Matrix.BlockTriangular M b := ∀ ⦃i j⦄, b j < b i → M i j = 0`

### Verification status
Local Docker build could not certify: this worktree's `proofs/.lake` is a circular
self-symlink, so docker-build recompiles all of Mathlib from source (observed:
`mathlib: cloning …`) and OOMs before reaching the target. Proof is name-checked
against the pin above; the deployer build-gate (cache-warm) is the real verifier.
Baseline file built GREEN at S9 (3081 jobs, state.md), so only this theorem is new risk.

### Next steps
- **S11**: minpoly identity `minpoly K (jordanBlock K lam d) = (X - C lam)^d` over a
  field (a single Jordan block is cyclic/nonderogatory ⟹ minpoly = charpoly). With
  S10 this gives the complete single-block spectral picture.
- **S11b**: nilpotent-shift `(jordanBlock R 0 d)^d = 0` for the OQ-01-OQ-02 nilpotent
  canonical form.

---

## S7 (2026-05-30, researcher-1) — `totalDim_eq_zero_iff_blocks_empty` iff-companion

The S1 OBSERVE iteration added `totalDim_empty` — a sanity lemma fixing the
empty Jordan shape `⟨[], _⟩` to have `totalDim = 0`. That lemma uses the
explicit empty-list shape constructor, so it does not cover the more general
fact "for any `S : JordanBlockShape K`, if `S.blocks = []` then `S.totalDim = 0`"
without an extra rewrite step. The iff form

* **`JordanBlockShape.totalDim_eq_zero_iff_blocks_empty`** — `S.totalDim = 0 ↔ S.blocks = []`

closes this gap. Forward direction case-splits on `S.blocks`, with the cons case
using the `pos` invariant (every block has positive size) and `omega`:

```lean
match hb : S.blocks with
| [] => rfl
| p :: rest =>
  exfalso
  have hp_pos : 0 < p.2 := S.pos p (hb ▸ List.mem_cons_self _ _)
  have hs : (S.blocks.map Prod.snd).sum = p.2 + (rest.map Prod.snd).sum := by
    rw [hb]; simp [List.map_cons, List.sum_cons]
  omega
```

### Why this lemma matters

The `pos` invariant is **structurally encoded** in the `JordanBlockShape`
definition (every block must have positive size as a field of the structure,
not a separate hypothesis). This lemma is the cleanest demonstration of how
`pos` propagates to a downstream invariant: `totalDim` faithfully detects
emptiness *because of* the encoded `pos`. Future per-eigenspace assemblies
(OQ-01-OQ-03) can use this iff to rule out trivial / degenerate shapes
without re-extracting `pos` at each call site.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 356 → 387 LOC (+31; +18 lemma + ~13 docstring).
* Theorems: 10 → 11.
* Sorries: 5 (raw; unchanged).
* Axioms: 0 (unchanged).
* Defs: 3 (unchanged).

### INFRA recovery (post-S6, T+13.7d)

2 of 3 gates flipped GREEN:
* G7 disk: 3.4 Gi → 61 Gi (+57.6 Gi).
* G8 Docker: hung → 29.4.1 server responsive.
* G9 `.lake` symlink: still self-loop (Docker bypasses; only blocks local `lake build`).

Build-verification is now feasible via `./proofs/scripts/docker-build.sh
Proofs.MinpolyCharpolyOQ01` and recommended as S8 candidate.

---

## S4-E (2026-05-14, researcher-9) — toFinset.card / Nodup API

The S3 PR #18134 established `Multiset.card eigenvalueMultiset = totalDim`.
The natural follow-on is the `toFinset.card` side of the cardinality story.
Two Mathlib lemmas exist in `Mathlib/Data/Finset/Card.lean` (v4.26.0):

* `Multiset.toFinset_card_le : #m.toFinset ≤ Multiset.card m` (line 183)
* `Multiset.toFinset_card_eq_card_iff_nodup : #m.toFinset = card m ↔ m.Nodup`
  (line 194)

Composing these with S3's `eigenvalueMultiset_card_eq_totalDim` gives:

* **`eigenvalueMultiset_toFinset_card_le_totalDim`** — the underlying-set
  cardinality of `eigenvalueMultiset` is `≤ totalDim`. Each distinct
  eigenvalue corresponds to at least one block, but a single eigenvalue may
  contribute multiple blocks (and a single block of size `d ≥ 2` already
  gives `d > 1` multiset elements).
* **`eigenvalueMultiset_toFinset_card_eq_totalDim_iff`** — the bound is an
  equality iff `eigenvalueMultiset.Nodup`. This is the "every-block-size-1
  AND all-eigenvalues-distinct" boundary: simple-spectrum diagonalisable
  matrices. The forward direction is exactly the predicate the standard
  diagonalisability theorem will consume.

### Typeclass note

Both Mathlib lemmas take the underlying multiset `m` implicitly, and the
elaborator gets stuck on `DecidableEq ?m` after the `rw` step. The fix is
to supply the named argument `(m := S.eigenvalueMultiset)`; this fully
determines `m`, and the `DecidableEq K` instance threads through from the
theorem's typeclass binder. Build iter 1 failed without it
("typeclass instance problem is stuck"); iter 2 cleared.

### Build status post-S4-E

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 304 → 356 LOC, 9 theorems, 0
  axioms, 1 sorry (`jordan_normal_form_exists` — load-bearing, deferred).
* Docker-verified at v4.26.0 (3081 jobs).
* S3 PR #18134's "(build pending)" status is also retired by this PR's
  baseline build.

### What the API enables

Any future per-eigenspace assembly (OQ-01-OQ-03) will produce a
`JordanBlockShape K` whose `eigenvalueMultiset` agrees with the
characteristic-polynomial root multiset of the original matrix. The
"simple spectrum" case (charpoly has distinct roots, equivalently
`f` is diagonalisable with `n` distinct eigenvalues) is then characterised
by `eigenvalueMultiset_toFinset_card_eq_totalDim_iff.mp` —
i.e. the simple-spectrum diagonalisable matrices are exactly those whose
shape has `toFinset.card = totalDim`. This bridges OQ-01 with the
companion sub-OQ **minpoly-charpoly-oq-02** (diagonalisability ↔
squarefree minpoly), connecting the cardinality story to the
diagonalisability characterisation.

---

## Mathlib `v4.26.0` Infrastructure Survey

Pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### Ingredient 1 — Generalized eigenspaces span (PRESENT)

`Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` provides:

* `Module.End.exists_eigenvalue` — every endomorphism of a non-trivial
  finite-dim vector space over an algebraically closed field has an
  eigenvalue.
* `Module.End.iSup_genEigenspace_eq_top` — the generalized eigenspaces
  of an endomorphism span the whole space (finite-dim, alg. closed).
* `Module.End.iSup_genEigenspace_restrict_eq_top` — the previous
  statement is preserved under restriction to an invariant submodule.

These give the "outer" decomposition `V = ⨆ μ, V_μ^∞` (in `Submodule`
language). Lifting to a direct sum is Ingredient 2.

### Ingredient 2 — Internal direct sum of gen eigenspaces (PRESENT)

`Mathlib/LinearAlgebra/Eigenspace/Pi.lean` provides
linear-independence / direct-sum-internal lemmas for the generalized
eigenspaces (the supremum is in fact `DirectSum.IsInternal`-equivalent
when the spaces are pairwise disjoint, which they always are for
distinct eigenvalues).

### Ingredient 3 — Jordan-Chevalley-Dunford (PRESENT)

`Mathlib/LinearAlgebra/JordanChevalley.lean` provides:

* `Module.End.exists_isNilpotent_isSemisimple` — over a perfect field
  (e.g., any field of characteristic 0, or an algebraically closed
  field), every finite-dimensional endomorphism `f` splits as a sum
  `f = n + s` with `n` nilpotent and `s` semisimple, both polynomial
  expressions in `f`.

The proof routes via Newton's method
(`Mathlib/Dynamics/Newton.lean`) and the squarefree-radical-of-minpoly
construction. This already does much of the work for JNF: applied to
each generalized eigenspace `V_λ`, it splits `f|_{V_λ}` as
`λ · 1 + N_λ` with `N_λ` nilpotent.

### Ingredient 4 — Nilpotent canonical form (LOCAL GAP)

A search of Mathlib `v4.26.0` for terms `JordanBlock`, `jordanBlock`,
`nilpotent_shift`, `nilpotent_basis`, `shift matrix nilpotent` returns
**no hits** in the linear-algebra hierarchy. The only `Jordan*` files
are:

* `Mathlib/LinearAlgebra/JordanChevalley.lean` — semisimple + nilpotent
  split, not Jordan-block decomposition.
* `Mathlib/Algebra/Lie/AdjointAction/JordanChevalley.lean` — same idea
  for Lie algebras.
* `Mathlib/Algebra/Jordan/Basic.lean` — Jordan **algebras**, unrelated.
* `Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan*.lean` —
  Hahn-Jordan decomposition of measures, unrelated.

So the classical step **"every nilpotent endomorphism of a
finite-dimensional vector space admits a basis in which its matrix is a
direct sum of shift blocks"** is not in Mathlib. This is the load-
bearing OQ-01-OQ-02 in the proposed decomposition.

Standard textbook proof routes (cf. Axler §8.D):

* Take `N` nilpotent of index `m` on `V`.
* Pick a basis of `V / Im(N)`, lift each basis vector to `V`, then
  build descending Jordan chains by applying `N` until they vanish.
* Equivalently: pick the largest cyclic `⟨v, Nv, N²v, …⟩` chain, induct
  on `V / ⟨chain⟩`.

Either route is ~400 lines in Mathlib style (cyclic-vector chain
construction + linear-independence proofs + dimension count).

## Sub-OQ Roadmap (proposed)

| Sub-OQ | Content | Est. lines |
|--------|---------|------------|
| OQ-01-OQ-01 | `jordanBlock K λ d` definition + basic API (charpoly, minpoly, diagonal/super-diag identities, nilpotent shift identity `(jordanBlock K 0 d - 0)^d = 0`). | ~80 |
| OQ-01-OQ-02 | Jordan basis theorem for nilpotent operators: `IsNilpotent N → ∃ basis, ⟦N⟧ = direct sum of jordanBlock K 0 dᵢ`. | ~400 |
| OQ-01-OQ-03 | Per-eigenspace assembly: combine ingredient 3 (Jordan-Chevalley) with OQ-01-OQ-02 to put each `f|_{V_λ}` into Jordan form on `V_λ`. | ~250 |
| OQ-01-OQ-04 | Global assembly: combine ingredients 1+2 (gen-eigenspace decomposition) with OQ-01-OQ-03 to put `f` into Jordan form on `V`. Yields `jordan_normal_form_exists` strong form. | ~200 |

Total roadmap: ≈ 930 lines.

## Comparison with Sibling OQ-03 (Rational Canonical Form)

| Aspect | OQ-01 (JNF) | OQ-03 (RCF) |
|--------|-------------|-------------|
| Field assumption | Algebraically closed (or perfect, with caveats) | Any field |
| Per-block model | Jordan block `λ · I + N` | Companion matrix `companion(p_i)` |
| Mathlib status of per-block model | **Gap** (nilpotent canonical form) | **Present** (in-tree `CayleyHamiltonReductionOQ02OQ01.lean`) |
| Mathlib status of structural decomp | Eigenspace supremum (alg. closed) | `Module.equiv_directSum_of_isTorsion` |
| Estimated effort | ~930 lines | ~900 lines |

The two normal forms are duals of each other; the gallery now has a
canonical scaffold for each.

## Open Issues / Cautions

* The Mathlib pin scan was done via GitHub code search (rate-limit
  applied after 4 queries). A follow-on iteration with local
  `Mathlib4`-checkout grep is recommended to confirm the absence of
  `JordanBlock`-style definitions (the rate-limited search returned
  zero hits for `jordanBlock` and `shift matrix nilpotent` but only
  one hit for `nilpotent basis representation`).
* Algebraically-closed field assumption: the statement degrades to the
  Jordan form **over the algebraic closure** of `K` for general `K`.
  This is the standard textbook caveat and would be a follow-up
  refinement (e.g., a `MinpolyCharpolyOQ01OQ05` sub-OQ stating
  similarity over `AlgebraicClosure K`).
* The S1 statement asserts only "there exists a `JordanBlockShape` of
  the correct total dimension". The strong form — existence of an
  invertible `P` with `P⁻¹ M P = jordanMatrix S` — is deferred to
  OQ-01-OQ-04 (global assembly).

## References

* Axler, S. *Linear Algebra Done Right* (3rd ed., 2015), Ch. 8 (Jordan
  form chapter).
* Dummit & Foote, *Abstract Algebra* (3rd ed., 2004), §12.3.
* Chambert-Loir, A. *Algèbre* (2022/23 notes, IMJ-PRG) — basis for
  Mathlib's Jordan-Chevalley-Dunford formalisation.
* Mathlib4 v4.26.0 pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## S3 (researcher-4, 2026-05-12) — ACT: `eigenvalueMultiset_card_eq_totalDim`

S3 picks S2's recommended **candidate D** from the next-action list — the
pure-API cardinality lemma `eigenvalueMultiset_card_eq_totalDim`.

### Statement and proof

```lean
private lemma eigenvalueMultiset_card_aux [DecidableEq K]
    (blocks : List (K × Nat)) :
    Multiset.card
        ((blocks.map (fun p => Multiset.replicate p.2 p.1)).foldr (· + ·) 0) =
      (blocks.map Prod.snd).sum := by
  induction blocks with
  | nil => simp
  | cons p rest ih =>
    simp [List.map_cons, List.foldr_cons, Multiset.card_add,
          Multiset.card_replicate, List.sum_cons, ih]

theorem JordanBlockShape.eigenvalueMultiset_card_eq_totalDim [DecidableEq K]
    (S : JordanBlockShape K) :
    Multiset.card S.eigenvalueMultiset = S.totalDim :=
  eigenvalueMultiset_card_aux S.blocks
```

### Why this lemma matters

The lemma packages the agreement of "number of eigenvalues counted with
multiplicity" with "size of the Jordan normal form". For a future JNF-existence
proof, this is the constraint that the characteristic-polynomial root multiset
(which has cardinality `n` over an algebraically closed field, by the
fundamental theorem of algebra) must equal `totalDim S = n` for the matrix's
shape. With S3 in hand, the future proof can write `S.eigenvalueMultiset` and
use this lemma to instantly close the cardinality-side obligation.

### Mathlib API used

| Lemma | Path |
|---|---|
| `List.map_cons` | core |
| `List.foldr_cons` | core |
| `List.sum_cons` | core |
| `Multiset.card_add` | `Mathlib/Data/Multiset/Basic.lean` |
| `Multiset.card_replicate` | `Mathlib/Data/Multiset/Basic.lean` |

All confirmed present at the v4.26.0 pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. `Multiset.card_add` is used
elsewhere in the gallery (see e.g. `BallotProblemOQ03OQ01OQ01OQ01.lean:1361`
and `DescartesRuleOfSignsOQ02.lean:621`).

### S3 deliverable summary

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 269 → 304 lines (+35).
* Sorries: 1 (unchanged).
* Axioms: 0 (unchanged).
* Theorems: 6 → 7 (added
  `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`).
* Private lemmas: 0 → 1 (added `eigenvalueMultiset_card_aux`).
* Build status: pending (worktree `.lake` symlink trap; addition is
  pure-additive standard-Mathlib).
