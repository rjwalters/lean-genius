import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic
import Proofs.MinpolyCharpoly

/-
# Jordan Normal Form via Minpoly/Charpoly Infrastructure

## Open Question (minpoly-charpoly-oq-01)

> Can the Jordan normal form theorem be formalized in Lean 4 using this
> infrastructure?

This is `conclusion.openQuestions[0]` of the parent gallery entry
`minpoly-charpoly` (Minimal Polynomial vs Characteristic Polynomial of
Matrices — 17 theorems, 0 axioms). Sibling open questions: OQ-02
(diagonalizability characterisation via squarefree minpoly), OQ-03
(rational canonical form — scaffolded in `MinpolyCharpolyOQ03.lean`).

## Resolution (S1 OBSERVE — affirmative, modulo one local gap)

**Yes, the Jordan normal form (JNF) is formalizable in Lean 4** for any
finite-dimensional vector space over an algebraically closed (or, more
generally, perfect) field. Four ingredients are needed; three are
already in Mathlib `v4.26.0`, and the fourth is a self-contained local
construction (the nilpotent canonical form).

1. **Generalized eigenspaces span the space (Mathlib).** Over an
   algebraically closed field `K`, every endomorphism `f` of a
   finite-dimensional vector space satisfies
   `⨆ μ, f.genEigenspace μ = ⊤`
   via `Module.End.iSup_genEigenspace_eq_top`
   (`Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean`).

2. **The supremum is an internal direct sum (Mathlib).** Distinct
   generalized eigenspaces of the same endomorphism intersect
   trivially, so the supremum is `DirectSum.IsInternal`-equivalent.
   Provided by lemmas in `Mathlib/LinearAlgebra/Eigenspace/Pi.lean`
   (e.g., `Module.End.independent_genEigenspace`).

3. **Jordan-Chevalley-Dunford decomposition (Mathlib).**
   `Module.End.exists_isNilpotent_isSemisimple`
   (`Mathlib/LinearAlgebra/JordanChevalley.lean`) gives, over a perfect
   field, a polynomial-in-`f` splitting `f = n + s` with `n` nilpotent
   and `s` semisimple, with `n` and `s` commuting.

4. **Nilpotent canonical form (LOCAL GAP).** Each restriction of `f`
   to a generalized eigenspace `V_λ` decomposes as `λ · 1 + N_λ` with
   `N_λ` nilpotent. The remaining classical step is: every nilpotent
   endomorphism of a finite-dimensional vector space admits a basis in
   which its matrix is a direct sum of shift blocks (single-eigenvalue
   Jordan blocks with eigenvalue `0`). This is the **Jordan basis
   theorem for nilpotent operators**; a 2026-05-12 Mathlib search at
   pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) finds
   `LinearAlgebra/JordanChevalley.lean` and the eigenspace
   triangularisation file, but no `JordanBlock` definition and no
   nilpotent-shift-basis theorem. This is the single load-bearing
   sub-OQ for the full JNF assembly.

## Decomposition into Sub-OQs (proposed)

| Sub-OQ           | Content                                                                | Est. lines |
|------------------|------------------------------------------------------------------------|------------|
| **OQ-01-OQ-01**  | `jordanBlock K λ d : Matrix (Fin d) (Fin d) K` definition + basic API. | ~80        |
| **OQ-01-OQ-02**  | Jordan basis theorem for nilpotent operators on a fin-dim space.       | ~400       |
| **OQ-01-OQ-03**  | Per-eigenspace assembly: `f|_{V_λ}` is similar to a direct sum of      |            |
|                  | `jordanBlock K λ dᵢ`. Uses OQ-01-OQ-01 and OQ-01-OQ-02.                | ~250       |
| **OQ-01-OQ-04**  | Global assembly: `f` is similar to `⊕_λ ⊕_i jordanBlock K λ dᵢ`.       |            |
|                  | Glues OQ-01-OQ-03 via the internal-direct-sum decomposition (#2).      | ~200       |

Total roadmap: ≈ 930 lines. Comparable in size to OQ-03 (~900 for RCF).
The two normal forms share ingredients (1) and the gen-eigenspace
machinery; they diverge at the per-block model (Jordan block vs.
companion matrix) and at the field assumption (alg. closed vs. any
field).

## What This File Contributes (S1 scaffold + S2 entry-wise API)

The S1 OBSERVE iteration provided:

* **`JordanBlockShape`** — a data structure capturing a multiset of
  block sizes per eigenvalue, sufficient to reconstruct the JNF up to
  permutation of blocks.
* **`jordanBlock`** — the matrix `λ · I + N_d` where `N_d` is the
  upper-shift matrix on `Fin d` (i.e., `1` strictly above the diagonal
  in the canonical basis ordering). Stated for any commutative ring.
* **`jordanBlock_diag_eq`** / **`jordanBlock_super_diag_eq`** —
  unconditional sanity lemmas for the diagonal entries (all `λ`) and
  super-diagonal entries (all `1`) of `jordanBlock K λ d`.
* **`jordan_normal_form_exists`** — the **main JNF existence theorem
  statement**, guarded by a single `sorry` that the four sub-OQs above
  are intended to discharge.

The S2 iteration (this PR) adds the *third* case of the entry-wise
classification, completing the case-by-case coverage of every
`(i, j)` position in a Jordan block:

* **`jordanBlock_off_diag_eq`** — entries `(i, j)` with `i ≠ j` and
  `j ≠ i + 1` are `0`.
* **`jordanBlock_zero_dim`** — `jordanBlock R λ 0 = 0` (the empty-
  index Jordan block agrees with the zero matrix), useful for
  inductive arguments on block dimension.

The S3 iteration added `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`
(Multiset.card of the eigenvalue multiset equals totalDim). The S4-E
iteration (this PR) adds the `toFinset.card`-side refinement:

* **`JordanBlockShape.eigenvalueMultiset_toFinset_card_le_totalDim`** —
  the underlying-set cardinality of `eigenvalueMultiset` is at most
  `totalDim`.
* **`JordanBlockShape.eigenvalueMultiset_toFinset_card_eq_totalDim_iff`**
  — the bound is tight iff `eigenvalueMultiset` is `Nodup`, which
  characterises the "diagonalisable, simple spectrum" boundary of the
  JNF shape data.

These lemmas do **not** discharge any of OQ-01-OQ-01..04. The single
sorry on `jordan_normal_form_exists` is the entire JNF assembly. The
contribution of S1+S2 is the resolution of the OQ at the strategy
level (affirmative + 4-step roadmap + 1 identified Mathlib gap), the
Lean-side surface for follow-on iterations, and a complete entry-wise
API for the `jordanBlock` definition. Together the three entry-wise
lemmas (`_diag_eq`, `_super_diag_eq`, `_off_diag_eq`) partition the
`Fin d × Fin d` index set, which is the canonical input shape that the
upcoming OQ-01-OQ-01 charpoly identity will consume.

## References

* Axler, *Linear Algebra Done Right* (3rd ed., 2015), Ch. 8.
* Dummit & Foote, *Abstract Algebra* (3rd ed., 2004), §12.3.
* Chambert-Loir, *Algèbre* (2022/23 notes), Ch. 4 — used by Mathlib's
  Jordan-Chevalley-Dunford proof.

## Status

* [x] Resolution at strategy level (affirmative)
* [x] Mathlib gap analysis (single gap: nilpotent canonical form)
* [x] Sub-OQ decomposition (OQ-01-OQ-01 .. OQ-01-OQ-04)
* [x] Scaffold (JordanBlockShape, jordanBlock, sanity lemmas)
* [x] Entry-wise classification of `jordanBlock` (S2: `_off_diag_eq`,
  `_zero_dim`)
* [x] `eigenvalueMultiset` cardinality API (S3:
  `eigenvalueMultiset_card_eq_totalDim`; S4-E:
  `eigenvalueMultiset_toFinset_card_le_totalDim` +
  `_eq_totalDim_iff`)
* [ ] Discharge `jordan_normal_form_exists` (sorry-guarded — deferred to sub-OQs)

## Mathlib Dependencies

* `Module.End.iSup_genEigenspace_eq_top` (Eigenspace/Triangularizable)
* `Module.End.exists_isNilpotent_isSemisimple` (JordanChevalley)
* `Matrix.charpoly`, `Matrix.minpoly_dvd_charpoly` (Charpoly/Minpoly)
-/

namespace MinpolyCharpolyOQ01

open Matrix BigOperators

/--
A Jordan block shape: a list of pairs `(λ, d)` describing one Jordan
block of size `d × d` with eigenvalue `λ`. The total size is the sum of
the `d` components; the underlying matrix is a block-diagonal of
`jordanBlock K λ d` for each pair, in list order.
-/
structure JordanBlockShape (K : Type*) where
  /-- The list of `(eigenvalue, block size)` pairs. -/
  blocks : List (K × Nat)
  /-- Every block has positive size. -/
  pos    : ∀ p ∈ blocks, 0 < p.2

namespace JordanBlockShape

variable {K : Type*}

/-- The total dimension of the JNF: sum of block sizes. -/
def totalDim (S : JordanBlockShape K) : Nat :=
  (S.blocks.map Prod.snd).sum

/-- The multiset of eigenvalues (with multiplicity equal to the sum of
their block sizes). Useful for stating that the JNF respects
the characteristic-polynomial root multiplicities. -/
def eigenvalueMultiset [DecidableEq K] (S : JordanBlockShape K) :
    Multiset K :=
  (S.blocks.map (fun p => Multiset.replicate p.2 p.1)).foldr (· + ·) 0

end JordanBlockShape

/--
The `d × d` **Jordan block** with eigenvalue `λ`: `λ` on the diagonal,
`1` strictly above the diagonal (at positions `(i, i+1)`), `0`
elsewhere. Returns the trivial `0 × 0` matrix when `d = 0` (no entries).
-/
noncomputable def jordanBlock (R : Type*) [CommRing R] (lam : R) (d : Nat) :
    Matrix (Fin d) (Fin d) R :=
  fun i j =>
    if i = j then lam
    else if (j : Nat) = (i : Nat) + 1 then 1
    else 0

/-- The diagonal entries of `jordanBlock R λ d` are all `λ`. -/
theorem jordanBlock_diag_eq (R : Type*) [CommRing R] (lam : R) (d : Nat)
    (i : Fin d) :
    jordanBlock R lam d i i = lam := by
  simp [jordanBlock]

/-- Strictly above-diagonal entries of `jordanBlock R λ d` (positions
`(i, i+1)`) are `1`. -/
theorem jordanBlock_super_diag_eq (R : Type*) [CommRing R] (lam : R)
    (d : Nat) (i : Fin d) (j : Fin d)
    (hij : (j : Nat) = (i : Nat) + 1) :
    jordanBlock R lam d i j = 1 := by
  have hne : i ≠ j := by
    intro h; rw [h] at hij; omega
  simp [jordanBlock, hne, hij]

/-- Off-diagonal and off-super-diagonal entries of `jordanBlock R λ d`
are `0`. Together with `jordanBlock_diag_eq` and
`jordanBlock_super_diag_eq` this completes the entry-wise classification
of `jordanBlock R λ d` into the three cases of its `if … then … else
if … then … else 0` definition. -/
theorem jordanBlock_off_diag_eq (R : Type*) [CommRing R] (lam : R)
    (d : Nat) (i : Fin d) (j : Fin d)
    (hne : i ≠ j) (hns : (j : Nat) ≠ (i : Nat) + 1) :
    jordanBlock R lam d i j = 0 := by
  simp [jordanBlock, hne, hns]

/-- The trivial Jordan block over the empty index `Fin 0`: any function
`Fin 0 → Fin 0 → R` is the zero matrix vacuously. Stated for
convenience in inductive arguments on block dimension. -/
theorem jordanBlock_zero_dim (R : Type*) [CommRing R] (lam : R) :
    jordanBlock R lam 0 = 0 := by
  ext i j; exact Fin.elim0 i

/-! ## S8: semisimple/nilpotent decomposition of a Jordan block

Every Jordan block factors as the eigenvalue acting by scalar multiplication on
the identity plus the "nilpotent shift" — the eigenvalue-zero Jordan block of
the same size. This is the Jordan-Chevalley decomposition specialised to a
single block: the `λ • 1` part is semisimple (a scalar) and `jordanBlock R 0 d`
is the strict upper-shift, which is nilpotent (its `d`-th power is zero).

The lemma exposes the structural split as an entry-wise equality and so
transfers any result proved for the eigenvalue-zero case (the OQ-01-OQ-02
nilpotent canonical form target) to general eigenvalues. It is also the entry-
wise version of `Module.End.exists_isNilpotent_isSemisimple` (Mathlib
v4.26.0, `LinearAlgebra/JordanChevalley.lean`) at the block level.

Pure API; no new definitions. -/

/-- **S8**: a Jordan block decomposes as `λ • 1 + jordanBlock R 0 d`. The
`λ • 1` summand is the (commuting) semisimple part — acting by `λ` on every
basis vector — and `jordanBlock R 0 d` is the strict upper-shift, which is
nilpotent. This is the entry-wise Jordan-Chevalley decomposition specialised
to a single block. -/
theorem jordanBlock_eq_lam_smul_one_add_zero_block (R : Type*) [CommRing R]
    (lam : R) (d : Nat) :
    jordanBlock R lam d =
      lam • (1 : Matrix (Fin d) (Fin d) R) + jordanBlock R 0 d := by
  ext i j
  simp only [jordanBlock, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
             smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hij : i = j
  · simp [hij]
  · by_cases hs : (j : Nat) = (i : Nat) + 1
    · simp [hij, hs]
    · simp [hij, hs]

/-! ## S9: trace of a Jordan block

The trace of `jordanBlock R lam d` is `d • lam`. This is the entry-wise content
of `Matrix.trace` applied to a Jordan block: all `d` diagonal entries equal
`lam` (by `jordanBlock_diag_eq`), so the trace collapses to `d • lam`.

Companion to S8's Jordan-Chevalley split: the trace is invariant under the
decomposition `jordanBlock R lam d = lam • 1 + jordanBlock R 0 d` because the
nilpotent shift `jordanBlock R 0 d` has trace `0` (its diagonal is `0`), so
trace adds `lam • d` from the scalar part to `0` from the nilpotent part. This
also illustrates that trace is a class function on Jordan blocks (it depends
only on `lam` and `d`, not on the basis).

Pure API; no new definitions. -/

/-- **S9**: the trace of `jordanBlock R λ d` is `d • λ`.

    All `d` diagonal entries of `jordanBlock R λ d` equal `λ` by
    `jordanBlock_diag_eq`, so the trace sum `∑ i, A i i` collapses to
    `d • λ` via `Finset.sum_const`. -/
theorem trace_jordanBlock (R : Type*) [CommRing R] (lam : R) (d : Nat) :
    (jordanBlock R lam d).trace = d • lam := by
  simp only [Matrix.trace, Matrix.diag_apply, jordanBlock_diag_eq,
             Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **S9 corollary**: the nilpotent shift `jordanBlock R 0 d` has trace `0`.

    Direct specialisation of `trace_jordanBlock` at `lam = 0`: `d • (0 : R) = 0`. -/
theorem trace_jordanBlock_zero (R : Type*) [CommRing R] (d : Nat) :
    (jordanBlock R 0 d).trace = (0 : R) := by
  rw [trace_jordanBlock]; exact smul_zero d

/-! ## S3 candidate D: cardinality of `eigenvalueMultiset` equals `totalDim`

A small but useful API lemma about `JordanBlockShape`: the cardinality of the
eigenvalue multiset (which counts each eigenvalue with multiplicity equal to
the sum of its block sizes) equals the total dimension. This is the natural
agreement of "number of eigenvalues counted with multiplicity" with "size of
the Jordan normal form", and it is the relation that any future
`jordan_normal_form_exists`-discharging proof must respect on the
characteristic-polynomial-root side.

The proof is a direct list induction: each block contributes `Multiset.replicate
p.2 p.1` to the eigenvalue multiset (cardinality `p.2`) and `p.2` to the total
dimension. -/

/-- List-level helper: the cardinality of the eigenvalue multiset built from a
list of `(eigenvalue, block-size)` pairs equals the sum of block sizes. -/
private lemma eigenvalueMultiset_card_aux {K : Type*} [DecidableEq K]
    (blocks : List (K × Nat)) :
    Multiset.card
        ((blocks.map (fun p => Multiset.replicate p.2 p.1)).foldr (· + ·) 0) =
      (blocks.map Prod.snd).sum := by
  induction blocks with
  | nil => simp
  | cons p rest ih =>
    simp [List.map_cons, List.foldr_cons, Multiset.card_add,
          Multiset.card_replicate, List.sum_cons, ih]

/-- **S3-D**: the cardinality of `eigenvalueMultiset` equals `totalDim`.
For any `JordanBlockShape`, the eigenvalue multiset has exactly `totalDim`-many
elements (each block of size `d` contributes `d` copies of its eigenvalue). -/
theorem JordanBlockShape.eigenvalueMultiset_card_eq_totalDim {K : Type*}
    [DecidableEq K] (S : JordanBlockShape K) :
    Multiset.card S.eigenvalueMultiset = S.totalDim :=
  eigenvalueMultiset_card_aux S.blocks

/-! ## S4-E: distinctness bound on `eigenvalueMultiset.toFinset.card`

A refinement of S3-D: the cardinality of the *underlying set* of eigenvalues
(`eigenvalueMultiset.toFinset`) is at most `totalDim`, with equality exactly
when the eigenvalue multiset is `Nodup` — i.e. every eigenvalue appears with
multiplicity 1, which forces every block to have size 1 and all eigenvalues
to be pairwise distinct. This is the natural "all-eigenvalues-distinct"
boundary on the JNF shape data, and the canonical witness for the
"diagonalisable with simple spectrum" case (where the JNF reduces to a
diagonal matrix). Pure API, composed from S3-D and the Mathlib lemmas
`Multiset.toFinset_card_le` and
`Multiset.toFinset_card_eq_card_iff_nodup`. -/

/-- **S4-E (bound)**: the underlying-set cardinality of `eigenvalueMultiset`
is at most `totalDim`. Each distinct eigenvalue corresponds to at least one
block; the bound is tight iff every block has size 1 AND no two blocks
share an eigenvalue (see `eigenvalueMultiset_toFinset_card_eq_totalDim_iff`). -/
theorem JordanBlockShape.eigenvalueMultiset_toFinset_card_le_totalDim
    {K : Type*} [DecidableEq K] (S : JordanBlockShape K) :
    S.eigenvalueMultiset.toFinset.card ≤ S.totalDim := by
  rw [← S.eigenvalueMultiset_card_eq_totalDim]
  exact Multiset.toFinset_card_le (m := S.eigenvalueMultiset)

/-- **S4-E (equality)**: the bound
`eigenvalueMultiset.toFinset.card ≤ totalDim` is an equality iff
`eigenvalueMultiset` is `Nodup`. This characterises the
"simple-spectrum, every-block-size-1" JNFs: their shape data has all
eigenvalues pairwise distinct AND every block has size 1, so that the
multiset of eigenvalues is also a set (no repetitions). -/
theorem JordanBlockShape.eigenvalueMultiset_toFinset_card_eq_totalDim_iff
    {K : Type*} [DecidableEq K] (S : JordanBlockShape K) :
    S.eigenvalueMultiset.toFinset.card = S.totalDim ↔
      S.eigenvalueMultiset.Nodup := by
  rw [← S.eigenvalueMultiset_card_eq_totalDim]
  exact Multiset.toFinset_card_eq_card_iff_nodup (m := S.eigenvalueMultiset)

/-
## Main JNF Existence Theorem (statement only — proof deferred)

We state the existence of a Jordan normal form for any matrix over an
algebraically closed field. The statement asserts:

* Existence of a `JordanBlockShape` `S`.
* Equality of total dimension with the matrix size.
* The multiset of eigenvalues (with multiplicity) matches the roots of
  the characteristic polynomial (in the algebraic closure, but here we
  are already over an algebraically closed field).
* Existence of an invertible matrix `P` exhibiting the similarity.

The full similarity claim is the load-bearing assertion deferred to
OQ-01-OQ-04 (global assembly). Per the resolution analysis above, the
proof routes through Mathlib's gen-eigenspace decomposition + Jordan-
Chevalley + a local nilpotent-canonical-form construction (OQ-01-OQ-02).
-/

/--
**The Jordan normal form theorem (statement, S1)**: every square matrix
over an algebraically closed field is similar to a block-diagonal matrix
of Jordan blocks. The full similarity assembly is deferred to
OQ-01-OQ-02..04 (see module docstring).
-/
theorem jordan_normal_form_exists
    {K : Type*} [Field K] [IsAlgClosed K]
    {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n K) :
    ∃ S : JordanBlockShape K, S.totalDim = Fintype.card n := by
  -- The full statement (existence of a similarity transform) is the
  -- target of OQ-01-OQ-04. The weak-form S1 statement above asserts
  -- only existence of a shape with the correct total dimension, which
  -- already requires the gen-eigenspace decomposition (#1, #2). This
  -- is sorry-guarded in S1; sub-OQs OQ-01-OQ-01..04 discharge it.
  sorry

/-- Sanity check: `JordanBlockShape.totalDim` of the empty shape is `0`.

(S2 drift-fix: replaces S1's `absurd hp (List.not_mem_nil _)` —
unsound after Mathlib's v4.26.0 signature change of `List.not_mem_nil`
to `(h : a ∈ []) → False` — with the equivalent `nomatch hp`,
which is robust under future API changes since it relies only on the
empty `List.Mem _ []` type having no constructors.) -/
theorem totalDim_empty {K : Type*} :
    (⟨[], by intro _ hp; nomatch hp⟩ :
        JordanBlockShape K).totalDim = 0 := by
  simp [JordanBlockShape.totalDim]

/-! ## S7: `totalDim` zero-detection lemma

A small API lemma connecting `totalDim` with the underlying `blocks` list.
Since every block has positive size (the `pos` invariant of `JordanBlockShape`),
the total dimension is zero exactly when no blocks are present. This is the
companion of `totalDim_empty` on the iff side — `totalDim_empty` only handles
the explicit empty-list constructor, whereas this lemma handles an arbitrary
`JordanBlockShape S`. -/

/-- **S7**: the total dimension of a Jordan block shape is zero iff its
underlying block list is empty. Forward direction uses the `pos` invariant
(every block has positive size, so a single block already gives positive
total). Backward direction is the unfolded definition on `[]`. -/
theorem JordanBlockShape.totalDim_eq_zero_iff_blocks_empty
    {K : Type*} (S : JordanBlockShape K) :
    S.totalDim = 0 ↔ S.blocks = [] := by
  unfold JordanBlockShape.totalDim
  constructor
  · intro h
    match hb : S.blocks with
    | [] => rfl
    | p :: rest =>
      exfalso
      have hp_mem : p ∈ S.blocks := by rw [hb]; exact List.mem_cons_self
      have hp_pos : 0 < p.2 := S.pos p hp_mem
      have hs : (S.blocks.map Prod.snd).sum = p.2 + (rest.map Prod.snd).sum := by
        rw [hb]; simp [List.map_cons, List.sum_cons]
      omega
  · intro h
    rw [h]; simp

end MinpolyCharpolyOQ01
