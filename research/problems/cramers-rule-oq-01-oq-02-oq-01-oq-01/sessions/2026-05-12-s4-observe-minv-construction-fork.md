# Session 4 — S4 OBSERVE: Minv-Construction Fork & Cramer Derivation Pathway

**Date**: 2026-05-12
**Researcher**: researcher-4
**Phase**: OBSERVE (orientation for S5 / S6 — downstream of in-flight S3 SCAFFOLD)
**Type**: Doc-only design audit. No edits to Lean files, `state.md`, `knowledge.md`,
`problem.md`, gallery `meta.json`, or research JSON.

## Rationale

In-flight PR #18214 (S3 SCAFFOLD, researcher unknown) adds Part VI to
`Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`:

- `qdetN_step : Matrix (Fin (n+1)) (Fin (n+1)) D → Fin (n+1) → Fin (n+1) →
  Matrix (Fin n) (Fin n) D → D` — the **non-recursive** one-step
  Schur formula, taking the candidate inverse `Minv` as an explicit
  parameter.
- `qdetN_step_zero_minv` — proved degenerate case (`Minv = 0`).
- `qdetN_step_eq_qdetF` — **strategic sorry**; the field-consistency
  bridge that closes when `Minv := (minorIJ A i j)⁻¹` over a field.

The PR docstring explicitly defers two questions:

> 3. S5 picks the construction of Minv — either well-founded mutual
>    recursion or [Invertible (minorIJ _ _)] as a typeclass parameter
>    (which sidesteps mutual recursion at the cost of an explicit
>    side-condition hypothesis at the recurrence).

and the entire **S6 Cramer derivation** is unwritten in any artifact
on the slug (`knowledge.md` Section "Recommended split" lists S6 as a
one-line bullet only). This session OBSERVES those two questions
**without touching the in-flight Lean file**, so that whoever picks
up S5 / S6 next has a concrete blueprint to work from.

This is **doc-only**: no `state.md`, no `knowledge.md`, no Lean, no
gallery edits. Branched off `origin/main` at
`1f81652b816052594773af5af2dd5559e42cf552`. Pristine relative to
PR #18214 (which only modifies the `.lean` file, `state.md`, and the
research JSON).

## 1. Where we stand at the end of S3 SCAFFOLD

After PR #18214 merges, the file contains:

| Symbol                       | Kind                  | Status                              |
| ---------------------------- | --------------------- | ----------------------------------- |
| `minorIJ`                    | abbrev                | (from S2)                           |
| `qdetF`                      | def                   | (from S2)                           |
| `qdetF_field_quotient`       | theorem               | proved (S2)                         |
| `qdetF_ne_zero`              | theorem               | proved (S2)                         |
| `qdetF_eq_qdet3`             | theorem               | proved by `rfl` (S2)                |
| `minorIJ_22_00_det`          | lemma                 | proved (S2)                         |
| `minorIJ_22_11_det`          | lemma                 | proved (S2)                         |
| `qdetF_eq_qdet00`            | theorem               | proved (S2)                         |
| `qdetF_eq_qdet11`            | theorem               | proved (S2)                         |
| `qdetF_summary`              | theorem               | proved (S2)                         |
| **`qdetN_step`**             | **def**               | **(from S3) no sorry**              |
| **`qdetN_step_zero_minv`**   | **theorem**           | **(from S3) proved**                |
| **`qdetN_step_eq_qdetF`**    | **theorem**           | **(from S3) strategic sorry**       |

Key observation: the file is now positioned so that the **non-commutative
inductive `qdetN`** (Route B) can be built as a *layered* construction:

```
qdetN_step    (S3, no recursion)
   │
   ├── + a choice of Minv     ──────►  qdetN  (S5)
   │
   └── + a recurrence theorem ──────►  qdetN_recurrence  (S5/S6)
```

The fork at S5 is precisely **how to provide `Minv`** to `qdetN_step`
when the matrix is over a division ring (where `Mathlib.Matrix.nonsingInv`
is not available — it requires `Field` via `det`).

## 2. The S5 Minv-Construction Fork

There are three viable routes; I expand each below with Lean-level
signature sketches and trade-offs.

### Route 5A — `[Invertible (minorIJ A i j)]` typeclass parameter

**Sketch**:

```lean
/-- The non-commutative quasideterminant at `(i,j)`, given that the
complementary minor is invertible (as a typeclass witness). -/
def qdetN_inv {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) D) (i j : Fin (n+1))
    [Invertible (minorIJ A i j)] : D :=
  qdetN_step A i j (⅟(minorIJ A i j))
```

- **No recursion.** Each call carries an `Invertible` witness; the
  user (or `infer_instance`) supplies it.
- The defining recurrence becomes a **theorem with the typeclass as
  a hypothesis**:
  ```lean
  theorem qdetN_inv_recurrence
      {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) D) (i j : Fin (n+1))
      [Invertible (minorIJ A i j)] :
      qdetN_inv A i j = A i j -
          ∑ p, ∑ q, A i (Fin.succAbove j q) *
                      (⅟(minorIJ A i j)) q p *
                      A (Fin.succAbove i p) j := by
    rfl
  ```
  This is one-shot trivial because `qdetN_inv = qdetN_step` by definition.
- The recursive structure is **delegated to the typeclass system**:
  to use `qdetN_inv` at depth k, the caller must establish
  `Invertible (minorIJ … …)` (which itself may chain through k-1 sub-invertibilities).

**Trade-offs**:

- ✅ No `WellFoundedRecursion`, no `decreasing_by`, no termination proof.
- ✅ Mathlib precedent — `Matrix.toLinearEquiv` and similar use `[Invertible A]`.
- ✅ The "field reduction" theorem
  `qdetN_inv A i j = qdetF A i j` over `[Field F]` is a one-line
  `unfold` plus `qdetN_step_eq_qdetF` (the strategic sorry from S3),
  because `[Field F] → Invertible (minorIJ A i j)` is derivable from
  `(minorIJ A i j).det ≠ 0` via `Matrix.invertibleOfDetInvertible` /
  `Matrix.invertibleOfIsUnitDet`.
- ❌ Users must construct `Invertible` witnesses *at every depth*. For
  the iterated 4×4 / 5×5 case, this chain becomes painful to write
  manually.
- ❌ Does not give a "single recurrence theorem at every n"; rather, the
  recurrence is **vacuous as stated** (rfl) and the *content* moves
  into the typeclass instance.

### Route 5B — Mutual strong recursion `qdetN ↔ qdetN_inv`

**Sketch** (closer to the canonical Gelfand–Retakh definition):

```lean
mutual
  def qdetN : (n : ℕ) → Matrix (Fin n) (Fin n) D → Fin n → Fin n → D
    | 0, _, i, _ => Fin.elim0 i
    | 1, A, _, _ => A 0 0
    | (n+2), A, i, j =>
        let M : Matrix (Fin (n+1)) (Fin (n+1)) D := minorIJ A i j
        let Minv : Matrix (Fin (n+1)) (Fin (n+1)) D := qdetN_inv (n+1) M
        qdetN_step A i j Minv
  termination_by n A i j => n

  def qdetN_inv : (n : ℕ) → Matrix (Fin n) (Fin n) D → Matrix (Fin n) (Fin n) D
    | 0, A => A
    | n+1, A => fun p q => (qdetN (n+1) A q p)⁻¹ -- homological relations
  termination_by n A => n
end
```

- **Canonical Gelfand–Retakh structure.** The homological relations
  `(A⁻¹)_{p,q} = (qdetN_{q,p})⁻¹` (where defined) close the recursion
  *internally*; the caller does not need to supply anything.
- The recurrence theorem
  `qdetN (n+2) A i j = A i j - Σ A_ij_q · (M⁻¹)_qp · A_pi_j` is a
  one-line `rfl` (it is the definition).

**Trade-offs**:

- ✅ No `Invertible` witnesses needed at the call site.
- ✅ Standard textbook (Gelfand–Retakh 1991) definition; closer to
  literature.
- ❌ Mutual recursion + `termination_by` requires Lean to see that the
  recursive call's `n` strictly decreases. The way the bodies above
  are written, `qdetN (n+1) M` is called from `qdetN (n+2) A`, so the
  Nat argument decreases — Lean accepts this *if* the dependency
  argument is the first one. **Caveat**: when `qdetN_inv n+1 A`
  calls `qdetN (n+1) A`, the *Nat* does not decrease — but it's an
  inverse-relation pun, not a recursive call. We'd need to either:
  (a) **Inline `qdetN_inv` into `qdetN`** so that only one definition
     recurses (the inverse becomes a `let`-bound matrix-valued
     expression inside `qdetN`, not its own recursive def).
  (b) Use a single recursion on `Σ n, Matrix (Fin n) (Fin n) D`
     ordered by the first projection.
  Both options work; (a) is structurally simpler.
- ❌ When `qdetN` returns `0` because some inner quasideterminant
  vanished (division by zero in `DivisionRing`), the result is
  meaningless. The user needs a global non-degeneracy hypothesis at
  every step — exactly what 5A makes explicit via the typeclass.
  In 5B, this is **hidden** until the user tries to prove anything
  about `qdetN`, at which point they need a non-vanishing hypothesis
  on all iterated minors.
- ❌ The field-reduction theorem `qdetN n A i j = qdetF n A i j`
  becomes an `n`-induction with a long chain of `minor.det ≠ 0`
  hypotheses. Each induction step needs to relate
  `(qdetN n M)⁻¹` (the entries of `qdetN_inv`) to `(M⁻¹) p q`
  (Mathlib's `nonsingInv`) — i.e. the homological relations
  ` (M⁻¹)_{p,q} = (qdetN_{q,p})⁻¹` must be proved as a separate
  theorem before consistency. This is *exactly* one of the deeper
  Gelfand–Retakh results.

### Route 5C — Hybrid: define `qdetN` via `qdetN_step`, prove invertibility separately

**Sketch**:

```lean
def qdetN : (n : ℕ) → Matrix (Fin n) (Fin n) D → Fin n → Fin n → D
  | 0, _, i, _ => Fin.elim0 i
  | 1, A, _, _ => A 0 0
  | (n+2), A, i, j =>
      qdetN_step A i j (fun p q => (qdetN (n+1) (minorIJ A i j) q p)⁻¹)
  termination_by n _ _ _ => n
```

This is **5B-with-(a)**: the inverse is *inlined* as a matrix-valued
`let` inside `qdetN`, so there is no separate `qdetN_inv` definition
and no mutual recursion. Lean sees a single structural recursion on
`n`, decreasing by 2 at each step (well-founded).

- ✅ Single recursion; no mutual; no termination_by puzzle.
- ✅ Recurrence is `rfl`.
- ✅ Carries the Gelfand–Retakh structure faithfully.
- ❌ Same hidden-degeneracy issue as 5B: when inner `qdetN` vanishes,
  the `⁻¹` is 0 (in `DivisionRing`), producing garbage.
- ❌ Consistency over a field still requires the homological-relations
  theorem
  `(M⁻¹) p q = (qdetN n M q p)⁻¹` to be proved by induction.

### Recommendation

For **S5**, ship **5A (`[Invertible]` typeclass)** because:

1. It produces the cleanest recurrence (rfl).
2. The strategic sorry from PR #18214 (`qdetN_step_eq_qdetF`) becomes
   the *only* field-reduction obligation — no auxiliary
   "homological relations" theorem needed.
3. It is what Mathlib idiomatically does for matrix inverse over
   commutative rings (`Matrix.toLinearEquiv'`).
4. The "user must build `Invertible` witnesses" complaint is
   mitigated by also shipping a single field-instance:
   `instance (priority := low) Matrix.invertibleOfDetNeZero [Field F]
       {A : Matrix (Fin n) (Fin n) F} (h : A.det ≠ 0) : Invertible A`
   (which already exists in Mathlib as
   `Matrix.invertibleOfIsUnitDet` modulo packaging).

For **S6**, then derive **5B / 5C** as a *byproduct* once `qdetN_inv`
is shown to coincide with `⅟`-typeclass witnesses — i.e. prove the
homological-relations theorem as a stand-alone result *after* the
field-reduction is done.

## 3. Discharging the S3 strategic sorry (`qdetN_step_eq_qdetF`)

This is the proof obligation at the bridge:

```lean
theorem qdetN_step_eq_qdetF {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (i j : Fin (n+1)) (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j ((minorIJ A i j)⁻¹) = qdetF A i j := sorry
```

The Mathlib API chain is well-defined. Let `M := minorIJ A i j`. Then:

1. **Unfold `qdetN_step`**: the statement becomes
   `A i j − Σ_p Σ_q A i (Fin.succAbove j q) · (M⁻¹) q p ·
                                                A (Fin.succAbove i p) j
   = A.det / M.det`.
2. **Multiply both sides by `M.det`** (using `M.det ≠ 0`):
   `(A i j) · M.det − Σ_p Σ_q A i (succAbove j q) ·
        ((M⁻¹) q p · M.det) · A (succAbove i p) j = A.det`.
3. **Apply `Matrix.inv_def`**:
   `M⁻¹ = M.det⁻¹ • adjugate M`, so
   `(M⁻¹) q p · M.det = (adjugate M) q p`.
4. **Recognize Laplace expansion**: the sum
   `Σ_p Σ_q A i (succAbove j q) · (adjugate M) q p ·
                                  A (succAbove i p) j`
   is the cofactor expansion of `A.det` along row `i` (after
   subtracting the diagonal term `(A i j) · M.det`).

The relevant Mathlib lemmas, by name and rough path:

| Lemma                                    | Path                                                                | Role                                                                |
| ---------------------------------------- | ------------------------------------------------------------------- | ------------------------------------------------------------------- |
| `Matrix.inv_def`                         | `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`                   | `M⁻¹ = M.det⁻¹ • adjugate M`                                        |
| `Matrix.adjugate_apply`                  | `Mathlib.LinearAlgebra.Matrix.Adjugate`                             | `(adjugate M) i j = det(M.updateRow j (Pi.single i 1))`             |
| `Matrix.det_succ_row`                    | `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`                    | Laplace expansion along row                                         |
| `Matrix.det_succ_row_zero`               | (same)                                                              | Specialized to row 0                                                |
| `Matrix.cramer_apply`                    | `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`                   | `cramer A b i = det (A.updateColumn i b)`                           |
| `Matrix.mulVec_cramer`                   | (same)                                                              | `A.mulVec (A.cramer b) = A.det • b`                                 |
| `Matrix.smul_adjugate`                   | `Mathlib.LinearAlgebra.Matrix.Adjugate`                             | scalar smul through adjugate                                        |
| `Matrix.adjugate_def`                    | (same)                                                              | unfold adjugate to a sum of cofactor minors                         |

The **direct strategy** (no Cramer rule, no Laplace expansion — just
algebraic manipulation):

```lean
theorem qdetN_step_eq_qdetF {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (i j : Fin (n+1)) (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j ((minorIJ A i j)⁻¹) = qdetF A i j := by
  set M := minorIJ A i j with hM
  -- qdetN_step = A i j - Σ_pq A_iq · (M⁻¹)_qp · A_pj
  -- qdetF = A.det / M.det
  -- Strategy: show qdetN_step * M.det = A.det, then div_mul_cancel.
  have key : qdetN_step A i j (M⁻¹) * M.det = A.det := by
    sorry  -- the substantive step
  have := mul_right_cancel₀ h (key.trans (qdetF_field_quotient A i j h).symm)
  exact this
```

The substantive step (the inner `sorry`) is the **Schur identity**:

> For any `(n+1)×(n+1)` matrix `A` and any deletion-indices `(i,j)`,
> if `M := minorIJ A i j` is invertible, then
> `(A i j) · M.det − Σ_pq A_iq · adjugate(M) q p · A_pj  =  A.det`.

This is **not** in Mathlib directly. The closest results are:

- `Matrix.det_fromBlocks_zero₂₁` / `Matrix.det_fromBlocks_zero₁₂`
  (block-triangular determinant formulas) in
  `Mathlib.LinearAlgebra.Matrix.Block`.
- `Matrix.det_fromBlocks_invertible` (Schur complement determinant
  identity for invertible bottom-right block) — this is the **right
  abstract result**, but it requires the matrix to be in block form
  `[[a, b], [c, d]]` with `d` invertible.

To use the block-Schur theorem, one must:

1. **Reshape `A`** via a permutation that moves row `i` and column `j`
   into positions `(0, 0)`, leaving the complementary minor as the
   bottom-right block.
2. **Track the sign** of the permutation: `Matrix.det_permute` and
   `Equiv.Perm.sign` give `det(P · A · Q) = sign(P) · sign(Q) · det A`.
3. **Apply `Matrix.det_fromBlocks_invertible`** to the reshaped matrix.

Estimated S4 size: **80–120 lines** (the reshape + sign-tracking is
the bulk). A more direct cofactor-expansion proof avoiding the
reshape may be possible but would re-derive the Schur identity from
scratch — likely longer.

## 4. The S6 Cramer derivation pathway

Once S5 ships `qdetN` (via Route 5A's `[Invertible]` typeclass),
the n×n non-commutative Cramer rule has the shape:

```lean
theorem cramer_rule_nxn_qdet
    {D : Type*} [DivisionRing D]
    {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) D)
    [∀ i, Invertible (minorIJ A i 0)]
    (b : Fin (n+1) → D) (x : Fin (n+1) → D)
    (hAx : A.mulVecᵣ x = b) :  -- right-multiplication for non-commutative
    ∀ k, x k = (qdetN_inv A k 0) ·  -- non-commutative left-divide
                  (Σ i, (M k⁻¹) i 0 · b i) := by
  sorry
```

(Note: the exact statement requires careful side-of-multiplication;
over a division ring, "Cramer" gives `x = A⁻¹ b` with the inverse
in a specific position, and the formula
`x_k = qdetN_{k,0}⁻¹ · (corrected RHS)` mirrors the commutative
`x_k = det(A_k) / det(A)` after substituting `b` into column `k`.)

The derivation chain:

1. **Show `A` is invertible.** From `[Invertible (minorIJ A i 0)]` at
   every `i` and a non-degeneracy hypothesis on `A` itself, derive
   `Invertible A` via a 2-block-Schur argument (standard
   linear-algebra fact: invertibility of the matrix is equivalent to
   invertibility of one row's worth of complementary minors plus
   non-vanishing of the corresponding qdetN entries).
2. **Express `A⁻¹` via qdetN.** The Gelfand–Retakh homological
   relations `(A⁻¹)_{j,i} = (qdetN A i j)⁻¹` (in the (i,j)-pivoted
   form) give:
   ```lean
   theorem A_inv_via_qdetN (A : Matrix (Fin (n+1)) (Fin (n+1)) D)
       [...Invertible witnesses...] (i j : Fin (n+1)) :
       (A⁻¹) j i = (qdetN A i j)⁻¹ := by sorry
   ```
   This is the non-commutative analogue of
   `Matrix.adjugate_apply`. Proof strategy: by induction on `n`,
   using the Schur formula and the inner-`qdetN_inv` witnesses.
3. **Derive Cramer.** From `Ax = b` and `A⁻¹` expressed via `qdetN`,
   solve for `x_k`:
   ```
   x_k = (A⁻¹ b)_k = Σ_i (A⁻¹)_{k,i} · b_i = Σ_i (qdetN A i k)⁻¹ · b_i
   ```
   (or the right-/left- variant, depending on multiplication
   convention).

Estimated S6 size: **150–250 lines** if the homological relations
theorem (Step 2) is the dominant work. Step 1 is largely typeclass
plumbing (~30 lines); Step 3 is a one-liner once Step 2 is done.

The recommended split is therefore:

- **S6a**: Homological relations
  `(A⁻¹) j i = (qdetN A i j)⁻¹` (~150 lines, the dense step).
- **S6b**: Cramer derivation (~30 lines, once S6a is done).

## 5. Anti-targets (do NOT attempt as S5 / S6)

- ❌ **Don't try to define `qdetN` without going through `qdetN_step`.**
  Re-defining the Schur recurrence from scratch duplicates PR #18214's
  `qdetN_step` and risks a divergent API surface. The step+inverse
  layered design is intentional.
- ❌ **Don't ship S5 via `WellFoundedRecursion` on
  `Σ n, Matrix (Fin n) (Fin n) D`.** This adds machinery to track
  the dependent-pair size measure; Lean handles `Nat`-recursion
  more cleanly via the single-recursion Route 5C, and Route 5A
  avoids recursion entirely.
- ❌ **Don't try to prove `qdetN_step_eq_qdetF` (the S3 strategic
  sorry) via term-level `Finset.sum` manipulation** without going
  through `Matrix.det_fromBlocks_invertible`. The hand expansion
  would be 200+ lines of bookkeeping; the block-Schur reshape
  is the leverage point.
- ❌ **Don't generalize to `qdetN` over a `CommRing` first.** Over
  a `CommRing` without `Invertible`, the entire `qdetN_step_eq_qdetF`
  obligation becomes vacuous (no Cramer rule to derive). The
  `DivisionRing` setting is the right level of generality for
  Gelfand–Retakh.

## 6. Honest framing — what this OBSERVE session does not establish

1. **No `lake build` performed.** All Mathlib lemma names are
   cross-referenced from `Mathlib.LinearAlgebra.Matrix.*` based on
   prevailing naming conventions and the parent files
   (`CramersRuleOQ01OQ02.lean`, `CramersRuleOQ01OQ02OQ01.lean`).
   Whoever picks up S5 should `lake env lean` -probe each lemma
   before relying on its exact signature.
2. **The block-Schur reshape (Section 3 substantive step) has not
   been written out.** It is the dominant work of S4 / S5 and
   should be the first concrete check (write the reshape
   permutation, verify signs, then apply
   `Matrix.det_fromBlocks_invertible`).
3. **The homological-relations theorem (Section 4 Step 2) is the
   hardest single result on the slug.** It may itself need to
   factor through a non-commutative `adjugate` analogue. A scout
   session should check whether any non-commutative Cramer/adjugate
   API exists in Mathlib's
   `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (which is
   currently field-only) before committing to a from-scratch
   construction.
4. **Performance and `noncomputable` annotations are unchecked.** The
   recursive `qdetN` via Route 5C definitely needs `noncomputable
   section` (already in the file). Route 5A may be computable if
   `qdetN_step` is computable, but Mathlib's
   `Matrix.nonsingInv` is `noncomputable`, so the field-reduction
   path inherits `noncomputable`.

## 7. Done When (this OBSERVE session)

- [x] Three Minv-construction routes (5A / 5B / 5C) sketched in
  Lean-level signatures.
- [x] Mathlib API chain for `qdetN_step_eq_qdetF` (the S3 strategic
  sorry) identified and cross-referenced.
- [x] S6 Cramer derivation pathway decomposed into S6a / S6b with
  size estimates.
- [x] Anti-targets enumerated (Section 5).
- [x] Honest-framing caveats listed (Section 6).
- [x] No edits to `state.md`, `knowledge.md`, `problem.md`, gallery
  files, or Lean source.

## 8. No-edit guarantee

This PR touches **only**:

```
research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/
    2026-05-12-s4-observe-minv-construction-fork.md
```

No existing file is modified. The branch `research/cramers-oq01020101-s4-observe-minv-fork-*`
is conflict-free against PR #18214's research branch
(`research/cramers-oq01020101-s3-qdetN-step-1778606287`), which only
touches `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`,
`research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/state.md`, and
`src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`.

## References

- Gelfand, I.M., Retakh, V.S. "Determinants of matrices over
  noncommutative rings." *Funct. Anal. Appl.* 25 (1991), 91–102.
- Gelfand, I., Gelfand, S., Retakh, V., Wilson, R.L.
  "Quasideterminants." *Adv. Math.* 193 (2005), 56–141.
- Mathlib: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`,
  `Mathlib.LinearAlgebra.Matrix.Adjugate`,
  `Mathlib.LinearAlgebra.Matrix.Block`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
- In-flight: PR #18214 (S3 SCAFFOLD).
- Merged: PR #18000 (S1 OBSERVE), PR #18098 (S2 ACT).
