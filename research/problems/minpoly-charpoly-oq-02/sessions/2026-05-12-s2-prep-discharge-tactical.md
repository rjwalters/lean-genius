# S2 PREP — discharge tactical plan for `diagonalizable_iff_squarefree_minpoly`

**Researcher**: researcher-6
**Date**: 2026-05-12
**Branch**: `research/minpoly-charpoly-oq-02-s2-prep-discharge-tactical-1778632101`
**Predecessor PRs**: #18276 (S1 OBSERVE Lean scaffold, merged), #18279 (S1 OBSERVE research notes, merged).
**Mode**: Doc-only PREP. No Lean changes; no JSON or markdown edits to `problem.md`, `state.md`, `knowledge.md`, or `src/data/research/problems/minpoly-charpoly-oq-02.json`.

---

## 1. Goal

`proofs/Proofs/MinpolyCharpolyOQ02.lean:117–120` carries the open sorry

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  sorry
```

S1 (researcher-9, PR #18279) noted in `state.md` that the four sub-OQs
total ~450 lines, with the load-bearing biconditional `IsSemisimple ↔
Squarefree (minpoly)` **already in-tree** at
`CayleyHamiltonMinpolyOQ01.lean:206–211`. This PREP delivers a single-PR
tactical discharge that **does not** require the sub-OQ decomposition —
the main sorry can be closed directly inside `MinpolyCharpolyOQ02.lean`
in ~80–120 Lean lines.

This is **distinct** from the sub-OQ decomposition: the four sub-OQs
(OQ-02-OQ-01 … OQ-02-OQ-04) cover the **general-field** case with
`Splits`; the discharge sketched here covers only the headline
**alg-closed** case stated in the Lean file. The two routes complement
each other.

---

## 2. Race-safety

```
$ gh pr list --repo rjwalters/lean-genius --state open \
    --search "minpoly-charpoly-oq-02 in:title"
(no open PRs targeting this slug specifically)
```

No remote branches with `minpoly-charpoly-oq-02` prefix. Two `fix(meta):
sync count drift` PRs (#18079, #18184) mention this slug in their body
but neither touches its `research/` or `proofs/Proofs/MinpolyCharpolyOQ02.lean`
content. Two sibling-OQ PRs are in flight (`oq-01` JNF and `oq-03` RCF /
RCF-OQ-01) but on different `.lean` files. This PREP is conflict-free.

---

## 3. Observation: the `CharZero` hypothesis is unnecessary

The Lean statement carries **two** typeclass hypotheses on `K`:
`IsAlgClosed K` and `CharZero K`. Inspection of the route shows that
**`CharZero` is redundant** for the alg-closed case:

1. The in-tree `isSemisimple_iff_squarefree_minpoly` requires only
   `[FiniteDimensional K V]` (line 206 of `CayleyHamiltonMinpolyOQ01.lean`).
   No char hypothesis.
2. Over an algebraically closed field, every irreducible polynomial is
   linear. So simple `K[X]`-modules (i.e., `K[X] / (p)` for `p`
   irreducible) are exactly the 1-dimensional ones (`K[X] / (X - λ) ≅
   K`). This is char-independent.
3. Diagonalizability requires a basis of 1-dim invariant submodules.
   Semisimplicity (= direct sum of simples) combined with "all simples
   are 1-dim" (= alg-closed) gives diagonalizability. Again char-free.

The `[CharZero K]` typeclass was presumably added defensively against
the inseparable-minpoly hazard, but that hazard is absent here because
`IsAlgClosed K` forces every polynomial to split into linears, hence to
be a product of distinct linear factors when squarefree.

**Recommended weakening**: drop `[CharZero K]` from the statement in
the ACT PR. Alternatively, keep it for backward compatibility and add
a comment that it is redundant; future cleanup can remove it.

(The general-field theorem `isDiagonalizable_iff_squarefree_and_splits`,
which is OQ-02-OQ-03's target, also does **not** need char-zero — the
splits hypothesis on the minpoly together with squarefreeness gives
distinct linear factors, char-free. The char-zero version is a
*specialisation*, not a precondition.)

---

## 4. Discharge route — step-by-step tactic chain

The chain has **four legs**, each a Mathlib API call or a small lemma.

```
M : Matrix n n K       (Matrix-level diagonalizability)
        ↕ (Leg 1: matrix ↔ endomorphism transport)
toLin' M : (n → K) →ₗ[K] (n → K)   (Endo-level diagonalizability)
        ↕ (Leg 2: alg-closed reduction: diag ↔ semisimple)
(toLin' M).IsSemisimple
        ↕ (Leg 3: in-tree biconditional)
Squarefree (minpoly K (toLin' M))
        ↕ (Leg 4: minpoly transport)
Squarefree (minpoly K M)
```

### Leg 1: matrix ↔ endomorphism diagonalizability

**Claim.** For `M : Matrix n n K` with `[Fintype n] [DecidableEq n]`,
`M.IsDiagonalizable ↔ ∃ B : Basis n K (n → K), ∀ i, ∃ μ : K, toLin' M (B i) = μ • B i`.

In words: the matrix-level "similar to a diagonal" predicate (def in
`MinpolyCharpolyOQ02.lean:105`) is equivalent to the endomorphism
having an eigenbasis. This is a *concrete unfolding*: the invertible
similarity matrix `P` is the change-of-basis from the standard basis
to the eigenbasis.

**Mathlib hookups**:
- `Matrix.toLin'` (`Mathlib.LinearAlgebra.Matrix.ToLin`).
- `Basis.equivFun`, `Matrix.diagonal_toLin`.
- `IsDiag M ↔ ∀ i j, i ≠ j → M i j = 0` (`Matrix.isDiag_iff`).
- Conversion `P⁻¹ * M * P = D` (diagonal) gives `Mᵏ = P D P⁻¹` etc.; the
  eigenvalue at position `i` is `D i i`, the eigenvector is `P i j`-th
  column of `P`.

**Estimated proof length**: ~30–40 Lean lines as a stand-alone lemma
`Matrix.isDiagonalizable_iff_hasEigenbasis_toLin'` (new in this file).

### Leg 2: alg-closed reduction

**Claim.** Under `[IsAlgClosed K]`, for `f : Module.End K V` with
`[FiniteDimensional K V]`,
`(∃ B : Basis ι K V, ∀ i, ∃ μ, f (B i) = μ • B i) ↔ f.IsSemisimple`.

Forward (`→`): a basis of eigenvectors gives a direct-sum decomposition
into 1-dim simple submodules. Each `K • B i` is `f`-invariant (because
`f (B i) = μ • B i ∈ K • B i`) and simple (1-dim). The total direct sum
is `V` (because `B` is a basis). So `f` is semisimple.

Reverse (`←`): semisimple means `V = ⨁ Sⱼ` for `f`-invariant simple
`Sⱼ`. Over alg-closed `K`, every simple `f`-invariant submodule is
1-dim (because as a `K[X]`-module, simple = `K[X]/(p)` for `p`
irreducible, and over alg-closed `p` is linear, hence
`K[X]/(p) ≅ K`). Pick a basis vector `bⱼ ∈ Sⱼ` for each `j`; the
collection `{bⱼ}` is a basis of `V`, and each is an eigenvector.

**Mathlib hookups**:
- `Module.End.IsSemisimple` definition (`Mathlib.LinearAlgebra.Semisimple`).
- `IsSemisimple.module_End_iff_finsum_eigenspace` or the
  eigenspace-decomposition lemma `Module.End.iSup_eigenspace_eq_top_of_isSemisimple`
  (name to confirm at v4.26.0).
- `IsAlgClosed.splits_codomain` (every polynomial splits over an alg-closed
  field) for the "all irreducibles are linear" step.

**Estimated proof length**: ~30–40 Lean lines. **Highest risk leg** —
the exact Mathlib lemma packaging "alg-closed + semisimple ⇒ eigenbasis"
may not exist verbatim; the proof may need to expand the direct-sum
decomposition manually. See §6 Snag 2.

### Leg 3: in-tree biconditional

**Claim.** `(toLin' M).IsSemisimple ↔ Squarefree (minpoly K (toLin' M))`.

**Mathlib hookup**: directly `CayleyHamiltonMinpolyOQ01.isSemisimple_iff_squarefree_minpoly`
applied to `toLin' M` with `V := n → K` and the auto-derived
`FiniteDimensional K (n → K)` instance.

**Estimated proof length**: 1 line (`exact isSemisimple_iff_squarefree_minpoly`).

### Leg 4: minpoly transport

**Claim.** `minpoly K M = minpoly K (toLin' M)`.

**Mathlib hookup**:
- `Matrix.minpoly_toLin'` (Mathlib core, file `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`).
  Direction: `minpoly K (toLin' M) = minpoly K M`. Then
  `Squarefree (minpoly K (toLin' M)) ↔ Squarefree (minpoly K M)` by
  `Iff.rfl` or `simp [Matrix.minpoly_toLin']`.

**Estimated proof length**: 1 line (`simp [Matrix.minpoly_toLin']`).

---

## 5. Composite tactic chain (~80–120 lines total)

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] (M : Matrix n n K) :   -- CharZero dropped
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  -- Leg 1: matrix ↔ endomorphism
  rw [isDiagonalizable_iff_hasEigenbasis_toLin' M]
  -- Leg 2: alg-closed eigenbasis ↔ semisimple
  rw [Module.End.hasEigenbasis_iff_isSemisimple_of_isAlgClosed]   -- LOCAL helper
  -- Leg 3: in-tree biconditional
  rw [isSemisimple_iff_squarefree_minpoly]
  -- Leg 4: minpoly transport
  rw [Matrix.minpoly_toLin']
```

Plus two new helper lemmas in the same file:

1. `Matrix.isDiagonalizable_iff_hasEigenbasis_toLin'` (~35 lines) — Leg 1.
2. `Module.End.hasEigenbasis_iff_isSemisimple_of_isAlgClosed` (~40 lines) — Leg 2.

**Total ACT envelope: ~80 Lean lines**, replacing the single `sorry`.
If Snag 2 (§6) forces manual eigenspace-decomposition expansion, the
envelope grows to ~120 lines.

---

## 6. Mathlib-API snags

### Snag 1: lemma name `Matrix.minpoly_toLin'` vs. `LinearMap.toMatrix_minpoly` vs. ...

At v4.26.0 the exact name of "minpoly of the matrix equals minpoly of
its `toLin'` representation" may be:

- `Matrix.minpoly_toLin'`
- `LinearMap.minpoly_toMatrix'`
- `Matrix.toLin'.minpoly_eq_minpoly` (less likely)

**Probing command**:
```bash
grep -rn "minpoly.*toLin'\|minpoly.*toMatrix" \
  ~/.elan/toolchains/*/lib/lean4-mathlib 2>/dev/null
```
Confirm at ACT time. Fallback: prove it locally in ~10 lines via the
characterising property of `minpoly` (it is the smallest-degree monic
annihilator, and `toLin'` preserves polynomial evaluation).

### Snag 2: `Module.End.hasEigenbasis_iff_isSemisimple_of_isAlgClosed` is a local helper

This is the biggest unknown. Mathlib at v4.26.0 may or may not contain
the bundled form. Likely candidates to search:

- `Module.End.isSemisimple_iff_isDiagonalisable` (no — diagonalisable is
  not quite the same as eigenbasis at the LinearMap level if the field
  is not alg-closed).
- `IsSemisimple.module_End_iff_iSup_eigenspaces_top` or
  `Module.End.iSup_eigenspace_eq_top_of_isSemisimple` (when the field
  is alg-closed — this is the operator-theoretic content).
- `Module.End.IsSemisimple.directSum` (gives the direct-sum decomp
  into simples) + a 1-dimensional refinement under alg-closed.

If no single packaged lemma exists, the local helper expands as:

```lean
lemma Module.End.hasEigenbasis_iff_isSemisimple_of_isAlgClosed
    [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : Module.End K V} :
    (∃ B : Basis (Fin (Module.finrank K V)) K V, ∀ i, ∃ μ, f (B i) = μ • B i)
      ↔ f.IsSemisimple := by
  refine ⟨fun ⟨B, hB⟩ => ?_, fun hf => ?_⟩
  · -- forward: eigenbasis ⇒ semisimple
    -- Each `K • B i` is a 1-dim f-invariant simple. Their direct sum is V.
    sorry  -- ~15 lines
  · -- reverse: semisimple ⇒ eigenbasis (alg-closed)
    -- Decompose V into f-invariant simples; each is K[X]/(p) for p
    -- irreducible. Over alg-closed, deg p = 1, so each simple is 1-dim.
    -- Pick a generator of each summand to assemble the eigenbasis.
    sorry  -- ~20 lines
```

**Risk level**: medium. Both `sorry` are routine but each involves a
mini-construction. Plausibly Aristotle-fodder if the imports are right.

### Snag 3: `Basis (Fin (Module.finrank K V)) K V` vs. `Basis n K (n → K)`

In Leg 1 (matrix to endo), the natural eigenbasis index type is `n`
(the matrix's row index). In Leg 2 (endo to semisimple), the natural
index type is `Fin (Module.finrank K V)`. There is a canonical equiv
`n ≃ Fin (Fintype.card n)` and `Module.finrank K (n → K) = Fintype.card n`,
so the index transport is `Basis.reindex` + `Fintype.equivFin`. Adds ~5
lines of boilerplate. Documented as a minor snag.

---

## 7. Numeric falsification

The Lean file `MinpolyCharpolyOQ02.lean` has no `decide`-closed numeric
sanity check (unlike `EhrhartCubeProvenOQ03.lean`'s 4 numeric tests).
A small confidence-building addition during ACT would be a `2×2`
diagonal example:

```lean
example : (Matrix.diagonal ![1, 2] : Matrix (Fin 2) (Fin 2) ℝ).IsDiagonalizable :=
  Matrix.IsDiagonalizable.of_isDiag (Matrix.isDiag_diagonal _)
```

The corresponding minpoly is `(X − 1)(X − 2)` which is squarefree, so
the biconditional's forward direction is trivially witnessed by this
example. Adding 2-3 such tests would anchor the theorem statement
without inflating the line count.

**Off-the-shelf counterexample to the broken claim** (already in
knowledge.md): the `[0, -1; 1, 0]` matrix over `ℝ` shows that
`Squarefree (minpoly ℝ M) → M.IsDiagonalizable` **fails** without
`IsAlgClosed ℝ` — and indeed `ℝ` is not alg-closed. So the `[IsAlgClosed K]`
hypothesis is load-bearing. The proof in §5 uses `IsAlgClosed K`
exactly at Leg 2's reverse direction.

---

## 8. ACT-readiness checklist

When picking up S2 in an ACT:

1. Branch off **main** with name
   `research/minpoly-charpoly-oq-02-s2-act-discharge-<ts>`.
2. Open `proofs/Proofs/MinpolyCharpolyOQ02.lean`. Add the two helper
   lemmas (Leg 1 + Leg 2) **before** line 117. Then replace `sorry` on
   line 120 with the four-step `rw` chain in §5.
3. **Decision point**: drop `[CharZero K]` from the statement (§3)?
   Recommended yes; this is a free strengthening.
4. **Build inside Docker**:
   `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.
   Expected: 8–12 min fresh, 4–6 min with cache.
5. If Snag 1 (`Matrix.minpoly_toLin'` name) misfires: try the three
   candidate names from §6, or define a 10-line local helper.
6. If Snag 2 (eigenbasis ↔ semisimple) is too painful: ship Leg 1, Leg 3,
   Leg 4 as proved lemmas and leave Leg 2 as a smaller, well-stated
   sorry — the partial deliverable is still a strict improvement (one
   well-defined Mathlib gap vs. the whole-theorem sorry).
7. Bump `src/data/proofs/minpoly-charpoly/meta.json` if the gallery
   tracks `oq-02` sorries (likely yes given the OQ-01 / OQ-03 family
   structure).
8. PR title:
   `research(minpoly-charpoly-oq-02): S2 ACT — discharge diagonalizable_iff_squarefree_minpoly via toLin' + isSemisimple (build verified)`.

---

## 9. Comparison to the sub-OQ decomposition in `state.md`

`state.md` proposes a 4-sub-OQ decomposition totalling ~450 lines:

| Sub-OQ           | Content                                                            | LOC est. |
| ---------------- | ------------------------------------------------------------------ | -------- |
| OQ-02-OQ-01      | `Matrix.IsDiagonalizable` predicate + API                          | ~80      |
| OQ-02-OQ-02      | matrix ↔ endomorphism bridge                                       | ~120     |
| OQ-02-OQ-03      | universal characterization (squarefree ∧ splits)                   | ~180     |
| OQ-02-OQ-04      | algebraically-closed corollary                                     | ~40      |

This PREP's tactical discharge **covers the alg-closed case directly in
80–120 lines** without sub-OQs. Tradeoff:

- **Sub-OQ route**: lands the universal (alg-closed-free) theorem with
  full Mathlib-friendly factoring. ~5× the LOC, ~4× the PRs.
- **Tactical route**: lands only the alg-closed corollary. 1 PR, ~80–120
  lines. Does **not** prove OQ-02-OQ-03's general form.

**Recommendation**: ship the tactical route **first** (this PREP's
target). Its deliverable is the headline theorem currently sorry-marked
in the file. Then iterate towards OQ-02-OQ-03's universal form in
follow-up sessions.

---

## 10. Cross-references

- **Predecessor PRs**: #18276 (Lean scaffold), #18279 (research notes).
- **Sibling slugs**:
  - `minpoly-charpoly-oq-01` (JNF): merged S1 OBSERVE #18045, S2 ACT #18106,
    S3 ACT #18134. Active.
  - `minpoly-charpoly-oq-03` (RCF): merged S3-S5 chain. Active.
  - `minpoly-charpoly-oq-03-oq-01` (F[X]-module structure): merged #17995.
- **In-tree biconditional**: `CayleyHamiltonMinpolyOQ01.lean:206–211`
  (`isSemisimple_iff_squarefree_minpoly`).
- **Mathlib v4.26.0 main APIs needed**:
  - `Matrix.toLin'`, `Matrix.minpoly_toLin'`.
  - `Module.End.IsSemisimple`.
  - `IsAlgClosed.splits_codomain`.
  - `Basis.reindex`, `Fintype.equivFin`.

---

## 11. What this PR does NOT do

- No edit to `problem.md`, `state.md`, `knowledge.md`.
- No edit to `src/data/research/problems/minpoly-charpoly-oq-02.json`.
- No edit to any `.lean` file (no build needed; sorry count unchanged at 1).
- No `Matrix.IsDiagonalizable` API changes (the predicate at line 105
  stays as-is).
- No claim that the sub-OQ decomposition in `state.md` is wrong — only
  that the **headline theorem** in the file can be discharged faster.
