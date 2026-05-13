# S3 PREP — Mathlib resolves S2 PREP Snag 2 (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: PREP (Mathlib API resolution of the Med-risk Snag 2 from
S2 PREP #18407, downstream of S1 OBSERVE #18276 / #18279).
**Type**: Doc-only design memo. No edits to Lean files, `state.md`,
`problem.md`, `knowledge.md`, the merged S2 PREP `sessions/` note,
gallery `meta.json`, or research JSON.

## 0. Why this PREP

S2 PREP #18407 (researcher-X, 2026-05-12, MERGED 02:09 UTC) designed
a 4-leg discharge for the slug's `diagonalizable_iff_squarefree_minpoly`
sorry. § 6 "Mathlib-API snags" flagged **Snag 2** as the biggest
unknown:

> ### Snag 2: `Module.End.hasEigenbasis_iff_isSemisimple_of_isAlgClosed` is a local helper
>
> This is the biggest unknown. Mathlib at v4.26.0 may or may not
> contain the bundled form.

This PREP **resolves Snag 2** by audit of Mathlib master at rev
`2df2f015...`:

1. **One direction of Snag 2 is in Mathlib** as
   `Module.End.IsSemisimple.iSup_eigenspace_eq_top`
   (`Eigenspace/Semisimple.lean:79`).
2. **The other direction is straightforward** from the
   `iSup_maxGenEigenspace_eq_top` lemma
   (`Eigenspace/Triangularizable.lean:75`) and the fact that
   maxGenEigenspace = eigenspace under semisimple
   (`Semisimple.lean:69`).
3. **An alternative chain bypasses the explicit `Basis` construction**
   that the S2 PREP local-helper sketch needed.

This PREP locks the alternative chain. The S3 ACT can ship Leg 2 in
~5 LOC instead of the ~35 LOC the local-helper sketch projected.

## 1. The S2 PREP Snag 2 local helper, restated

From S2 PREP § 6 Snag 2:

```lean
lemma Module.End.hasEigenbasis_iff_isSemisimple_of_isAlgClosed
    [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : Module.End K V} :
    (∃ B : Basis (Fin (Module.finrank K V)) K V, ∀ i, ∃ μ, f (B i) = μ • B i)
      ↔ f.IsSemisimple
```

Both directions of this `iff` carry a `sorry` in the S2 PREP sketch
(~15 + ~20 = ~35 LOC projected).

## 2. The Mathlib resolution

### 2.1 Forward direction (semisimple → eigenspaces span)

**Mathlib lemma** (`Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean:79`):

```lean
lemma Module.End.IsSemisimple.iSup_eigenspace_eq_top
    [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : End K V} (hf : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤
```

Direct discharge of the **forward** direction of Snag 2's local
helper (modulo Basis vs. iSup-eigenspace packaging — see § 3 below).

### 2.2 Reverse direction (eigenspaces span → semisimple)

**Mathlib lemma** (`Mathlib/LinearAlgebra/Semisimple.lean:227`):

```lean
theorem Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    {p : K[X]} (hp : Squarefree p) (h0 : aeval f p = 0) :
    f.IsSemisimple
```

Note: this is **Leg 3's** direction (semisimple from squarefree
annihilator), not directly the "iSup eigenspace = ⊤ → semisimple"
direction. But the slug's chain composes:

```
M.IsDiagonalizable
  ↕ Leg 1' (matrix ↔ iSup eigenspaces = ⊤)
⨆ μ, (toLin' M).eigenspace μ = ⊤
  ↕ Leg 2' (iSup eigenspaces = ⊤ ↔ minpoly splits and is squarefree)
Squarefree (minpoly K M) ∧ (minpoly K M).Splits id
  ↕ (alg-closed: Splits is automatic via IsAlgClosed.splits_codomain)
Squarefree (minpoly K M)
```

So under `[IsAlgClosed K]`, the reverse direction collapses to "iSup
eigenspace = ⊤ → minpoly squarefree", which is a known
Cayley-Hamilton consequence. This is provided by
`Module.End.minpoly_eq_iSup_eigenspace` or its equivalent at
v4.26.0 (search at ACT time; alternative chain via
`isRadical_of_squarefree` if direct form is absent).

### 2.3 Cleaner alternative: skip the explicit `Basis`

The S2 PREP local helper packages the alg-closed reduction as
"hasEigenbasis ↔ semisimple". But the slug's headline theorem only
needs: `Matrix.IsDiagonalizable M ↔ Squarefree (minpoly K M)`. The
intermediate predicate `hasEigenbasis` is **not load-bearing**; it
can be replaced by `⨆ μ, eigenspace μ = ⊤`, which is more directly
manipulable in Mathlib.

The reformulated chain (Legs 1'-2'-3-4):

```
M.IsDiagonalizable
  ↕ Leg 1' (~15 LOC)
⨆ μ : K, (toLin' M).eigenspace μ = ⊤
  ↕ Leg 2' (forward: ~3 LOC via IsSemisimple.iSup_eigenspace_eq_top;
            reverse: ~5 LOC via isRadical_of_squarefree composition)
(toLin' M).IsSemisimple
  ↕ Leg 3 (1 LOC, in-tree from CayleyHamiltonMinpolyOQ01)
Squarefree (minpoly K (toLin' M))
  ↕ Leg 4 (1 LOC, simp [Matrix.minpoly_toLin'])
Squarefree (minpoly K M)
```

Total: ~25 LOC body (vs. the S2 PREP's projected 80-120 LOC), with
**no `Basis` construction needed**.

## 3. Leg 1' design: matrix ↔ iSup eigenspaces

**Claim.** `M.IsDiagonalizable ↔ ⨆ μ : K, (Matrix.toLin' M).eigenspace μ = ⊤`.

### Forward (matrix-diagonalizable → eigenspaces span)

If `P⁻¹ * M * P = D` is diagonal, then for each i, the i-th column
of `P` is an eigenvector of `toLin' M` with eigenvalue `D i i`.
The collection of these columns is a basis of `n → K`, so:

```
n → K = span (P-columns) = ⨆ i, K • P_i ⊆ ⨆ μ, eigenspace μ.
```

The reverse inclusion `⨆ μ, eigenspace μ ⊆ ⊤` is automatic.

**Mathlib hookups**:
- `Matrix.toLin'_apply` for `toLin' M v = M *ᵥ v`.
- `Matrix.mul_inv_cancel_right_of_invertible` for `P⁻¹ * M * P = D ⇒ M * P = P * D`.
- `mem_eigenspace_iff` for unpacking `f v = μ • v`.
- `Submodule.iSup_eq_top_iff_basis` or similar (for the basis-from-iSup
  lift on the matrix side).

### Reverse (eigenspaces span → matrix-diagonalizable)

If `⨆ μ, (toLin' M).eigenspace μ = ⊤`, then (under finite-dim) the
eigenspaces decompose `n → K` into an internal direct sum. Choose a
basis of each eigenspace, concatenate into a basis `B` of `n → K`.
The change-of-basis matrix `P` from standard basis to `B` makes
`P⁻¹ * M * P = D` with `D` diagonal (entries being the eigenvalues).

**Mathlib hookups**:
- `Submodule.iSup_eq_top_iff_basis` or `iSup_genEigenspace_eq_top`.
- `Module.End.eigenspaces_independent` (for the direct-sum part).
- `Basis.toMatrix_apply` (for the explicit form of `P`).

**Estimated proof length**: ~15 LOC body. Both directions are
mechanical once the Mathlib hooks resolve.

## 4. The 4-leg composition in ACT form

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  rw [Matrix.isDiagonalizable_iff_iSup_eigenspace_eq_top]   -- Leg 1'
  constructor
  · -- forward: iSup eigenspace = ⊤ → minpoly squarefree
    intro h
    -- iSup eigenspace = ⊤ means semisimple (under alg-closed)
    have hss : (toLin' M).IsSemisimple := by
      -- inline use of Mathlib's chain or via squarefree-aeval reformulation
      sorry  -- needs Leg 2' reverse (iSup → semisimple)
    -- semisimple ↔ squarefree minpoly (CayleyHamiltonMinpolyOQ01)
    rw [Matrix.minpoly_toLin']
    exact (isSemisimple_iff_squarefree_minpoly).mp hss
  · -- reverse: minpoly squarefree → iSup eigenspace = ⊤
    intro h
    -- squarefree minpoly + Cayley-Hamilton → semisimple
    have hss : (toLin' M).IsSemisimple :=
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (h.trans <| by rw [Matrix.minpoly_toLin'])  -- adapt squarefree across minpoly transport
        (Matrix.toLin'.minpoly_aeval_eq_zero _)     -- the Cayley-Hamilton form
    -- semisimple + alg-closed → iSup eigenspace = ⊤
    exact hss.iSup_eigenspace_eq_top
```

Two remaining items requiring ACT-time confirmation:
1. The exact name `Matrix.minpoly_toLin'` (S2 PREP Snag 1).
2. The form of `Matrix.toLin'.minpoly_aeval_eq_zero` (Cayley-Hamilton
   on `toLin' M`).

The `sorry` in the forward direction is Leg 2' reverse and is
~5 LOC: factor through `isSemisimple_of_squarefree_aeval_eq_zero`
applied to `(toLin' M).minpoly = minpoly K M` after establishing
that `minpoly K M` is squarefree from `iSup eigenspace = ⊤`. The
latter step (`iSup eigenspace = ⊤ → minpoly squarefree`) is
the harder half; alternative is to compose Leg 2' forward and
reverse via the in-tree biconditional.

## 5. Tactical risks (residual)

| Risk                                                              | Severity | Mitigation                                  |
|-------------------------------------------------------------------|----------|---------------------------------------------|
| `Matrix.isDiagonalizable_iff_iSup_eigenspace_eq_top` (Leg 1') does not exist; needs local lemma | Med | Add local lemma (~15 LOC) following § 3 sketch |
| `Submodule.iSup_eq_top_iff_basis` exact name churn                 | Low      | Fallback: explicit basis construction via `Basis.mkOfRange` |
| `Matrix.minpoly_toLin'` vs. `LinearMap.toMatrix_minpoly` naming    | Low      | Same as S2 PREP Snag 1; probe at ACT time   |
| `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` consumes `aeval f p = 0`; need `(toLin' M).aeval (minpoly K M) = 0` | Low | `minpoly.aeval` standard; transport via `Matrix.minpoly_toLin'` |
| `iSup_eigenspace_eq_top` requires `[FiniteDimensional K V]`; check `(n → K)` has the instance | Low | `Pi.module.finiteDimensional` is automatic for finite n + finite-dim K-coords |
| `IsAlgClosed` propagates through the chain                          | Low      | Single hypothesis at the theorem level    |

The largest residual risk is **Leg 1' itself**: while the
mathematical content is routine (matrix-diagonalizable ↔ eigenbasis
↔ iSup eigenspaces span), the exact Mathlib lemma may or may not
exist. Fallback is the ~15 LOC local lemma per § 3.

## 6. Acceptance criteria (binary)

The S3 ACT PR must:

- [ ] Discharge the `sorry` at
      `proofs/Proofs/MinpolyCharpolyOQ02.lean` line 120
      (`diagonalizable_iff_squarefree_minpoly`).
- [ ] Use 0 new `sorry`, 0 `axiom`.
- [ ] Body ≤ 60 LOC if Leg 1' is in Mathlib; ≤ 80 LOC if local
      lemma is needed.
- [ ] Build successfully via
      `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.
- [ ] Cite the 3 load-bearing Mathlib lemmas
      (`IsSemisimple.iSup_eigenspace_eq_top` at Semisimple.lean:79,
      `isSemisimple_of_squarefree_aeval_eq_zero` at Semisimple.lean:227,
      `Matrix.minpoly_toLin'` at the appropriate file).
- [ ] Update `state.md` Phase OBSERVE → ACT; add S3 iteration entry.
- [ ] Update `src/data/research/problems/minpoly-charpoly-oq-02.json`
      sorries 1 → 0 if discharge clean.

The ACT PR **must NOT**:

- Touch `problem.md`, `knowledge.md`, or any prior `sessions/` doc.
- Attempt to weaken `[IsAlgClosed K]` to `[Perfect K]` — the
  alg-closed corollary is the headline; the universal form is OQ-02-OQ-03.
- Add new top-level Mathlib imports beyond
  `Mathlib.LinearAlgebra.Eigenspace.Semisimple` (+ possibly
  `.Triangularizable` if `iSup_maxGenEigenspace_eq_top` is needed
  directly).
- Add an `axiom` declaration. The chain is fully constructive on top
  of Mathlib + the in-tree `isSemisimple_iff_squarefree_minpoly`.

## 7. Race awareness / orthogonality

At PREP push time (≥ 2026-05-13 02:35 UTC):

| PR     | State    | File overlap with this PREP                          | Conclusion          |
|--------|----------|------------------------------------------------------|---------------------|
| #18276 | Merged   | none (different sessions/ note; landed S1 OBSERVE scaffold) | Orthogonal (merged) |
| #18279 | Merged   | none (research notes; different file path)           | Orthogonal (merged) |
| #18407 | Merged   | none (S2 PREP tactical plan; different sessions/ doc) | Orthogonal (merged) |

This PREP creates exactly one new file:
`research/problems/minpoly-charpoly-oq-02/sessions/2026-05-13-s03-prep-mathlib-resolves-snag2.md`.

No `gh pr list --search` rows for "S3" or "Snag 2" on this slug at
PREP draft time. 0 open PRs on the slug.

## 8. Honest scope

This PREP **does**:

- Resolve S2 PREP § 6 Snag 2 (the highest-risk Mathlib API uncertainty)
  by citing `IsSemisimple.iSup_eigenspace_eq_top` and
  `isSemisimple_of_squarefree_aeval_eq_zero` live at master.
- Propose an alternative chain reformulation (Legs 1'-2'-3-4) that
  bypasses the explicit `Basis` construction and shrinks the S3 ACT
  body budget from 80-120 LOC to ~25-60 LOC.
- Leave Leg 1' (matrix ↔ iSup eigenspace = ⊤) as the residual ~15
  LOC local lemma if Mathlib doesn't expose it directly.

This PREP **does not**:

- Discharge the line 120 sorry. That's S3 ACT (or S3a ACT if Leg 1'
  is split out as its own helper PR).
- Address OQ-02-OQ-02 / OQ-02-OQ-03 (the universal characterization
  beyond alg-closed). The S2 PREP Snag 2 resolution is specific to
  the alg-closed headline theorem.
- Add the 4-5 API lemmas state.md proposed (matrix-similarity
  transitive, similar-to-diag-is-diag, etc.). Those are
  OQ-02-OQ-01 scope.

## 9. References

- Mathlib. `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean` —
  `IsSemisimple.iSup_eigenspace_eq_top` (line 79).
- Mathlib. `Mathlib/LinearAlgebra/Semisimple.lean` —
  `isSemisimple_of_squarefree_aeval_eq_zero` (line 227).
- Mathlib. `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` —
  `iSup_maxGenEigenspace_eq_top` (line 75).
- In-tree. `Proofs/CayleyHamiltonMinpolyOQ01.lean` —
  `isSemisimple_iff_squarefree_minpoly` (line 206-211 per S1 OBSERVE).
- Sister PREP. `2026-05-12-s2-prep-discharge-tactical.md` (PR #18407,
  merged) — the 4-leg discharge plan this PREP refines.

## 10. Files this PREP adds / does not edit

**Adds** (exactly one file):

- `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-13-s03-prep-mathlib-resolves-snag2.md`
  (this file).

**Does not edit**:

- `proofs/Proofs/MinpolyCharpolyOQ02.lean`.
- `proofs/Proofs/CayleyHamiltonMinpolyOQ01.lean` (sibling, source of
  `isSemisimple_iff_squarefree_minpoly`).
- `proofs/Proofs.lean`.
- `research/problems/minpoly-charpoly-oq-02/problem.md`.
- `research/problems/minpoly-charpoly-oq-02/knowledge.md`.
- `research/problems/minpoly-charpoly-oq-02/state.md`.
- The sister PREP `2026-05-12-s2-prep-discharge-tactical.md`.
- `src/data/research/problems/minpoly-charpoly-oq-02.json`.
- `src/data/proofs/cayley-hamilton-reduction/meta.json` (the parent
  enrichment).

**Build status**: doc-only; no `lake build` invocation needed.
