# Knowledge Base: euler-polyhedral-formula-oq-02-oq-02

Connect the discrete/smooth Gauss-Bonnet theorems to the Chern-Gauss-Bonnet
theorem in higher dimensions.

---

## Problem Understanding

The discrete Gauss-Bonnet (parent OQ-02) gives Σ_v δ(v) = 2πχ for polyhedral
surfaces; the smooth 2D version (sibling OQ-02-OQ-01) gives ∫_M K dA = 2πχ. The
full generalization is the **Chern-Gauss-Bonnet theorem**: for a closed oriented
Riemannian manifold of even dimension 2n,

    ∫_M Pf(Ω) = (2π)^n · χ(M),   equivalently   ∫_M Pf(Ω/2π) = χ(M),

where Ω is the curvature form and Pf its Pfaffian (Chern 1944-45; Allendoerfer-Weil
1943). For n=1, Pf of the 2×2 curvature is K·(area form), recovering classical
Gauss-Bonnet.

---

## Insights

- **Mathlib gap**: v4.26.0 has no Pfaffian, no characteristic-form integration over
  manifolds, and no manifold Euler characteristic. The C-G-B identity must be
  structure-encoded → entry is `axiomatized` (badge `axiom`), matching the sibling
  OQ-02-OQ-01 pattern.
- **Verified (0-axiom) content surrounding the assumption**:
  - χ(S^m) = 1 + (-1)^m: 2 in even dim, 0 in odd dim — the parity that makes the
    Pfaffian (an even-dim invariant) the right integrand.
  - (2π)^n normalization: positivity + multiplicativity (2π)^{m+n}=(2π)^m(2π)^n
    (drives product multiplicativity).
  - 2×2 Pfaffian identity Pf² = det: the algebraic mechanism behind the n=1 reduction.
- **Structure CGBManifold** (halfDim, chi, totalPfaffian, field chern_gauss_bonnet)
  yields: even-dimensionality, normalized ∫Pf/(2π)^n = χ, χ=0 ⇒ ∫Pf=0, sign matching,
  recovery of 2D Gauss-Bonnet at n=1, and integrality of the Euler number.
- **Functorial constructions**: sphereCGB (χ=2), prodCGB (χ multiplies; ∫Pf multiplies),
  torusCGB (χ=0). ClosedOddManifold records χ=0 (Poincaré duality), realized by S^{2k+1}.

## Result

`Proofs/EulerPolyhedralOQ02OQ02.lean`: 37 theorems, 8 defs, 2 structures, 0 sorries,
0 axiom declarations, 2 structure-encoded assumptions
(CGBManifold.chern_gauss_bonnet, ClosedOddManifold.chi_zero). Offline-verified
EXIT 0; `#print axioms` shows only propext/Classical.choice/Quot.sound (no sorryAx,
no Lean.ofReduceBool). Gallery entry created (meta.json + annotations.json, 7
annotations resolve cleanly).

---

## Dead Ends

- Attempting a fully `verified` (0-assumption) entry is impossible: the Pfaffian
  curvature integral and manifold χ are not in Mathlib. The honest status is
  `axiomatized` with the geometric identity as a single structure field.

---

## Session 2026-07-08 (researcher-6) — Part X: connected sums

**Mode:** REVISIT (mature axiomatized entry; add within the structure framework)
**Outcome:** progress (1 new construction + 7 theorems)

### What I Did
Added `connectedSumCGB` — the connected sum `M # N` of two same-dimensional CGB
manifolds — as a new functorial construction beside `prodCGB`:
- `connectedSumCGB M N (h : M.halfDim = N.halfDim)`: χ = M.chi + N.chi − 2 and
  totalPfaffian = M.tp + N.tp − 2·cgbConst n (curvature removed with the two glued
  disks). The `chern_gauss_bonnet` field is discharged from M's and N's identities
  since one normalization constant governs all three pieces.
- `connectedSumCGB_dim/chi/totalPfaffian` (rfl accessors).
- `connectedSum_sphere_chi`, `connectedSum_sphere_totalPfaffian`: **S^{2n} is the
  connected-sum identity** (both χ and ∫Pf neutral) — connected sum is a monoid,
  χ − 2 the induced additive homomorphism to ℤ.
- `genus_two_surface_chi` (= −2) and `genus_two_surface_totalPfaffian` (= −4π):
  T² # T² is the genus-2 surface, matching χ(Σ_g) = 2 − 2g and ∫K dA = 2π·χ = −4π.

### Verification
Built clean: `Proofs.EulerPolyhedralOQ02OQ02` (7743 jobs). File now 426 lines,
44 theorems, 9 defs, 2 structures, 0 sorries, 0 axiom declarations. Status stays
**axiomatized** (the 2 structure-encoded assumptions CGBManifold.chern_gauss_bonnet
and ClosedOddManifold.chi_zero are unchanged; the new construction adds no
assumptions). Build hit the recurring shared-volume corruption (exit-135, line-less)
×2 → cleared by `docker-build.sh --repair-cache` at load 0 then a clean rebuild.

### Frontier
Core still BLOCKED on Mathlib v4.26 gaps (no Pfaffian, no characteristic-form
integration over manifolds, no manifold Euler characteristic). The connected-sum,
product, and sphere/torus/odd constructions now give a fairly complete calculus of
the *structure-encoded* Euler-characteristic invariant; further elementary progress
is exhausted until Mathlib gains the differential-geometry machinery.

### Files Modified
- `proofs/Proofs/EulerPolyhedralOQ02OQ02.lean` (Part X, +~70 lines, verified)
- `src/data/proofs/euler-polyhedral-formula-oq-02-oq-02/meta.json` (counts + contribution)
- `src/data/research/problems/euler-polyhedral-formula-oq-02-oq-02.json` (counts + knowledge)

## Session 2026-07-09 (researcher-2) — Part XI: genus-g surface in closed form [VERIFIED]

**Mode**: REVISIT (mature axiomatized entry). **Outcome**: PROGRESS — genuine
generalization, not scaffolding: the file previously had only the *genus-2* surface
(`T²#T²`); this adds the full family.

### Shipped (Docker build EXIT 0, ✔ 7743 jobs, 0 axioms / 0 sorries added)
- `genusSurfaceCGB g` — the genus-`g` closed orientable surface as a `CGBManifold`:
  `halfDim = 1`, `χ = 2 − 2g`, `totalPfaffian = (2 − 2g)·(2π)`. One closed form for the
  entire family (sphere `g=0`, torus `g=1`, genus-2 `g=2`, …).
- `genusSurfaceCGB_chi` (`χ = 2−2g`), `genusSurfaceCGB_totalPfaffian`
  (**Gauss-Bonnet** `∫Pf = 2π(2−2g)`), `_halfDim`, `_dim`.
- `genusSurface_{zero,one,two}_chi` — sphere χ=2, torus χ=0, genus-2 χ=−2 (matches the
  existing `genus_two_surface_chi`).
- `genusSurface_succ_chi` — **handle attachment drops χ by 2**: `χ(Σ_{g+1}) = χ(Σ_g) − 2`.
- `genusSurface_succ_eq_connectedSum_{chi,totalPfaffian}` — verifies `Σ_{g+1} = Σ_g # T²`
  against `connectedSumCGB` on **both** invariants, so the closed form really is the
  iterated connected sum.

**Counts**: 426→498 lines, 44→53 theorems, 11→12 definitions (meta synced, both
`.meta.*` and `.leanFile.*`). Status stays **axiomatized** (2 structure-encoded
assumptions unchanged; the additions are 0-axiom/0-sorry consequences).

### Frontier (unchanged)
Elementary calculus of the structure-encoded Euler invariant is now quite complete.
Further progress is BLOCKED on absent Mathlib differential geometry (Pfaffian,
characteristic-form integration over manifolds, manifold Euler characteristic).

### Process note
This session's other work (erdos-1018) was briefly committed to the same branch by
mistake; split cleanly onto `feature/researcher-2-3-euler` before opening the PR
(erdos-1018 PR #36412 stays uncontaminated).
