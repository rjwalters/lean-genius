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

## Session 2026-07-09 (researcher-6) — Part XI: genus-g surface classification (VERIFIED)

Generalized the genus-0/1/2 special cases to the full closed-orientable-surface
classification. Added `genusSurfaceCGB g` (Σ_g at halfDim=1, χ=2-2g, ∫Pf=(2-2g)·2π;
chern_gauss_bonnet := rfl by direct construction, sidestepping the dependent-halfDim
recursion of an iterated connectedSum def) and 7 theorems:
- `genusSurfaceCGB_chi`: **χ(Σ_g) = 2-2g** (full classification, all g).
- `genusSurfaceCGB_gauss_bonnet` + `_totalPfaffian`: **∫K dA = 2π·χ = 4π(1-g)** via
  `two_dim_gauss_bonnet` (halfDim=1).
- `genusSurfaceCGB_chi_succ`: handle attachment χ(Σ_{g+1})=χ(Σ_g)+χ(T²)-2 = connected-sum law.
- `_zero_chi`(2)/`_one_chi`(0)/`_two_chi`(-2, matches genus_two_surface_chi).
8 decls, 0 sorry, 0 new axioms (status stays axiomatized; the 2 structure-encoded CGB
assumptions untouched). **VERIFIED** docker Build succeeded (retries 1-2 = env exit-135,
no .lean diagnostics; attempt 3 green). PR #36510.

Frontier unchanged: core BLOCKED on Mathlib v4.26 (no Pfaffian / characteristic-form
integration / manifold χ). The elementary surface calculus is now complete (arbitrary genus).

## Session 2026-07-09 (researcher-2) — Part XII: genus additivity of connected sum (UNVERIFIED, env SIGBUS)

Added the full genus-additivity of connected sum to `EulerPolyhedralOQ02OQ02.lean`
(namespace `ChernGaussBonnet`), 2 theorems, 0 new axioms (status stays axiomatized):
- `connectedSum_genusSurface_chi`: `χ(Σ_g # Σ_h) = χ(Σ_{g+h})` — from
  `(2−2g)+(2−2h)−2 = 2−2(g+h)`; `simp only [connectedSumCGB_chi, genusSurfaceCGB_chi]`
  then `push_cast; ring`.
- `connectedSum_genusSurface_totalPfaffian`: `∫Pf(Σ_g # Σ_h) = ∫Pf(Σ_{g+h})` — the
  removed-disk `2·(2π)` term exactly accounts for the χ-drop; `simp only
  [connectedSumCGB_totalPfaffian, genusSurfaceCGB_halfDim, genusSurfaceCGB_totalPfaffian,
  cgbConst_one]` then `push_cast; ring`.

Together these upgrade the single-handle recursion `genusSurfaceCGB_chi_succ` (the h=1
case) to full additivity, exhibiting genus as the monoid iso (surfaces, #) ≅ (ℕ,+).

Meta counts synced: leanFile+meta theoremCount 52→54, lineCount 483→512 (both blocks);
added a Part XII keyInsights bullet.

**Verification: UNVERIFIED.** Persistent env failure — SIGBUS-135 at olean-write on
~10 build runs (clean 3.8s elaboration each, no diagnostic at the new lines) plus
recurring corrupted mathlib cache `.ir/.olean` "invalid header" at the import line
(BoundedVariation.ir, Centroid.olean.private); `docker-build.sh --repair-cache`
re-downloaded 7727 files but the next build still SIGBUS'd at write. Both proofs are
one-liners over directly-applicable existing lemmas; shipped UNVERIFIED per the file's
own prior-session env pattern (Parts X/XI also hit exit-135 storms).

### Frontier
Unchanged: core BLOCKED on Mathlib v4.26 (no Pfaffian / characteristic-form integration
/ manifold χ). The elementary surface calculus (arbitrary genus, connected sum, product,
odd-vanishing) is now complete including genus-additivity; no further elementary increment
is evident without the differential-geometry machinery.

## Session 2026-07-10 (researcher-1) — VERIFY standing-unverified file (no bug)

Prior session shipped the last two theorems UNVERIFIED (SIGBUS-135 olean-write). The file
`EulerPolyhedralOQ02OQ02.lean` (612 L, ChernGaussBonnet namespace) is Mathlib-imports-only, so
verified via lean-elab ([[reference-docker-down-lean-elab-verification-path]]): whole file EXIT 0,
zero errors, zero warnings. `#print axioms genusSurfaceCGB_totalPfaffian_eq_zero_iff` =
[propext, Classical.choice, Quot.sound] — no sorryAx. The standing-unverified one-liners are
confirmed correct (no bug this time, unlike the 4 breakages found elsewhere this session).
0 axioms / 0 sorries. Marked completed.

---

## Session 2026-07-11 (researcher-8) — BUILD REPAIR: duplicate declarations

**Mode:** REVISIT (mature axiomatized entry) — **REPAIR, not new content**
**Outcome:** Fixed a broken file that did not compile on `main`.

### Bug
PR #37939 (`4fc27e19a7`, "genus χ order/parity + product-surface Euler
characteristic") added Part XV, which **re-declared** two theorems already
introduced by PR #37948 in Part XIII:
- `genusSurfaceCGB_chi_strictAnti` (Part XIII line 602 vs Part XV line 693)
- `genusSurfaceCGB_chi_even`       (Part XIII line 624 vs Part XV line 708)

Both are in the same namespace `ChernGaussBonnet`, so Lean 4 rejected the file:
`error: 'ChernGaussBonnet.genusSurfaceCGB_chi_strictAnti' has already been declared`
(and likewise for `_chi_even`). The file had been sitting broken on `main`
(the deployer merges math PRs without a Docker rebuild; the SIGBUS-prone
Docker build masks it as an environmental exit-135).

### Fix
Removed the two **duplicate** Part XV theorems. Kept the genuinely-new Part XV
content: `genusSurfaceCGB_chi_antitone` (weak-antitone corollary, which now
references the surviving Part XIII `genusSurfaceCGB_chi_strictAnti`),
`prodCGB_genusSurface_chi`, and `prodCGB_genusSurface_totalPfaffian`. Updated the
Part XV section header. Net: 74 → 72 theorems, still 0 sorries, 0 axiom decls,
2 structure assumptions — mathematical content unchanged.

### Verification
Host elan `lean` (v4.26.0) with main's Mathlib LEAN_PATH:
- Fixed file: **EXIT 0**, no output (type-checks clean).
- `origin/main` file: **EXIT 1**, the two "already been declared" errors above.
(Docker build gave transient exit-135 SIGBUS both times — olean corruption in
the volume, a known false negative; host lean is authoritative — see
researcher-9 note on exit-135.)

---

## Session 2026-07-12 (researcher-10) — Part XIX: Künneth convolution algebra

**Mode:** REVISIT (mature axiomatized entry; add within the elementary/homological framework)
**Outcome:** progress (1 def + 6 theorems, 0-axiom)

Rebased a stale branch onto `origin/main` first (Part XVIII, PR #38402, had merged
between claim and work). Part XVIII computes *one* Künneth convolution and matches it to
the `Σ_g × Σ_h` Betti table; Part XIX proves the algebraic laws of the `kunnethBetti`
convolution operation itself:

- `kunnethBetti_comm` — the convolution `(b ⋆ c)(k) = Σ_{i+j=k} bᵢcⱼ` is commutative,
  via `Finset.sum_range_reflect` reindexing `i ↦ k − i` (with `omega` on the two Nat
  subtractions `k+1-1-i = k-i` and `k-(k-i) = i`). Homological shadow of `M × N ≅ N × M`.
- `pointBetti` (def) `= (1, 0, 0, …)` + `pointBetti_zero/_succ` (@[simp]).
- `kunnethBetti_pointBetti_left` — δ is a left unit (`Finset.sum_eq_single 0`, off-degree
  terms killed by `pointBetti_succ`). `_right` follows by comm. Two-sided unit; shadow of
  `pt × M ≅ M`, mirroring `pointCGB` as the Cartesian-product monoid identity (Part XVII).
- `prodSurfaceBetti_comm` (concrete corollary) — `bₖ(Σ_g × Σ_h) = bₖ(Σ_h × Σ_g)` for
  `k ≤ 4`, the palindrome symmetric under `g ↔ h`; shadow of `Σ_g × Σ_h ≅ Σ_h × Σ_g`.

**Honest scope:** commutativity + two-sided unit only. Associativity of the Cauchy product
(needed to claim a full commutative *monoid*) is standard but NOT formalized here — the
prose says so. Not enumeration theater: these are the operation's structural laws, not more
tables.

### Verification
Docker skipped (SIGBUS-prone per prior sessions). Host `lean` v4.26.0 elab against main's
Mathlib LEAN_PATH: whole file **EXIT 0**, no errors/warnings (1171 L). `#print axioms` on
all four new theorems = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool`. 0-axiom preserved (2 structure-encoded CGB assumptions unchanged, not
invoked). File: 102 `^theorem` + 17 def, 0 sorries, 0 axiom decls.

### Frontier
Unchanged: core BLOCKED on Mathlib v4.26 (no Pfaffian / characteristic-form integration /
manifold χ). Convolution associativity would complete the commutative-monoid claim on Betti
sequences — a self-contained next elementary increment (Cauchy-product associativity over ℕ).

## Session 2026-07-19 (researcher-1) — Künneth convolution associativity (VERIFIED axiom-free)

**Mode:** REVISIT (mature axiomatized entry; the elementary `kunnethBetti` convolution algebra).
**Outcome:** +1 theorem, 0 axioms — closes the named frontier.

Parts XVIII–XIX built the Künneth convolution `kunnethBetti b c k = ∑_{i∈range(k+1)} bᵢ·c_{k−i}`
on Betti sequences and proved its **commutativity** (`kunnethBetti_comm`) and **two-sided unit**
`pointBetti = δ` (`kunnethBetti_pointBetti_left`/`_right`). The stated remaining increment was
**associativity** (Cauchy-product associativity over ℕ). Added:

- `kunnethBetti_assoc (a b c k) : kunnethBetti (kunnethBetti a b) c k = kunnethBetti a (kunnethBetti b c) k`.
  Both sides expand to `∑_{i+j+l=k} aᵢbⱼcₗ`. Proof: `unfold`, distribute the outer factor into each
  convolution (`simp_rw [Finset.sum_mul, Finset.mul_sum]`), flatten both double sums with
  `Finset.sum_sigma'`, then match the triangular index sets `{(m,i):i≤m≤k}` and `{(i,j):i+j≤k}`
  by the reindexing bijection `(m,i) ↦ (i, m−i)` / inverse `(i,j) ↦ (i+j, i)` via `Finset.sum_bij'`.

With comm + unit this makes `⋆` a **commutative-monoid** operation on Betti sequences — the
homological shadow of associativity of the Cartesian product `(M×N)×P ≅ M×(N×P)`.

Reusable idiom (Cauchy-product associativity over ℕ): distribute with `sum_mul`/`mul_sum`, flatten
nested sums with `Finset.sum_sigma'`, then `Finset.sum_bij'` between the two triangular sigma
finsets — **all five `sum_bij'` obligations (both membership, both inverses, the term equality)
close by `simp only [Finset.mem_sigma, Finset.mem_range] at …` followed by `omega` (with `ring` for
the term)**. Key: `simp only [mem_sigma, mem_range]` reduces the `Sigma.mk` projections so `omega`
sees the raw naturals; the sigma-equality inverse goals close by `simp only [<omega-fact>]` rewriting
the single differing first component (the second components are already syntactically equal).

**Build: VERIFIED** host-elab vs prebuilt Mathlib v4.31.0 oleans (`bin/lake env lean`, EXIT 0, no
errors/warnings in the new code). `#print axioms ChernGaussBonnet.kunnethBetti_assoc`
= `[propext, Classical.choice, Quot.sound]`. File 1302→1340 lines, +1 theorem; node stays 0-axiom
(the deep CGB core assumptions live in sibling files and are not invoked here).
