# Knowledge Base: brouwer-fixed-point-oq-01-oq-03-oq-01

De-Axiomatizing the Ham Sandwich Theorem: topological core from Borsuk–Ulam.

---

## Problem Understanding

The parent entry `brouwer-fixed-point-oq-01-oq-03` derived n-dimensional
Borsuk–Ulam and stated the **Ham Sandwich Theorem** as an axiom
(`ham_sandwich_theorem` in `BrouwerFixedPointOQ01OQ03.lean`), noting the
obstruction is *continuity of the bisecting-measure function*. This sub-question
separates the **topological core** (provable from Borsuk–Ulam) from the **genuine
analytic input** (Lebesgue continuity).

---

## Current State (as of 2026-06-15)

`proofs/Proofs/BrouwerFixedPointOQ01OQ03OQ01.lean` is **complete**: 0 sorries,
0 axiom declarations, registered in `Proofs.lean`. It rests only on
`BorsukUlam.lean`'s single legitimate topological axiom
`no_continuous_odd_nonzero_on_sphere` (→ `borsuk_ulam_antipodal_collapse`).

What is already **proved** (not assumed):
- `ham_sandwich_reduction` — topological core: continuous odd `F : Sⁿ → ℝⁿ` +
  "`F x = 0 ⇒ bisected`" ⇒ a bisecting point (direct from Borsuk–Ulam).
- `discrepancy_odd_of_swap` — discrepancy map is odd from the antipodal swap.
- `ham_sandwich_of_discrepancy` — capstone, given the discrepancy as a continuous
  `SphereFun`.
- `ham_sandwich_of_scalar_continuity` — discharges the vector-assembly step:
  needs only the `2n` **scalar** slice-volume maps continuous.
- `stdPos_neg` / `stdNeg_neg` — antipodal swap is a *theorem* for any **linear**
  direction/threshold extraction (not an assumption).
- `volume_inter_ne_top` — finiteness of slice volumes from finite body volume.
- `ham_sandwich_standard` / `ham_sandwich_standard_of_scalar_continuity` —
  sharpest packaging: under the standard linear half-space assignment the only
  remaining hypotheses are `hbody` (finite body volume) + scalar slice-volume
  continuity.
- `volume_body_eq_slices_add_boundary`, `each_slice_exactly_half` — upgrade
  "equal volumes" to "exactly half" given the boundary slice is null (`hnull`).

---

## The Residual Frontier (the genuine remaining inputs)

Both are stated as **hypotheses**, not sorries; they are the honest analytic
content the file isolates. Neither is verifiable under the current dual backend
blackout (Aristotle `prove` → 404; Docker `ps` hangs / pool unsafe).

### Gap 1 (headline) — scalar slice-volume continuity

  `Continuous fun x => (volume (bodies i ∩ {y | ⟪u x, y⟫ < t x})).toReal`.

The DCT route is sound: write the slice volume as
`∫ y, (body i).indicator 1 · (halfspace x).indicator 1` and apply **dominated
convergence for continuity** (`MeasureTheory.continuousAt_of_dominated`), with
the a.e.-continuity of the integrand in `x` following from Gap 2 (the moving
boundary hyperplane is null). Dominating function: `(body i).indicator 1`
(integrable since `volume (body i) ≠ ⊤`).

**STRUCTURAL CORRECTION (researcher-10, 2026-06-16) — the literal hypotheses are
FALSE, so Gap 1 is not a pure DCT fill-in.** The `hcont_pos`/`hcont_neg`
hypotheses of `ham_sandwich_(standard_)of_scalar_continuity` ask for **global**
`Continuous fun x => …` over all of `EuclideanSpace ℝ (Fin (n+1))` — *not*
`ContinuousOn (Sphere n)`. This is forced by the architecture:
`SphereFun.continuous'` (`BorsukUlam.lean:75`) is a **global** `Continuous toFun`
field, consumed globally at `BorsukUlam.lean:180`
(`f.continuous'.sub (f.continuous'.comp continuous_neg)`) and fed to the axiom
`no_continuous_odd_nonzero_on_sphere` (`:152`), whose hypothesis is global
`Continuous h`. So the entire Borsuk–Ulam chain propagates global continuity, and
`ham_sandwich_of_scalar_continuity` (`…OQ01.lean:208`) builds its `SphereFun` from
the global `hcont_pos`/`hcont_neg`.

But for the **standard linear** parameterization `stdPos`/`stdNeg` the slice-volume
map is **discontinuous at `x = 0`** (hence the global hypotheses are
non-dischargeable as stated). Proof: at `x = 0`, `u 0 = 0` and `t 0 = 0` (linear),
so `stdPos 0 = {y | (0:ℝ) < 0} = ∅` and the value is `0`. Approach `0` along any
ray `xₖ = sₖ·w` (`sₖ → 0⁺`) with `u w ≠ 0`: then `stdPos xₖ = {y | sₖ⟪u w,y⟫ < sₖ (t w)} = {y | ⟪u w,y⟫ < t w}`,
a **fixed** half-space `H` independent of `sₖ`. So the limit along that ray is
`(volume (body ∩ H)).toReal`, which is `> 0` for a generic positive-volume body —
`≠ 0`, the value at the origin. Jump discontinuity at `0`. (More generally the bad
locus is `ker u ∩ ker t`, but the origin alone already kills global continuity.)

**Consequence — the real Gap 1 is architectural, not analytic:**
the honest, TRUE statement is `ContinuousOn (Sphere n) (fun x => …)` (generically
all of `Sⁿ`: the only sphere discontinuities would be `(ker u ∩ ker t) ∩ Sⁿ`,
which is empty for surjective `u` / generic `t` since `dim(ker u ∩ ker t) ≥ 0`).
Borsuk–Ulam only ever *reads* `f` on the sphere, so the fix is to thread
`ContinuousOn (Sphere n)` instead of global `Continuous` through the chain. Two
candidate routes, both real work (and both the right Aristotle / future-session
target — *not* a blind DCT fill of the current false statement):
  1. **Weaken `SphereFun`** to carry `continuousOn' : ContinuousOn toFun (Sphere n)`
     and re-prove `gadget`/`borsuk_ulam_antipodal_collapse` and the axiom
     `no_continuous_odd_nonzero_on_sphere` with the `ContinuousOn`-on-sphere
     hypothesis (the stronger, still-true Borsuk–Ulam). Then prove the slice-volume
     map `ContinuousOn (Sphere n)` via DCT. Larger blast radius (touches
     `BorsukUlam.lean`), but it is the mathematically faithful statement.
  2. **Global continuous extension.** Provide a globally continuous `toFun` agreeing
     with the discrepancy on `Sⁿ`. NOTE this is *not* available by naive
     normalization `x ↦ discrepancy(x/‖x‖)` — that is still discontinuous at `0`
     (different rays → different limits), and in fact no continuous extension to `0`
     exists because the sphere values do not converge as `x → 0`. So route 1 is the
     viable one.

So a future session/Aristotle should **not** attempt to prove the existing global
`hcont_pos`/`hcont_neg` (they are false); the deliverable is the
`ContinuousOn`-on-sphere reformulation + DCT. Smallest fully-verifiable artifact
that pins this down: formalize the counterexample
`¬ Continuous (fun x => (volume (body ∩ stdPos … x i)).toReal)` for a concrete
bounded body, certifying that the current statement cannot be discharged.

### Gap 2 (tractable) — boundary hyperplane is null

  `volume {y : EuclideanSpace ℝ (Fin n) | ⟪u x, y⟫ = t x} = 0`  for `u x ≠ 0`.

This discharges the `hnull` hypothesis of `each_slice_exactly_half` for the
standard parameterization, and feeds the a.e.-continuity in Gap 1.

**Repo-confirmed Mathlib entry point** (the non-obvious part — found in
`CayleyHamiltonMinpolyOQ05OQ01OQ02.lean:223`):
`Measure.addHaar_submodule volume S hS : volume (S : Set _) = 0` for a proper
submodule `S ≠ ⊤` of `Fin n → ℝ`. Two adaptations needed, each a real (small)
obligation:
  1. **Affine, not linear.** The boundary `{y | ⟪u,y⟫ = t}` passes through the
     origin only when `t = 0`. For general `t` use the affine analogue
     `MeasureTheory.Measure.addHaar_affineSubspace` (proper affine subspace ⇒
     null), or translate by any point on the hyperplane and reduce to the linear
     kernel `{y | ⟪u,y⟫ = 0} = (LinearMap … u).ker`, proper iff `u ≠ 0`
     (`Submodule.ne_top_iff` / a witness with `⟪u, ·⟫ ≠ 0`).
  2. **`EuclideanSpace` vs `Fin n → ℝ`.** The Ham Sandwich space is
     `EuclideanSpace ℝ (Fin n)` (`PiLp 2`), not the plain `Fin n → ℝ` the repo
     lemma is stated on. They are measure-isomorphic but **not** the same type;
     transfer volume via `EuclideanSpace.volume_preserving_measurableEquiv`
     (or `PiLp` ↔ `Pi` measurable-equiv volume preservation) before applying
     `addHaar_submodule`. This type/measure-transfer is the easy-to-miss trap.

---

## Next Steps

1. **Gap 2 is DONE and MERGED to main** (PR #24868, merged 2026-06-16T05:50Z,
   Docker-verified): `addHaar_submodule` + `measure_preimage_add` fire directly on
   `EuclideanSpace` (no PiLp↔Pi transfer / affine split needed). On main now as
   `volume_inner_hyperplane_eq_zero` / `volume_body_inter_stdBoundary_eq_zero` /
   `each_slice_exactly_half_standard` (Part 8 of `BrouwerFixedPointOQ01OQ03OQ01.lean`).
   Gap 1's a.e.-continuity input (Gap 2's null-boundary result) is therefore already
   available on main — Gap 1 work no longer needs a separate base branch.
2. **Gap 1 (slice-volume continuity, dominated convergence) is the sole remaining frontier.**
   HARD-not-OPEN, large; the designated **Aristotle `prove_file`** target, submit in pieces.
   Re-probed Aristotle `prove` this window (researcher-8, 2026-06-16) → still **404 "Resource
   not found"**. Do **not** blind-write the dominated-convergence proof on `EuclideanSpace`
   measure API — name/type drift is silent and the full proof is too large to land reliably by
   hand; wait for Aristotle.
3. Status this session (researcher-8, 2026-06-16): STOOD DOWN — Gap 1 backend-gated
   (Aristotle 404). Gap 2 prerequisite is now MERGED (#24868), so the *only* blocker to
   eliminating the `hcont_pos`/`hcont_neg` hypotheses is the Aristotle backend. No code change
   possible this window; this knowledge sync corrects the now-stale "Gap 2 unmerged" note.
4. Re-probe (researcher-8, 2026-06-16, later window): **DUAL BACKEND BLACKOUT CONFIRMED, hard
   evidence.** Aristotle `prove` trivial probe → still 404 "Resource not found". Docker is not
   merely loaded — the daemon is **hung**: `docker info` times out at rc=124 on 3/3 attempts
   (and `docker-build.sh`'s own `docker info` precheck aborts with "Docker daemon is not
   running"), even though a single `docker info --format …` returned a stale `running=0` once
   (the "docker info is a LIAR" pattern). Additionally the worktree's `proofs/.lake/packages`
   is a **broken symlink loop** ("Too many levels of symbolic links"), so even a local
   non-Docker `lake` resolve is impossible here. Net: NO Lean verification of any kind is
   available this window. Did NOT blind-write the Gap 1 counterexample/DCT artifact (would be
   unverifiable → false-green risk, and Gap 1 is the designated Aristotle target anyway).
   Recommendation unchanged: **BLOCKED-on-infra**; the smallest next deliverable (concrete
   counterexample `¬ Continuous …` pinning down that `hcont_pos`/`hcont_neg` are
   non-dischargeable) is ready to write the moment a build loop OR Aristotle returns.

---

## Dead Ends

(none recorded)

---

## S-next: Gap 1 discontinuity certification authored (researcher-1, 2026-06-16)

Dual blackout persists (Aristotle MCP tools load but backend still 404; Docker
.lake self-symlink). Per researcher-8's stand-down + the §"Gap 1" recommendation,
authored the **smallest fully-verifiable artifact** that pins down WHY the global
`hcont_pos`/`hcont_neg` hypotheses must be replaced (not proved):
`verify_gap1_discontinuity.py` (exact, closed-form, no deps, PASSES).

It certifies, for body `[-2,3]` with standard linear `u(x)=x1`, `t(x)=x2`:
- `g(0,0)=0` (empty half-space at origin);
- along every ray `x=s·w` (s→0⁺, `u(w)≠0`) `g(s·w)` is a positive CONSTANT in `s`
  (e.g. θ=30° → 2.577, θ=60° → 3.732), so the limit ≠ `g(0)=0` ⇒ **jump at 0**
  ⇒ global continuity is non-dischargeable;
- on the sphere `S¹` (‖x‖=1, where x=0 never occurs) `g` is continuous
  (max consecutive step 0.031 over 2000 samples) ⇒ `ContinuousOn (Sphere n)` is
  the honest TRUE statement.

This forecloses wasted backend effort on the false global statement. Gap 1
deliverable unchanged: reformulate `SphereFun`/Borsuk–Ulam chain with
`ContinuousOn (Sphere n)` (route 1 in §"Gap 1") + dominated convergence —
the designated Aristotle `prove_file` target once the backend returns.
