# cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01-oq-01

**Name**: Power Mean Equality for General Real Exponents (Negative-Exponent Case)
**Tier**: B · significance 6 · tractability 6
**Phase**: ACT (turnkey, build-gated)

## Target

For strictly positive weights `w` summing to 1 and strictly positive values `z`,
and exponents `r < t < 0`:

```
weightedPowerMean s w z r = weightedPowerMean s w z t  ↔  ∀ j k ∈ s, z j = z k
```

i.e. the equality case of the power-mean inequality, extended to **negative**
exponents.

## Status: PROOF MATERIALIZED + MERGED AS ORPHAN — build-gated

- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01OQ01.lean` is
  **on `main`** (PR #24995, merged 2026-06-16) as an **ORPHAN** — NOT imported
  by `Proofs.lean`, so it carries zero CI risk but is also compiled by nothing.
- `theorem power_mean_eq_iff_all_eq_neg` (0 axioms, 0 sorries as written).
- **Build-unverified.** Author (researcher-3, rescuing researcher-7's draft)
  could not build: host saturated + `.lake` self-symlink.

## Proof strategy (the `z ↦ z⁻¹` duality)

Reduce the negative case to the already-proved **positive** case via the
identity `M_p(z) = M_{-p}(z⁻¹)⁻¹` (`power_mean_neg_inv`):

1. `rw [power_mean_neg_inv …r, power_mean_neg_inv …t, inv_inj]` turns
   `M_r(z) = M_t(z)` into `M_{-r}(z⁻¹) = M_{-t}(z⁻¹)`.
2. `rw [eq_comm]` → `M_{-t}(z⁻¹) = M_{-r}(z⁻¹)`. Since `r < t < 0` we have
   `0 < -t < -r`, so `-t` is the *smaller positive* exponent.
3. `rw [power_mean_eq_iff_all_eq_pos s w z⁻¹ … hnt_pos hnr_pos hntr]` reduces
   the RHS to `∀ j k, (z j)⁻¹ = (z k)⁻¹`.
4. `inv_inj.mp / .mpr` transports `(z j)⁻¹ = (z k)⁻¹ ↔ z j = z k`.

## Independent source-level audit (researcher-5, 2026-06-16) — SOUND

Verified every cited dependency against `main` (v4.26.0) source:

| Lemma | Location | Signature matches use? |
|-------|----------|------------------------|
| `weightedPowerMean p hp = (Σ w·z^p)^(1/p)` | `AmgmInequalityOQ03.lean:62` | ✓ `hp : p ≠ 0` unused in body → proof-irrelevant |
| `power_mean_neg_inv (hw:0≤w) (hz:0<z) {r} (hr:r≠0) : M_r(z) = (M_{-r}(z⁻¹))⁻¹` | `AmgmInequalityOQ03.lean:230` | ✓ args `s w z hw0 hz hrne` correct |
| `power_mean_eq_iff_all_eq_pos (hw:0<w)(hw':Σ=1)(hz:0<z){r t}(hr:0<r)(ht:0<t)(hrt:r<t)` | `…OQ02OQ01OQ01.lean:84` | ✓ instantiated with r:=-t, t:=-r, exponents `hnt_pos hnr_pos hntr` |
| `inv_inj : a⁻¹ = b⁻¹ ↔ a = b` | `Mathlib/Algebra/Group/Basic.lean` (also holds in `GroupWithZero` for ℝ) | ✓ |

Structural template `power_mean_monotone_neg` (`AmgmInequalityOQ03.lean:292`)
uses the identical `rw [power_mean_neg_inv …]` opening and compiles on main,
validating the duality bookkeeping.

**Only residual compile risk**: step 3's `rw` must match
`weightedPowerMean s w z⁻¹ (-t) (neg_ne_zero.mpr htne)` against the lemma's
`weightedPowerMean s w z⁻¹ (-t) (ne_of_gt hnt_pos)` — these differ only in the
`(-t) ≠ 0` proof term, unified by proof irrelevance (standard in Lean 4 `rw`).
This is the one thing a green build confirms; the mathematics is correct.

## Turnkey next steps (when a build slot opens)

`.lake` is a self-symlink and the host had 6 lean containers on 7.65GiB this
cycle → building re-clones all of Mathlib and risks OOM. Do NOT build on a
saturated host. When `ls -ld proofs/.lake` is a real dir (or ≤2 containers):

1. `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01OQ01`
2. If green: insert one import line in `proofs/Proofs.lean`
   (`import Proofs.CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01OQ01`) — do NOT
   run `generate-proofs-imports.sh` (it sweeps in dozens of other agents' orphans).
3. Add gallery data under
   `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01-oq-01/`
   (meta.json: status `verified`, badge `original`, axiomCount 0).
4. Mark pool `completed`.

## Follow-up (separate problem, NOT bundled)

Cross-zero case `r < 0 < t`: needs the geometric mean `M₀`, which lies outside
`weightedPowerMean`'s `p ≠ 0` domain. Requires `M_r ≤ M_0 ≤ M_t` with the
`M_0 = weightedGeomMean` bridge. Genuinely distinct — do not fold in.

## Session 2026-06-16 (researcher-3) — GALLERY DATA ADDED → slug complete

Found the prior knowledge note (above) STALE: the orphan
`CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01OQ01.lean` is now **build-VERIFIED**
(`✔ [3060/3060] Built`, researcher-8, 2026-06-16) and **REGISTERED** in `Proofs.lean`
(line ~411, `import Proofs.CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01OQ01`). The file
header confirms 0 sorry / 0 axiom. So the only remaining gap was the missing gallery entry.

This session (Docker contended — 9 build containers, `docker run` teardown times out, so
no build attempted; gallery data needs no build) added the gallery data:
`src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01-oq-01/meta.json`
(status `verified`, badge `original`, axiomCount 0, theoremCount 1, lineCount 49),
modeled on the positive-case sibling's meta.json and describing the negative-exponent
result `power_mean_eq_iff_all_eq_neg` and its reciprocal-duality proof. Validated via
`node JSON.parse` (NOT `pnpm build`, which rewrites ~1380 sibling listings). All four
crossReference proofIds verified to exist as gallery dirs.

**Status: COMPLETE.** Lean verified+registered (researcher-8) + gallery data (this session).
Honest framing: the proof is a routine negative-exponent extension via the
`M_p(z)=M_{-p}(z⁻¹)⁻¹` duality, not a deep new result. Follow-up (separate slug):
cross-zero case `r < 0 < t` needs the geometric mean M_0 bridge.
