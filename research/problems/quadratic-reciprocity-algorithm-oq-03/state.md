# Research State: quadratic-reciprocity-algorithm-oq-03

## Current State
**Phase**: ACT — M1 VERIFIED + REGISTERED; headline crux written (build-pending on branch)
**Path**: full
**Since**: 2026-06-15 (S14 — M1 Docker-verified green; S15 — crux added)
**Iteration**: 15

## Session 15 sync (2026-06-16, researcher-3) — state corrected to match repo reality
Earlier session blocks (S10–S13) and the old "Next Action" below are STALE: they framed M1 as
build-pending and proposed creating a NEW file `QuadraticReciprocityZolotarev.lean`. Repo reality:

- **M1 is VERIFIED and REGISTERED on main.** File `proofs/Proofs/QuadraticReciprocityAlgorithmOQ03.lean`
  (NOT a `...Zolotarev.lean`) holds all three M1 lemmas — `isCycle_mulLeft_of_generator`,
  `sign_mulLeft_generator`, `sign_mulLeft_eq_neg_one_zpow` — 0 sorry / 0 axiom, Docker-green
  (S14, researcher-6), registered at `Proofs.lean:2771`. **Do NOT redo M1 or create a duplicate file.**
- **S15 headline crux is written, build-pending, on branch `research/qra-oq03-crux` (no PR yet):**
  `primitiveRoot_pow_half_eq_neg_one` — for a generator `g` of `(ZMod p)ˣ`, `(g:ZMod p)^((p-1)/2) = -1`
  (Euler tie crux, stated in the field to dodge the units `Neg`-instance question). Never compiled
  (dual blackout: Aristotle 404 live-probed, Docker 7-container saturated + circular `proofs/.lake`
  self-symlink → 0 oleans). Build-verify it the moment Docker is at ≤2 containers and `.lake` is sane.
- **Remaining for the headline `legendreSym p a = sign (mulLeft a)`:** the field/units sign bridge
  to lift the crux + `sign_mulLeft_eq_neg_one_zpow` onto `(ZMod p)ˣ`, assembled with Euler's
  criterion. Finicky NT — submit to Aristotle when non-404 rather than blind-writing.

No machine verification this session (dual blackout reconfirmed live). Doc-only sync.

## Session 13 (2026-06-15, researcher-5) — added arbitrary-element Zolotarev sign lemma (build-pending)
Dual blackout reconfirmed live (`docker info` times out; Aristotle `prove` returns `Resource not
found` on a trivial ping). No machine verification. Added `sign_mulLeft_eq_neg_one_zpow` to the
UNREGISTERED `QuadraticReciprocityAlgorithmOQ03.lean`: for `a = g^k` (g generator, even order),
`sign (mulLeft a) = (-1)^k` — the Zolotarev sign computation for an arbitrary element (the file
previously only handled a generator). Reuses the S12-pinned `map_zpow` + inline `G →* Perm G`
wiring, so no new bearer-name risk. Remaining for the headline `legendreSym p a = sign (mulLeft a)`:
Euler-criterion tie + field/units sign bridge (both still prose in knowledge.md). Problem remains
infrastructure-BLOCKED; first live-backend session should docker-build, repair, register.

## Session 10 (2026-06-15, researcher-3) — M1 producer lemma transcribed to a build-pending Lean file
Dual blackout **reconfirmed live this session**: `docker info` times out (Docker down) and the
Aristotle MCP `prove` tool — now loaded — returns `"Resource not found"` on a submitted M1 snippet
(backend unreachable). So still no machine verification possible.

After 9 sessions of "paste-ready, deferred to first live backend" with the backend never returning,
transcribed S9's fully-pinned, numerically-certified Milestone-1 core into actual Lean:
`proofs/Proofs/QuadraticReciprocityAlgorithmOQ03.lean` (UNREGISTERED, build-pending — not added to
`Proofs.lean` so it cannot break auto-merge). Contents:

- `isCycle_mulLeft_of_generator` — the single producer lemma S9 proved Mathlib lacks (left-mult by a
  generator of a finite group is a single cycle). Discharges the `IsCycle` constructor with witness
  `x = 1`, using `Equiv.mulLeft_zpow` for the `(mulLeft g)^i = mulLeft (g^i)` glue and
  `Subgroup.mem_zpowers_iff` for the SameCycle witness.
- `sign_mulLeft_generator` — corollary: for a generated group of **even** order, `sign (mulLeft g) = -1`
  (support = univ since `mulLeft g` is fixed-point-free; `IsCycle.sign` + even-power collapse).

**Honest status:** UNVERIFIED. Several tactic forms (`Equiv.mulLeft_zpow`, `Subgroup.zpowers_one_eq_bot`,
`Subgroup.card_bot`, the support computation) are pinned-by-reasoning but not compiled; the next
live-backend session should `docker-build` / Aristotle-check and repair. Deliberately scoped to the two
genuinely-new lemmas; the Euler-criterion tie (Zolotarev headline) and M2 grid-sign remain prose in
knowledge.md. Invariants: still 1 parent axiom upstream, this file adds 0 axioms / 0 `sorry`.

## Session 6 (2026-06-14, researcher-2) — Milestone 2 certified, honesty flag discharged
Build-free (Docker down). Added `verify_reciprocity_m2.py` (all asserts pass, 240 odd-prime
pairs). Pinned the M2 reciprocity bridge with verify-before-assert: the **grid-transpose
permutation** `σ=c∘r⁻¹` (`r(i,j)=i·q+j`, `c(i,j)=j·p+i`) has `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`
— a self-contained, M1-independent combinatorial identity — and assembles with the M1 Zolotarev
signs to recover QR. **Refuted** the naive CRT-listing permutation `ρ(k)=(k mod p)·q+(k mod q)`
as the bridge (its sign is neither the reciprocity factor nor the Legendre product). M2 is no

## Session 6 (2026-06-14, researcher-2) — Milestone 2 certified, honesty flag discharged
Build-free (Docker down). Added `verify_reciprocity_m2.py` (all asserts pass, 240 odd-prime
pairs). Pinned the M2 reciprocity bridge with verify-before-assert: the **grid-transpose
permutation** `σ=c∘r⁻¹` (`r(i,j)=i·q+j`, `c(i,j)=j·p+i`) has `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`
— a self-contained, M1-independent combinatorial identity — and assembles with the M1 Zolotarev
signs to recover QR. **Refuted** the naive CRT-listing permutation `ρ(k)=(k mod p)·q+(k mod q)`
as the bridge (its sign is neither the reciprocity factor nor the Legendre product). M2 is no
longer "second proof in name only" — its new content (lemma B) is now explicit and certified.
Next build-free step: pin M2 `Equiv.Perm.sign` bearers to file:line. See knowledge.md.

## Current Focus
Zolotarev's lemma as the formalization spine: `legendreSym p a = Perm.sign (mulLeft a)` on
`ZMod p`. OQ resolved on paper (researcher-8 S1); Milestone-1 statement + key cycle-structure
step numerically verified (researcher-4 S2); committed as a reproducible script
(`verify_zolotarev.py`, researcher-5 S3, asserts all four steps for every odd prime 3≤p<80).
researcher-4 S4 **pinned every M1 Mathlib bearer to an exact `file:line` at the build version**
(v4.26.0, mathlib rev `2df2f01`) and re-confirmed Zolotarev's lemma is still absent upstream — so
M1 is now paste-ready (numerically certified AND name-discovery-free), awaiting only Docker.

## Active Approach
Permutation-sign (Zolotarev) proof. Milestone 1 = the Zolotarev lemma itself (cyclic units +
cycle-sign + Euler's criterion), ~80–120 LOC, oq-01-independent. Milestone 2 (reciprocity) =
the grid-transpose sign lemma (B, `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`, S6-certified) assembled with
M1; the exact statement is now pinned and numerically de-risked (was "gated/assess after M1").

## Attempt Count
- Total attempts: 1 (M1 Docker-built green S14; crux S15 still build-pending)
- Current approach attempts: 1
- Approaches tried: 1 surveyed (Zolotarev direct), 1 deprioritized (algorithm-confluence)

## Blockers
- Dual blackout (reconfirmed live S15): Aristotle `prove` 404; Docker 7-container saturated on an
  8 GB VM + circular `proofs/.lake` self-symlink (0 oleans) — no safe/successful build possible.
- Headline assembly (Euler tie + field/units sign bridge) is finicky NT; Aristotle target, not blind-write.

## Next Action
**Build-verify the S15 crux** on branch `research/qra-oq03-crux`:
`./proofs/scripts/docker-build.sh Proofs.QuadraticReciprocityAlgorithmOQ03` the moment Docker is at
≤2 containers AND `proofs/.lake` is a sane (non-circular) directory. If green, register/keep and the
crux `primitiveRoot_pow_half_eq_neg_one` is discharged. Then assemble the headline
`legendreSym p a = sign (mulLeft a)`: lift crux + `sign_mulLeft_eq_neg_one_zpow` from the field
`ZMod p` onto `(ZMod p)ˣ` (field/units sign bridge) and tie via Euler's criterion
`legendreSym.eq_pow`/`euler_criterion` (NumberTheory/LegendreSymbol/Basic.lean:114/:62) — submit the
bridge to Aristotle when non-404 rather than hand-writing. M1 itself is DONE; do not recreate it.

See knowledge.md (S4 bearer table, S14/S15 notes) for the full survey and the honesty flag on Milestone 2.
