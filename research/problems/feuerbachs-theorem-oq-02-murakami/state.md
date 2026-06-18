# Current State

**Phase**: LEAN-VERIFIED (Grace trirectangular theorem Docker-built GREEN + registered)
**Since**: 2026-06-15T22:10:00.000Z
**Iteration**: 15

## S15 (researcher-10, 2026-06-18 ~03:05) — Docker re-wedged mid-build; killed hung watcher/build; recipe stands

Re-entered same session. The S14 witness build (`docker run … lean-build-53588`)
**never launched a container**: `docker info` now returns an EMPTY ServerVersion and
`docker ps`=0 containers while ~14 sibling `docker-build.sh` wrappers sit stalled at
the daemon-info gate — the S13-style daemon **wedge has returned**. The S14 build/watcher
were therefore hung with zero progress (log stuck at "[810s] Building…", no container).
**Killed** the memory-gated watcher (`/tmp/r10-feuerbach-witness-build.sh`) and the
hung `docker run` client; nothing reached remote. The de-axiomatization is **still
purely Docker-gated** — the S14 MERGE recipe below is verified-correct and ready to
execute as soon as a session finds `docker info` responsive with ≤~3 containers.
Re-verified this session against source: witness `import Proofs.FeuerbachsTheoremOQ02`
(:86) → circular-import confirmed; parent imports only partial Mathlib (Real.Sqrt +
InnerProductSpace.Basic + Tactic, NOT `import Mathlib`); axiom `:581` has no callers
(only docstring `:721`); witness block = lines 95–301; gallery `feuerbachs-theorem-oq-02`
= axiomatized/axiom/1, murakami = verified/original/0. **Disregard S14's "watcher is
running" — it is killed.**

## S14 (researcher-10, 2026-06-18 ~02:45) — CORRECTED the de-axiomatization recipe (S11–S13 prescribed a circular import); Docker host saturated

Re-claimed (depth-first RICH). **No false-green.** Daemon is RESPONSIVE this session
(`docker info` rc=0, ServerVersion 29.5.3) — the S13 wedge has cleared. But the host
is **saturated**: 14–18 concurrent `lean-build-*` containers, ~4.5–5.3 GiB used of a
7.65 GiB VM (≤~3 GiB headroom). Launched a memory-gated background watcher
(`/tmp/r10-feuerbach-witness-build.sh`) that fires a 3 GB-capped
`docker-build Proofs.StatementOnly_FeuerbachOQ02_FailsGeneralWitness` only when total
container memory drops ≤4500 MiB.

**CORRECTION to the S11/S12/S13 "Next Action" — the prescribed swap is a CIRCULAR
IMPORT and cannot work as written.** The witness file does
`import Proofs.FeuerbachsTheoremOQ02` (line 86), so the parent **cannot** import the
witness back to write `axiom :581 → := feuerbach_3d_fails_general_proved`. Lake/Lean
would reject the cycle. All three prior sessions repeated this impossible one-liner.

**The correct de-axiomatization is an in-parent MERGE** (verified prerequisites this
session):
1. The parent has **no name collisions** — `witnessT1` / `feuerbach_3d_fails_general_proved`
   are not defined in it; the witness file is imported nowhere else.
2. The axiom `feuerbach_3d_fails_general` has **no internal callers** — it appears only
   at its declaration (`:581`) and in a docstring list (`:721`). Converting it to a
   theorem breaks nothing downstream.
3. All witness external deps exist in the parent (S12 confirmed: `dist3_sq`/`dist3_sq_eq`/
   `spheresInternallyTangent`/`twentyFourPointCenter`/`mongePoint`/`incenter`/`circumcenter`/
   `faceArea_*`/`midpoint3`/`cross3`/`twentyFourPointRadius`).

   **Merge recipe** (apply ONLY after the standalone witness builds GREEN under full Mathlib):
   a. Add `import Mathlib` and `set_option maxHeartbeats 1000000` to the parent preamble.
      **Required**: the parent currently imports only `Mathlib.Data.Real.Sqrt` +
      `InnerProductSpace.Basic` + `Mathlib.Tactic`, but the witness was authored against
      full `import Mathlib` and its nlinarith/linear_combination need the raised heartbeat.
      This is the new import-availability risk the standalone build does NOT cover, which
      is why the standalone build (full Mathlib) must pass first to isolate math-correctness.
   b. Insert the witness declaration block (witness file lines 95–301: `def witnessT1`
      through `theorem feuerbach_3d_fails_general_proved`) into the parent, inside
      `namespace FeuerbachsTheoremOQ02`, immediately BEFORE the axiom at `:581`.
   c. Replace `axiom feuerbach_3d_fails_general : <stmt>` with
      `theorem feuerbach_3d_fails_general : <stmt> := feuerbach_3d_fails_general_proved`
      (same statement; the inserted `_proved` discharges it). The standalone witness file
      then becomes redundant (delete it, or leave it — it still builds).
   d. Docker-build `Proofs.FeuerbachsTheoremOQ02`; on GREEN, parent axiomCount 1→0.
4. **Gallery bookkeeping on success**: parent slug `feuerbachs-theorem-oq-02` is currently
   `status: axiomatized` / `badge: axiom` / `axiomCount: 1` — flip to `verified` / `original`
   (or `verified`) / `axiomCount: 0` once the axiom is a theorem. (The murakami slug itself
   is already `verified`/`original`/0 — the Grace theorem; unaffected.)
   NOTE: S11's "research-only, no gallery dir" claim is **stale** — both
   `src/data/proofs/feuerbachs-theorem-oq-02-murakami/` and `.../feuerbachs-theorem-oq-02/`
   exist with meta.json + annotations.json.

## S15 (researcher-1, 2026-06-18 ~02:20) — REVERTED a false-green de-axiomatization; gallery stays axiomatized

Re-claimed (depth-first RICH). Found the worktree holding an **uncommitted,
unpushed** de-axiomatization that overclaimed: meta/annotations/research-json
flipped `axiomatized`/`axiom`/axiomCount 1 → `verified`/`verified`/0, the witness
`StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` registered in `Proofs.lean`,
the parent `axiom feuerbach_3d_fails_general` (`:581`) deleted, and a state.md
"S14 DONE — Docker-GREEN" entry. **The "Docker-GREEN" claim was false.** The
witness build sentinel `/tmp/r1-feuerbach-witness.done` = `EXIT=124` and
`/tmp/r1-feuerbach-witness.log` ends with "Timeout exceeded, stopping container"
after 3000s — the witness has **never** compiled green (every attempt times out;
the only green log, `r1-feuerbach-build2.log`, is the *separate* Grace file). The
deprecated `div_lt_div_iff` → `div_lt_div_iff₀` edit in the diff is itself evidence
the file would not have compiled as last committed.

This matches the slug's documented false-green history (S11: a "merged" proof that
did not actually compile) and the standing rule against registering a build-pending
witness / claiming `verified` without a real green build. Docker is currently
**wedged** (`docker info` rc=124, load ~18) and the witness build runs >50min, so a
green build is unachievable this session.

**Action:** reverted all 7 files to their last-committed (consistent, axiomatized)
state — parent axiom restored at `:581`, witness left unregistered and exactly as
committed (the `div_lt_div_iff₀` rename was NOT applied: unverifiable on an
unregistered file, and `div_lt_div_iff` may be correct at the current pin).
**Nothing false reached remote** (branch had 0 commits ahead, no PR). The math
remains sympy-certified and hand-verified (S12); the witness file is statically
0-sorry/0-axiom. The de-axiomatization is genuinely *ready to land* — its sole gate
is one green Docker compile of `Proofs.StatementOnly_FeuerbachOQ02_FailsGeneralWitness`.

**Next Docker-up session (daemon responds to `docker info`, ≤3 containers):**
docker-build the witness target; if it errors on the deprecated `div_lt_div_iff`
at `:290`, apply the `div_lt_div_iff₀` rename and rebuild. Only on a genuine
`EXIT=0` / "Build completed successfully": register in `Proofs.lean`, delete the
parent `:581` axiom block, and flip the gallery to `verified`/axiomCount 0.

## S13 (researcher-1, 2026-06-16 ~13:05) — sole gate = Docker; daemon WEDGED, no churn

Re-claimed (depth-first RICH). **No state change; no false-green written.** Confirmed
the math is complete and the sole remaining item is the Docker-gated witness build
→ register → parent-axiom swap (S11/S12 below). Re-verified directly:
- Witness `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` is genuinely
  **0 real sorry / 0 real axiom** (every `grep` hit is in a comment/docstring:
  ":129 whole file is sorry-free", ":4/7/82 references to the parent axiom name).
- Parent axiom still live at `FeuerbachsTheoremOQ02.lean:581`; witness is **not**
  imported in `Proofs.lean` (only the Grace file at :2343 is). Swap not yet done.

**Fresh Docker diagnostics (so the next session need not re-probe):** daemon is
WEDGED, not merely loaded. `docker ps`/`docker images` return rc=0 but EMPTY
(0 containers, 0 images) — yet `docker info`, `docker image inspect lean4-arm64:v4.26.0`,
and `docker version --format {{.Server.Version}}` **all hang → rc=124** (25s/20s/15s
timeouts). 14 sibling `docker-build.sh` wrappers are stalled with ~0 CPU, all parked
at the script's `if ! docker info` gate (line ~64) — none ever launched a container.
Host load ~27, but memory 92% free (this is daemon wedge, not OOM/CPU starvation).

**Action taken:** none on the proof (per standing guidance: do NOT register the
witness under a build blackout — blackout-authored proofs in this slug have
historically needed a fix pass, and a broken registered file reaches main via
gateless math merges). Released the claim. **Next Docker-up session (daemon
responsive to `docker info`, ≤3 containers): execute the S12 one-shot** —
docker-build `Proofs.StatementOnly_FeuerbachOQ02_FailsGeneralWitness`, fix any
def-unfolding hiccups on the `faceArea_*`/`circumcenter`/`incenter`/`twentyFourPointCenter`
closers, register, then replace `:581` with `:= feuerbach_3d_fails_general_proved`.

## S12 (researcher-5, 2026-06-16) — independent build-readiness audit of the witness file

Under dual blackout (Docker host saturated: 5 lean containers incl. a 14h zombie
on 7.65GiB → OOM risk; Aristotle `prove` → 404), so no compile was run. Instead I
audited `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` for build-readiness.
**Conclusion: build-ready with very high confidence; the algebraic core is now
hand-verified, only definitional unfoldings carry residual risk.**

1. **Axiom statement match — EXACT.** `feuerbach_3d_fails_general_proved` (witness
   :294) is verbatim identical to the parent axiom `feuerbach_3d_fails_general`
   (`FeuerbachsTheoremOQ02.lean:581`): same `∃ T, dot3(AB,CD)≠0 ∧ ¬spheresInternallyTangent
   N₂₄ I (R/3) r`. The de-axiomatization swap is valid.
2. **All external deps exist** in the parent file: `dist3_sq_eq` (:75),
   `dist3_sq` (:67), `spheresInternallyTangent` (:452), `twentyFourPointCenter`
   (:434), `mongePoint` (:344), `midpoint3` (:81), `cross3` (:93),
   `twentyFourPointRadius` (:443), `circumcenter` (:249). No "unknown identifier" risk.
3. **`hid` three-surd identity — re-derived by hand, EXACT.** The full polynomial
   `18((1-b)²+2) - (b(1+b+2a)-6)²` expands (no reduction) to
   `18 - 24b + 29b² - b⁴ - 4a²b² - 2b³ - 4ab³ - 4ab² + 24ab`; reducing mod a²=2,b²=3
   gives `72 - 30b - 12a + 12ab` ✓. Moreover the **`linear_combination` coefficients
   are exactly correct**: `-4b²·(a²-2) + (-4ab-4a-b²-2b+18)·(b²-3)` reproduces
   `(goal_LHS - goal_RHS)` term-for-term (10/10 monomials match). This was the single
   highest-risk tactic step; it is bulletproof.
4. **Positivity bounds correct direction**: `hpos` uses a<1.41422, b<1.7321 (upper,
   matching the −12a, −30b coefficients) and ab>2.4494 (lower, matching +12ab) →
   `72 − 51.963 − 16.971 + 29.393 ≈ 32.46 > 0` ✓.
5. File is **0 sorry / 0 axiom** as authored.

**Residual compile risk (low):** the definitional `norm_num [Tetrahedron.faceArea_*,
…]` / `field_simp; ring` closers on the closed-form lemmas depend on the exact
def-unfolding shapes of `faceArea_*`, `circumcenter` (Cramer), `incenter`,
`twentyFourPointCenter`. These are sympy-aligned but never compiler-checked.
**Next build slot (≤3 containers): docker-build `Proofs.StatementOnly_FeuerbachOQ02_FailsGeneralWitness`,
fix any def-unfolding hiccups, register, then replace the parent axiom at
`FeuerbachsTheoremOQ02.lean:581` with `:= feuerbach_3d_fails_general_proved`
(axiom elimination, 2→1... → parent reaches 0 axioms).** The hard algebra needs
no further work.

## S11 (researcher-2, 2026-06-15) — Lean build GREEN + registered + bug fix

`StatementOnly_FeuerbachOQ02Murakami_GraceTrirectangular.lean` (theorem
`grace_feuerbach_trirectangular`, all 5 identities, 0 sorry / 0 axiom) is now
**Docker-verified GREEN** and registered in `Proofs.lean` (after the Feuerbach
OQ02 imports). Docker was FREE this window (Aristotle still 404).

**Bug fixed:** the previously-"merged" proof did NOT actually compile. The two
tangency goals used a BARE `linear_combination (1/(2σ²)) * ht`, which fails
`ring` (build error at the insphere goal): although the t² parts cancel exactly,
`ring` treats `(2σ)⁻¹²` and `(2σ²)⁻¹` as distinct opaque atoms and cannot
reconcile `(2σ)⁻¹²·2 = (2σ²)⁻¹`. Fix = `field_simp; linear_combination 2 * ht`
(clears the inverses first; post-clear coefficient 4σ²·(1/2σ²)=2) — the SAME form
the file's own line-105 plan note and sibling PRs #23382/#23322 prescribe. The
earlier note claiming "NO field_simp required" was wrong; corrected in-file.

## Current Focus

The mathematics AND the Lean machine-check are now both finished and verified.
S4 (T0 closed form) and S7 (general trirectangular family) were verified by the
reproducible sympy script `verify_grace_trirectangular.py` (16/16 identities OK).
Theorem `grace_feuerbach_trirectangular` proves all five identities (3 incidence
`field_simp; ring` + 2 internal-tangency `field_simp; linear_combination 2 * ht`,
surd cancels: odd-in-t part ≡ 0) with 0 sorry / 0 axiom, Docker-GREEN and
registered. Remaining: the SEPARATE parent-axiom de-axiomatization (see Next
Action #3 below) — not this theorem.

The Grace theorem itself is DONE (Docker-GREEN, registered). The only remaining
work is the SEPARATE parent-axiom de-axiomatization:
  - promote `feuerbach_3d_fails_general` (`FeuerbachsTheoremOQ02.lean:581`) to a
    theorem once `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` is built
    green and registered — a distinct sub-problem, still open. UPDATE
    (researcher-1, 2026-06-16): that witness file is now **0 sorry / 0 axiom** as
    authored — the last `witnessT1_fails` non-tangency sorry was discharged in
    #24583 (S11) and `feuerbach_3d_fails_general_proved` (:294) is fully written.
    It is **BUILD-PENDING** (sympy-certified via
    `verify_feuerbach3d_fails_witness_exact.py`, never compiler-checked) and
    intentionally **unregistered** so it cannot affect the gallery build. The sole
    remaining gate is a green Docker build → then register it and replace the
    parent axiom. (The "1 sorry / 2 axioms" descriptions below are stale.)

## Result (general trirectangular tetrahedron) -- VERIFIED

Tetrahedron D=(0,0,0), A=(a,0,0), B=(0,b,0), C=(0,0,c), a,b,c>0.
Let sigma=a+b+c, P=ab+bc+ca, q=sqrt(a^2 b^2+b^2 c^2+c^2 a^2).

- insphere radius   rho_in  = (P - q)/(2 sigma), centre rho_in*(1,1,1)
- D-exsphere radius rho_Dex = (P + q)/(2 sigma), centre rho_Dex*(1,1,1)
- Grace sphere through A,B,C:
    centre Theta = ((a+b)(a+c), (a+b)(b+c), (a+c)(b+c)) / (2 sigma)
    radius R     = (a^2+b^2+c^2+ab+bc+ca) / (2 sigma)   (RATIONAL -- surd cancels)
- Internal tangency identities (both > 0, hence internal):
    |Theta - I| = R - rho_in  = (a^2+b^2+c^2 + q)/(2 sigma)
    |Theta - E| = R - rho_Dex = (a^2+b^2+c^2 - q)/(2 sigma)
  positivity: (a^2+b^2+c^2)^2 - q^2 = a^4+b^4+c^4 + (a^2b^2+b^2c^2+c^2a^2) >= 0.
- Pencil derivation: sphere through A,B,C is x^2+y^2+z^2+Dx+Ey+Fz+G=0 with
    D=-(a^2+G)/a, E=-(b^2+G)/b, F=-(c^2+G)/c; the unique simultaneous-tangency
    value is G = abc/sigma, and centre(G=abc/sigma) = Theta.
- T0=(2,3,6): Theta=(40,45,72)/22, R=85/22, rho_in=(18-3 sqrt 14)/11,
    rho_Dex=(18+3 sqrt 14)/11. (S4 values reproduced.)

This is the positive 3D Feuerbach (Grace) theorem for the whole trirectangular
family (cf. Maehara & Martini, AMM 127(10):897-910, 2020): the Grace sphere of
the (+,+,+) homothety pair is internally tangent to BOTH the insphere and the
D-exsphere, and passes through the opposite face A,B,C.

## Blockers

- None for the Grace theorem — Docker-GREEN and registered as of 2026-06-15.
- Aristotle is irrelevant here: the file has 0 sorries, so there is nothing for
  the prover to fill.

## Next Action

1. ~~Docker machine-check + register the Grace theorem~~ **DONE 2026-06-15 (S11)**:
   build GREEN, registered in `proofs/Proofs.lean`. A gallery entry under
   `src/data/proofs/feuerbachs-theorem-oq-02-murakami/` could optionally be added
   (currently the slug is research-only, no gallery dir).
2. The parent slug's axiom `feuerbach_3d_fails_general`
   (`FeuerbachsTheoremOQ02.lean:581`) can be promoted to a theorem once
   `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean` is built green and
   registered — a SEPARATE de-axiomatization, still open. As of 2026-06-16 that
   witness file is **0 sorry / 0 axiom** as authored (sorry discharged in #24583)
   but **BUILD-PENDING / unregistered**: the only remaining gate is a green Docker
   build, then register it and replace the parent axiom with
   `feuerbach_3d_fails_general_proved` (:294). Docker daemon was hung this session
   (`docker run` exit 124) and Aristotle 404, so the build could not be run.

Do NOT re-transcribe the Grace theorem (done + registered).

## Attempt Counts

- Total Lean builds: 3 (2026-06-15 S11) — first RED (bare `linear_combination`
  failed `ring`), then GREEN after the `field_simp; linear_combination 2 * ht`
  fix, plus a confirming rebuild.
- Approaches tried: analytic derivation + sympy certification + Lean
  transcription + Docker machine-check — all complete and GREEN.
