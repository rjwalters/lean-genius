# Current State

**Phase**: ACT (post-S13 STATE-SYNC; S12 BUILD-PENDING preserved)
**Since**: 2026-05-15 (S12 ACT first genuinely non-vacuous sufficient condition `(forget C) full + faithful + preservesMono → HasSBP C`, researcher-6), realises S10 PREP §3.2 Path D.i
**Iteration**: 13
**Last Updated**: 2026-05-16T16:50Z (S13 STATE-SYNC, researcher-10; absorbs S11 ACT #19424 + S12 ACT #19466 into head/Sessions/Drift; parent file 266→**353 LOC** post-S12 (corrects S12 head approx "~340 LOC"); 4-spot bearer drift recheck at pin `2df2f0150c...` v4.26.0, 0 drift; **B1 host disk full at 141Mi partially recovered (now 6.9Gi avail) → SUPERSEDED BY NEW B2 Docker daemon hung** (8s `docker version` timeout, no response); BUILD-VERIFY still blocked but by different blocker. S14 BUILD-VERIFY rotation queued for post-B2-recovery picker)

## Current Focus

Through S12 the slug now has a **six-theorem pos/neg corpus**
for the categorical Schroeder–Bernstein predicate `HasSBP` in
`proofs/Proofs/SchroederBernsteinOQ01.lean` (now ~340 LOC,
6 public theorems, 0 sorries, 0 axioms, **build pending on S12**).

| Stage | Category | Theorem | Sign | Vacuous? | Build | Anchor PR |
|---|---|---|---|---|---|---|
| S2/S3 ACT | `Type u` | `hasSBP_Type` | + | non-vacuous (Mono = Injection ≠ Iso) | verified | #18383 |
| S4 ACT    | `Discrete α` | `hasSBP_Discrete` | + | vacuous (every morph is iso) | verified | #18496 |
| S5 ACT    | `TopCat.{0}` | `not_hasSBP_TopCat` | − | n/a (refutation) | verified | #18707 |
| S6 ACT    | abstract `[IsDiscrete C]` | `hasSBP_of_isDiscrete` | + | vacuous (every morph is iso) | verified | #19086 |
| S11 ACT   | abstract `[IsGroupoid C]` | `hasSBP_of_isGroupoid` | + | vacuous-but-broadening | verified | #19424 |
| **S12 ACT** | **fully-faithful concrete `(forget C)`** | **`hasSBP_of_fullFaithful_forget`** | + | **NOT vacuous (narrow: forces C ≈ full subcat of Type)** | **pending** | **this PR** |

S12 ACT is the **first genuinely non-vacuous** sufficient condition
in the corpus: under `[HasForget C][(forget C).Full][(forget C).Faithful]
[(forget C).PreservesMonomorphisms]`, the proof admits non-iso
C-monos (e.g. on `Type u`, `Set.Subtype.val : { n // n ∈ s } ↪ ℕ`)
and lifts the classical Schroeder–Bernstein `Function.Embedding.antisymm`
in `Type` through the fully-faithful forgetful via
`Functor.FullyFaithful.ofFullyFaithful (forget C) |>.preimageIso e.toIso`.

The S12 hypothesis is non-vacuous but **narrow**: `(forget C).Full`
essentially forces `C` to be a full subcategory of `Type` (S8 PREP
§4 catalogue: `Type u`, `Discrete α`, and similar Type-like
instances qualify; `Grp`, `TopCat`, `Ring`, `ModuleCat` etc. all
fail the fullness clamp). Concrete instance space: `Type u`,
`Discrete α`, full subcategories of `Type`.

**Sanity vs S5**: `TopCat` lacks `(forget TopCat).Full` — continuous
maps form a proper subset of underlying functions — so
`not_hasSBP_TopCat` survives.

The next horizon (S13+) is the **non-vacuous-AND-broad** target:
Path D.ii abstract orbit construction (~150-250 LOC, per S10 PREP
§3.3) or Path E Banaschewski–Brümmer 1986 retraction condition
(~150-300 LOC, per S10 PREP §3.4 — long-horizon, requires
`MorphismProperty.Factorisation` API). The "complete characterization"
half of the open question is a research-level survey goal (S20+
ANALYSIS), not a near-term Lean target.

## Active Approach

**Four-theorem corpus + non-vacuous sufficient-condition follow-up.**

1. ✅ **Define** `HasSchroederBernsteinProperty (C : Type*) [Category C]` as
   `∀ X Y, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)`.
2. ✅ **Instantiate (positive)** in `Type u` via `Function.Embedding.antisymm`
   bridged through `CategoryTheory.mono_iff_injective` (PR #18383, build verified).
3. ✅ **Instantiate (positive)** in `Discrete α` via Discrete-category-is-iso
   reduction (PR #18496, build verified post-S6 BUILD UNBLOCKER).
4. ✅ **Refute (negative)** in `TopCat.{0}` via the [0,1] vs (0,1)
   compactness obstruction with explicit compression maps `fHom`, `gHom`
   (PR #18707, build verified post-S6 BUILD UNBLOCKER).
5. ✅ **Vacuous sufficient condition** (S6 ACT, this PR): every
   `[IsDiscrete C]` category satisfies SBP via the more abstract
   `hasSBP_of_isDiscrete : [IsDiscrete C] → HasSBP C`. Generalizes
   `hasSBP_Discrete` beyond `C = Discrete α` to any Mathlib `IsDiscrete`
   instance (e.g., the discrete subcategory `Discrete C` of any category,
   per `Discrete.isDiscrete`). The proof is one line (`asIso m`) using
   Mathlib's `isIso_of_isDiscrete`. Documented as **vacuous** (hypothesis
   forces `Mono = Iso`).
6. ⏳ **Non-vacuous sufficient condition** (S7+): some hypothesis `P` on
   `C` with `P C → HasSBP C` AND `P` does NOT force every mono to be iso.
   Candidates per S6 ACT docstring: regular-mono variants (RegularMono /
   StrongMono), groupoid reductions of monoidal slices,
   Banaschewski–Brümmer 1986 retraction condition. Sanity constraint:
   any chosen `P` must exclude `TopCat` (since `P TopCat → HasSBP TopCat`
   contradicts `not_hasSBP_TopCat`).
7. ⏳ **First non-vacuous-broadening sufficient condition** (S10+ ACT,
   per S10 PREP STATE-SYNC §3 + §4):
   - **Path C — `[IsGroupoid C]`**: ~5-10 LOC, vacuous-corpus-expanding
     (same sense as `[IsDiscrete C]`), `IsGroupoid.all_isIso` makes
     every morph iso. ACT-ready GREEN per S10 §4. Skeleton in S10 §3.1.
   - **Path D.i — fully-faithful concrete**: ~25-35 LOC (S8-revised
     from S7's 100-200), genuinely **non-vacuous but narrow** (forces
     C ≈ full subcategory of Type via `(forget C).Full` clamp).
     ACT-ready GREEN per S10 §4. Skeleton in S10 §3.2 (lifted
     verbatim from S8 §3).
   Both ACT-ready; recommended order C → D.i. Both can be picked up
   by the same researcher in two sequential PRs. Negative corpus
   expansion `not_hasSBP_AddCommGrpCat` (~245-400 LOC, S9 §6) deferred
   past S10. problem.md S3 §2 line 70 amendment (S9 §8 Path (ii))
   recommended but deferred to doctor/auditor or next STATE-SYNC.

## Blockers

**B2 (NEW, S13 STATE-SYNC, 2026-05-16T16:50Z, researcher-10) — Docker
daemon hung; supersedes B1 for BUILD-VERIFY purposes.**
`timeout 8 docker version --format '{{.Server.Version}}'` gives no
response within 8 seconds (killed by timeout). `docker ps -a` returns
empty (0 containers). Host disk has partially recovered (B1's
141Mi → 6.9Gi avail at S13 STATE-SYNC-time, still 100% used capacity
overall), but the Docker daemon does not respond even to read-only
health-check commands — so `./proofs/scripts/docker-build.sh
Proofs.SchroederBernsteinOQ01` cannot proceed. **Wait-for-recovery**;
do NOT run `docker system prune` (would risk losing whatever cache
state is recoverable when the daemon comes back). Matches research
trap pattern
`_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`
(Docker CLI hangs while disk is non-extreme — distinct from
`_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`
which requires ≤200Mi avail + `ld.lld I/O error`). Recommended next
picker action: post-B2 recovery, run S14 BUILD-VERIFY rotation
(~3069-3080 jobs forecast per S8 PREP §6 / S12 ACT memo §6); update
state.md head to clear B1 + B2 and mark S12 verified.

**B1 (S12 ACT, 2026-05-16T04:30Z, researcher-6) — host disk full at
141Mi → partially recovered to 6.9Gi at S13 STATE-SYNC-time, SUPERSEDED
BY B2.** S12 ACT (PR #19466, researcher-6) Docker build attempt failed
with `Input/output error` writing the cache:exe binary; host
`/dev/disk3s1s1` at 141Mi free / 100% used capacity at that time.
The Lean code is independently grounded by the live v4.26.0 Mathlib API
audit (S8 PREP §1.1–§1.5; every bearer pinned at lake SHA `2df2f015...`
in S12 ACT's sessions memo §2; re-spotchecked in S13 STATE-SYNC
sessions memo §2 with 0 drift on 4 spots). Follows the S5 ACT pattern
(PR #18707, cleared by S6 BUILD UNBLOCKER PR #18980). The disk has
since recovered ~6.7Gi (S13 STATE-SYNC-time disk-snapshot table in
session memo §3); the BUILD-VERIFY blocker that remains is B2 (daemon
hang), not B1 (disk extreme). **Mathematically non-blocking for
downstream work** — every theorem with build-verified status remains
so, and the new S12 theorem fails-shut (i.e. if the build discovers
an error, the next iteration ships a small fix; no cascading risk).

**Build verification CLEARED for S2/S3/S4/S5/S6/S11** (S6 BUILD UNBLOCKER
2026-05-13 22:55Z; S11 ACT 2026-05-16T04:40Z):
- S2/S3 (`hasSBP_Type`) — verified at PR #18383.
- S4 (`hasSBP_Discrete`) — verified post-S6 BUILD UNBLOCKER (PR #18980).
- S5 (`not_hasSBP_TopCat`, `fHom`, `gHom`, `fHom_injective`,
  `gHom_injective`) — verified post-S6 BUILD UNBLOCKER (PR #18980).
- S6 (`hasSBP_of_isDiscrete`) — verified at PR #19086 (3069 jobs).
- S11 (`hasSBP_of_isGroupoid`) — verified at PR #19424 (3069 jobs).
- **S12 (`hasSBP_of_fullFaithful_forget`) — PENDING** (B1 partial-recovery → B2 daemon-hang).

S6 BUILD UNBLOCKER detail: pre-claim Docker build of
`Proofs.SchroederBernsteinOQ01` at origin/main `893e29b7d7b` surfaced one
error: line 103 `fHom` defined via `(x+1)/4` (real division) needs
`noncomputable`. Applied 2-token fix (`def → noncomputable def` on
`fHom` and `gHom`), re-built: `✔ [3069/3069] Built
Proofs.SchroederBernsteinOQ01 (3.5s)`. The S4 ACT (PR #18496) and S5 ACT
(PR #18707) build-pending annotations are now mathematically verified
— the shipped Lean compiled clean once this oversight was patched.
See sessions/2026-05-13-s6-build-unblocker... for the full diagnosis.

**No current mathematical blocker** for the S6 follow-up. The proof
of `[HasSplitMonos C] → HasSBP C` is short *if* one accepts the
collapse `Mono = Iso`. The literal Banaschewski-Brümmer 1986 result
is more nuanced (involves extremal / regular monos, or a
slice-category reformulation); the S6 researcher should reread the
1986 paper before fixing the hypothesis shape.

## Next Action

**S14 BUILD-VERIFY rotation (RECOMMENDED FIRST FOR NEXT PICKER,
post-B2-recovery; queued at S13 STATE-SYNC, 2026-05-16T16:50Z,
researcher-10)**: once the Docker daemon responds again (B2 cleared
— wait for natural recovery or e.g. host reboot /
`launchctl kickstart -k system/com.docker.*` / Docker Desktop restart),
run `./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01`
and confirm S12 (`hasSBP_of_fullFaithful_forget`) builds clean.
Expected: 3069 ≤ count ≤ 3080 jobs (per S8 PREP §6 + S12 ACT memo §6
forecasts). On success: update state.md head + Sessions to mark S12
build-verified; clear B1 + B2 from Blockers; bump iteration 13 → 14
(or roll into next ACT). If Docker daemon recovers AND build is clean,
the corpus is **slug-wide 6 public theorems / 0 sorries / 0 axioms /
0 structure-encoded assumptions, all build-verified** — trigger
Auditor + Hermit follow-up batch (badge eligibility, lint sweep,
companion file `additionalFiles` cross-ref enrichment) at that point.

ACT-readiness gate for S14 (from S13 STATE-SYNC memo §11): 7/8 GREEN
+ 1 RED (B2 daemon hang). Lean source unchanged, Mathlib pin
unchanged, bearer drift 0, S2/S3/S4/S5/S6/S11 already verified,
forecast 3069-3080 jobs, recipe is a verbatim apply of S10 PREP §3.2
+ S8 PREP §3 + S8 PREP §1.1-§1.5 audit; only daemon-hang is blocking.

**S12 ACT — Path D.i SHIPPED, BUILD PENDING** (PR #19466, researcher-6,
2026-05-16T04:30Z, merged 2026-05-16T08:54Z): Added `hasSBP_of_fullFaithful_forget : ∀ (C : Type*)
[Category C] [HasForget C] [(forget C).Full] [(forget C).Faithful]
[(forget C).PreservesMonomorphisms], HasSBP C` (~12 LOC tactic
body + ~60 LOC prose docstring; parent file 266→~340 LOC). 6th
positive instance in the corpus and **first genuinely non-vacuous**.
Tactic: lift C-monos to Type-injections via `(forget C).PreservesMonomorphisms`
+ `mono_iff_injective`, apply `Function.Embedding.antisymm` for the
classical Schroeder–Bernstein in Type, then lift the Type-equivalence
back to a C-iso via `Functor.FullyFaithful.ofFullyFaithful (forget C)
|>.preimageIso e.toIso`. Two new imports: `Mathlib.CategoryTheory.ConcreteCategory.Basic`
+ `Mathlib.CategoryTheory.ConcreteCategory.EpiMono`.

**Build pending caveat (updated S13 STATE-SYNC)**: Docker build
attempted at S12 ACT-time (2026-05-16T04:30Z) but host disk exhausted
(141Mi free / 100% used `/dev/disk3s1s1`, Docker containerd metadata
corrupted on first attempt). As of S13 STATE-SYNC-time (2026-05-16T16:50Z)
the disk has freed ~6.7Gi (now 6.9Gi avail), but the **Docker daemon
is now hung** (B2; supersedes B1). Following the S5 ACT precedent
(PR #18707, "build pending" cleared by S6 BUILD UNBLOCKER PR #18980),
shipping the Lean code with the build-pending annotation; mechanic /
next-rotation auditor / next researcher with Docker daemon health AND
disk headroom runs `./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01`
once daemon recovers. The proof structure is independently grounded by
the live v4.26.0 Mathlib API audit in S8 PREP §1.1–§1.5 (every
bearer cited inline by file:line and re-verified at lake SHA
`2df2f015...` for this S12 ACT, plus 4-spot re-spot at S13 STATE-SYNC,
0 drift). Forecast: ~3069–3080 jobs (S6 baseline ≤ count ≤ S6 baseline
+ 11 if `ConcreteCategory/EpiMono` adds new transitive deps; per S8
PREP §6 forecast).

**S13 ACT (any researcher) — Path D.ii or Path E (DEFERRED LONG-HORIZON)**:

- **Path D.ii — abstract orbit construction** (~150-250 LOC, per
  S10 PREP §3.3): genuinely non-vacuous AND broader than D.i;
  requires Bernstein-orbit recursion in pure category theory. No
  Mathlib precedent identified.
- **Path E — Banaschewski-Brümmer 1986 literal** (~150-300 LOC,
  per S10 PREP §3.4): requires `MorphismProperty.Factorisation`
  API navigation; S7 §2.3 flagged RED for Mathlib API auditability.
- **`not_hasSBP_AddCommGrpCat` corpus expansion** (~245-400 LOC,
  S9 §6): blocked on problem.md S3 §2 line 70 amendment from S9 §8
  Path (ii).

~~Recommended near-term: a STATE-SYNC absorbing the S11 ACT (#19424)
and this S12 ACT, then BUILD-VERIFY rotation post-disk-recovery,
then a Path E feasibility re-scoping PREP if D.ii is judged too
speculative.~~

**S13 STATE-SYNC SHIPPED** (this PR, researcher-10, 2026-05-16T16:50Z):
the first half of the above recommendation. State.md head + Sessions
+ Drift + Blockers absorb the S11 ACT (#19424) and S12 ACT (#19466)
deltas; 4-spot bearer drift recheck at unchanged pin `2df2f015...`
(0 drift). The BUILD-VERIFY rotation is **queued as S14** (see top of
this section) — re-blocked by NEW B2 (Docker daemon hung) which
supersedes the recovered B1 (host disk no longer at 141Mi extreme;
now 6.9Gi). Path E feasibility re-scoping PREP remains deferred to
S15+ post-S14 BUILD-VERIFY clearance.

~~**S12 BUILD-PENDING follow-up (RECOMMENDED FIRST FOR NEXT PICKER)**:~~
Superseded by S14 BUILD-VERIFY rotation (above) — same intent, refreshed
blocker chain (B1 partial-recovery + NEW B2 daemon-hang).

Legacy three-path catalogue (preserved for reference):

- **(C) Groupoid / `IsGroupoid C`.** Add `import Mathlib.CategoryTheory.Groupoid`
  and prove `[IsGroupoid C] → HasSBP C` (~5 LOC, identical proof
  pattern as `hasSBP_of_isDiscrete` since `IsGroupoid.all_isIso` makes
  every morph iso). **Still vacuous in the same sense** (forces
  `Mono = Iso`), but expands the formal scope to non-Discrete groupoid
  examples like `EssGroupoid` and fundamental groupoids. Cheap and
  factual; ship if a low-cost broadening is desired.

- **(D) Regular-mono variant.** Use Mathlib's `RegularMono` and state
  the weaker hypothesis "every mono is regular and split", which
  avoids the `Mono = Iso` collapse. The proof sketch: given m mono +
  regular (so m is the equalizer of some pair) + split (with section
  s), use the equalizer universal property + s ≫ m = 𝟙_Y to derive
  m ≫ s = 𝟙_X. ~30-50 LOC. Requires deeper API navigation through
  `Mathlib.CategoryTheory.Limits.Shapes.RegularMono`.

- **(E) Banaschewski-Brümmer 1986 literal.** The original paper uses
  a "retraction condition" expressed in terms of factorisation systems
  (extremal / regular monos + epi factorisation). Formalising at the
  Mathlib pin requires familiarity with `MorphismProperty` and
  `Mathlib.CategoryTheory.MorphismProperty.Factorisation`. ~150-300 LOC.

Path (C) is recommended for S7 as a 1-PR low-cost broadening of the
S6 vacuous regime. Path (D) is recommended for S8 as the first genuine
non-vacuous result. Path (E) is the long-horizon goal aligning with
the literature.

The S5 TopCat counterexample remains the sanity check across all
three: any chosen hypothesis `P` must *exclude* `TopCat` (since
`P TopCat → HasSBP TopCat` would contradict `not_hasSBP_TopCat`).
For path (C), this is automatic — `TopCat` is not a groupoid. For
paths (D, E), the exclusion must be verified by hand or via a
`P TopCat → False` proof.

Skeleton for path (C):

```lean
import Mathlib.CategoryTheory.Groupoid

namespace SchroederBernsteinOQ01
open CategoryTheory

theorem hasSBP_of_isGroupoid (C : Type*) [Category C] [IsGroupoid C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩
-- Substantive work: `IsGroupoid.all_isIso : IsIso f` (auto-applied
-- via `attribute [instance]` in `Mathlib.CategoryTheory.Groupoid`).

end SchroederBernsteinOQ01
```

Estimated S7 LOC: ~10 (path C), ~40-60 (path D), ~150-300 (path E).

## Sessions

- S1 (2026-05-12, researcher-8): OBSERVE — three doc files + JSON
  entry. No Lean changes. Phase NEW → OBSERVE.
- S2/S3 (2026-05-12, researcher-1): ACT — `SchroederBernsteinOQ01.lean`
  (~60 LOC, 1 def + 1 theorem, no sorries, no axioms). Phase OBSERVE →
  ACT. See `sessions/2026-05-12-s2-act-type-u-bridge.md`.
- S4 PREP (2026-05-12, researcher-7): doc-only `HasSBP (Discrete α)`
  tractable second-instance design memo. PR #18428.
- S4 ACT (2026-05-13, researcher-?): `hasSBP_Discrete` instance via
  Discrete-category-is-iso reduction. PR #18496 (build pending).
- S5 PREP (2026-05-13, researcher-?): `¬ HasSBP TopCat` design memo —
  [0,1] vs (0,1) compactness counterexample. PR #18450.
- S5b PREP (2026-05-13, researcher-?): TopCat coercion ritual audit,
  closes 4 honesty caveats from S5 PREP. PR #18508.
- S5c PREP (2026-05-13, researcher-3): final S5 ACT preflight, locks
  Step-5 `isCompact_iff_isCompact_univ` + `TopCat.ofHom` + complete
  compression-map bodies. PR #18602.
- S5d PREP (2026-05-13, researcher-?): citation line-drift audit on
  S5b/S5c PREP — 4 lemmas off by 1-46 lines (names resolve, no
  build impact). PR #18655.
- S5e PREP (2026-05-13, researcher-9): substantive audit-correction on
  S5c PREP §3.5 injectivity proofs — phantom `Subtype.mk.inj_iff` +
  missing `simp [fHom]` argument; supplies §4 verbatim drop-in.
  PR #18673.
- **S5 ACT** (2026-05-13, researcher-1): ACT — adds `fHom`, `gHom`,
  `fHom_injective`, `gHom_injective`, `not_hasSBP_TopCat` to
  `SchroederBernsteinOQ01.lean` (+~55 LOC; 2 private defs + 3 private
  theorems + 1 public theorem; 0 sorries, 0 axioms). **Build pending**
  — worktree `.lake` symlink loop precludes local verification;
  doctor/mechanic runs `docker-build.sh Proofs.SchroederBernsteinOQ01`.
  Uses S5e PREP §4's `simp [fHom]` / `simp [gHom]` injectivity forms.
- **S6 BUILD UNBLOCKER** (2026-05-13, researcher-12): single-file Lean
  fix — `private def fHom/gHom` → `private noncomputable def fHom/gHom`
  (2-token fix, real-division dependency from `(x+1)/4` requires
  `noncomputable`). Docker build now passes: `✔ [3069/3069] Built
  Proofs.SchroederBernsteinOQ01 (3.5s)`. Closes build-pending
  annotations on S4 ACT (PR #18496) and S5 ACT (PR #18707) — the
  shipped Lean was correct modulo this `noncomputable` oversight.
  Pattern: `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md`
  (in-PR one-line unblocker). Discovered via pre-claim Docker build
  per new memory `feedback_researcher_docs_only_chain_silent_parent_regression.md`
  (introduced this session at nth-root-irrational-oq-03 PR #18978).
  See `sessions/2026-05-13-s6-build-unblocker-noncomputable-fhom-ghom.md`
  for full diagnosis.
- **S6 ACT** (2026-05-14, researcher-9): ACT — adds
  `hasSBP_of_isDiscrete : (C : Type*) [Category C] [IsDiscrete C] → HasSBP C`
  to `SchroederBernsteinOQ01.lean`. Generalizes `hasSBP_Discrete`
  beyond `C = Discrete α` to any Mathlib `IsDiscrete` instance.
  Proof is one tactic-line (`exact ⟨asIso m⟩`) using Mathlib's
  `isIso_of_isDiscrete` instance at `Mathlib/CategoryTheory/Discrete/Basic.lean:342`
  (pinned SHA `2df2f01`). +~40 LOC (33 docstring lines + 7 theorem lines).
  Docker build verified: `✔ [3069/3069] Built Proofs.SchroederBernsteinOQ01 (5.8s)`
  in 1 iteration. Pre-claim Docker baseline also clean (same 3069
  jobs). Phase remains ACT; iteration bumped 6 → 7. Documents the
  hypothesis as **vacuous** (forces Mono = Iso) and points the S7
  picker at three candidate paths for non-vacuous follow-up: IsGroupoid
  (~5 LOC), RegularMono variant (~30-50 LOC), or full Banaschewski-Brümmer
  factorisation system (~150-300 LOC). See
  `sessions/2026-05-14-s6-act-vacuous-sufficient-condition-isdiscrete.md`.
- **S7 PREP** (2026-05-14, researcher-?): doc-only paths-C/D/E
  feasibility audit at v4.26.0. Per-path Mathlib API verification +
  LOC estimates (C: 5-10, D.i: 100-200 (S8-revised to 25-35),
  D.ii: 150-250, E: 150-300). Sequencing recommendation:
  C → D.i → D.ii → E. PR #19158.
- **S8 PREP** (2026-05-15, researcher-9): doc-only path-D.i refinement.
  Refines hypothesis from S7's `[SplitMonoCategory C][ConcreteCategory C]`
  to S8's `[ConcreteCategory C][(forget C).Full][(forget C).Faithful]
  [(forget C).PreservesMonomorphisms]`. LOC estimate revised
  100-200 → 25-35. Path-D.i admitted as narrow (forces C ≈ full
  subcategory of Type) but non-vacuous. PR #19196.
- **S9 PREP** (2026-05-15, researcher-3): doc-only `Grp` /
  `AddCommGrpCat` counterexample feasibility audit. **Falsifies
  problem.md S3 §2 line 70** (`(ℤ, ℤ × ℤ/2ℤ)` pair: no injective
  group hom `ℤ × ℤ/2ℤ → ℤ` exists since ℤ is torsion-free; the
  `(0,1)` torsion element is killed under any hom into ℤ).
  Supplies corrected candidate in `AddCommGrpCat` via Ulm-invariant
  separation (~245-400 LOC for S10+ ACT). Recommends doctor/auditor
  amendment of problem.md line 70 (deferred). PR #19259.
- **S10 PREP STATE-SYNC** (2026-05-15, researcher-9): catches
  state.md from iteration 7 → 10 after the S6/S7/S8/S9 drain wave.
  Per-path ACT-readiness gate at lake SHA `2df2f015...` (5
  critical bearers re-verified at unchanged SHA; 0 drift). Path C
  (`[IsGroupoid C]`, ~5-10 LOC, vacuous-broadening) and Path D.i
  (`[ConcreteCategory C][(forget C).Full][(forget C).Faithful]
  [(forget C).PreservesMonomorphisms]`, ~25-35 LOC, narrowly
  non-vacuous) are both **GREEN ACT-ready**. Recommended order:
  C → D.i. Path D.ii / Path E / `not_hasSBP_AddCommGrpCat`
  deferred past S10 (LOC scope or Mathlib audit). problem.md
  line 70 amendment recap (S9 §8 Path (ii)) — deferred to next
  picker. PR #19369.
- **S11 ACT** (2026-05-16, researcher-5, PR #19424): realises S10
  PREP §3.1 Path C — adds `hasSBP_of_isGroupoid : ∀ (C : Type*)
  [Category C] [IsGroupoid C], HasSBP C` to
  `SchroederBernsteinOQ01.lean`. Broadens `hasSBP_of_isDiscrete`
  (S6 ACT) from at-most-one-Hom categories to all groupoids via
  Mathlib's `IsGroupoid.all_isIso` instance
  (`Mathlib.CategoryTheory.Groupoid:119` registered global at line
  121, pinned SHA `2df2f015...`). One-line proof body (`exact
  ⟨asIso m⟩`), structurally identical to `hasSBP_Discrete` /
  `hasSBP_of_isDiscrete`. +56 LOC (parent 210→266; 1 new theorem
  +5-line body + ~30 docstring lines + 1 import + ~20-line section
  preamble + header docstring §S11 ACT block). Vacuous (still forces
  Mono = Iso) but broadens the corpus to fundamental groupoids,
  Brandt groupoids, `EssGroupoid`, action groupoids. Sanity vs S5:
  `TopCat` is not a groupoid; `not_hasSBP_TopCat` survives.
  Bearer pin recheck: 0 drift (S10 §1.2 row 5 re-verified). Phase
  remains ACT; iteration 10 → 11. Docker build verified:
  `✔ [3069/3069] Built Proofs.SchroederBernsteinOQ01 (6.1s)`
  (identical job count to S6 ACT baseline; Groupoid import
  transitively present per S10 PREP §3.1 forecast). Next picker:
  S12 Path D.i (first genuinely non-vacuous, ~25-35 LOC).
  See `sessions/2026-05-15-s11-act-isgroupoid.md`.
- **S12 ACT** (2026-05-16, researcher-6, PR #19466): realises S10
  PREP §3.2 Path D.i — adds `hasSBP_of_fullFaithful_forget : ∀ (C :
  Type*) [Category C] [HasForget C] [(forget C).Full] [(forget C).Faithful]
  [(forget C).PreservesMonomorphisms], HasSBP C` to
  `SchroederBernsteinOQ01.lean`. **First genuinely non-vacuous**
  sufficient condition: hypothesis admits non-iso C-monos (witness
  on `Type u`: `Set.Subtype.val : { n // n ∈ s } ↪ ℕ`). Proof
  structure (12-line tactic body): lift C-monos to Type-injections
  via `(forget C).PreservesMonomorphisms` + `mono_iff_injective`,
  apply `Function.Embedding.antisymm`, then lift the Type-equiv back
  to a C-iso via `(Functor.FullyFaithful.ofFullyFaithful (forget C)).preimageIso e.toIso`.
  Narrow: `(forget C).Full` forces C ≈ full subcategory of Type (per
  S8 PREP §4 catalogue; `Grp` / `TopCat` / `Ring` / `ModuleCat` all
  fail the fullness clamp). +87 LOC (parent 266→**353**, S12 head's
  approx "~340 LOC" undershoots actual by ~13). Two new imports:
  `Mathlib.CategoryTheory.ConcreteCategory.Basic` + `EpiMono`. Bearer
  pin re-verification: 10 bearers, 0 drift at pin `2df2f015...`
  (S12 memo §2). Phase remains ACT; iteration 11 → 12. **BUILD
  PENDING — B1 host disk full at 141Mi** (containerd metadata
  corrupted on first attempt; following S5 ACT precedent PR #18707).
  See `sessions/2026-05-15-s12-act-path-Di-fullfaithful-forget.md`.
- **S13 STATE-SYNC** (this PR, 2026-05-16, researcher-10): absorbs
  S11 ACT (#19424) and S12 ACT (#19466) into state.md head +
  Sessions + Drift / parent state + Blockers. **No Lean / meta.json
  / problem.md / knowledge.md edits** (pure doc-only catch-up).
  4-spot bearer drift recheck at unchanged pin `2df2f015...` on
  `preimageIso` (FullyFaithful.lean:197), `mono_iff_injective`
  (Types/Basic.lean:242), `HasForget` (ConcreteCategory/Basic.lean:73),
  `Function.Embedding.antisymm` (SchroederBernstein.lean:97) — **0
  drift** on all 4. Host snapshot: disk recovered 141Mi→6.9Gi (still
  100% used capacity overall), but **Docker daemon hung** (8s
  `docker version` timeout, no response; 0 containers running).
  **B1 host-disk-full SUPERSEDED BY NEW B2 Docker-daemon-hung**;
  BUILD-VERIFY still blocked but by different blocker (B1 partially
  recovered, B2 introduced). S14 BUILD-VERIFY rotation queued for
  post-B2-recovery picker (7/8 GREEN + 1 RED ACT-readiness gate per
  S13 memo §11). Phase remains ACT (S13 is doc-only catch-up, not a
  new ACT); iteration 12 → 13. See
  `sessions/2026-05-16-s13-statesync-s11-s12-catchup.md`.

## Drift / parent state

- Parent `Proofs/SchroederBernstein.lean` is **verified** (0 sorries,
  0 axioms, 5 theorems, 3 definitions, 198 LOC, Wiedijk #25 ✓).
- Parent `meta.json` does **not** yet list `SchroederBernsteinOQ01.lean`
  in `additionalFiles`; cross-reference update is deferred to a later
  enrichment / auditor PR (does not block S7).
- OQ-02 (Knaster-Tarski variant), OQ-03 (Myhill computability), OQ-04
  (dual SBP for surjections) are independent and have their own Lean
  files (`SchroederBernsteinOQ02.lean`, `OQ03`, `OQ04`).
- Companion file `Proofs/SchroederBernsteinOQ01.lean` post-S12 ACT
  (verified counts at S13 STATE-SYNC, 2026-05-16T16:50Z):
  **353 LOC**, **6 public theorems** (`hasSBP_Type` S2/S3,
  `hasSBP_Discrete` S4, `not_hasSBP_TopCat` S5, `hasSBP_of_isDiscrete`
  S6, **`hasSBP_of_isGroupoid` S11**, **`hasSBP_of_fullFaithful_forget`
  S12**), 1 def (`HasSBP`), 2 private noncomputable defs (`fHom`,
  `gHom`), 2 private theorems (`fHom_injective`, `gHom_injective`),
  **0 tactic sorries, 0 axioms, 0 structure-encoded assumptions**.
  Build status: S2/S3/S4/S5/S6/S11 verified at 3069 jobs (PRs #18383,
  #18496, #18707, #18980, #19086, #19424); **S12 BUILD PENDING** (B2
  Docker daemon hung supersedes recovered B1 host disk 141Mi).
  LOC drift trail: 210 (post-S6 ACT) → 266 (post-S11 ACT, +56) →
  353 (post-S12 ACT, +87).
