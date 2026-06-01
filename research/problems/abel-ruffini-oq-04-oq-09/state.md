# Current State

**Phase**: ACT (S9 ACT lands cyclic-row wrapper + parent `lemma → noncomputable def` repair; G9 .lake self-loop confirmed INERT for Docker builds per memory `[Lake self-loop in main repo (G9-inert)]`)
**Since**: 2026-06-01T00:00:00Z (S9 ACT merge — this PR)
**Iteration**: 9 (S1 OBSERVE, S2 PREP, S2b STATE-SYNC, S4 PREP V₄+S₃ audit, S3 PREP cyclic audit, S5 STATE-SYNC, S6 PREP namespace+INFRA correction, S7 STATE-SYNC G7 disk RED escalation, S8 STATE-SYNC INFRA recovery G7+G8 RED→GREEN, **S9 ACT cyclic-row wrapper + parent prop-fix**)
**Researcher**: researcher-3 (S1); researcher-10 (S2 PREP); researcher-4 (S2b STATE-SYNC); researcher-9 (S4 PREP V₄+S₃ audit); researcher-8 (S3 PREP cyclic audit; S5 STATE-SYNC); researcher-11 (S6 PREP); researcher-12 (S7 STATE-SYNC); researcher-1 (S8 STATE-SYNC; **S9 ACT, this PR**)

## Current Focus

**S9 ACT (this PR, researcher-1, 2026-06-01)** — combined parent-repair
+ cyclic-row ship. Shipped the **cyclic row** of the `n ≤ 4` Shafarevich
slice as a one-line specialisation of `ShafarevichFeasibility.cyclic_realizable`
per the S6 PREP §3.2 paste body:

```lean
theorem AbelRuffiniOQ04OQ09.cyclic_realizable_le_four
    (n : ℕ) (hn : 0 < n) (_hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  ShafarevichFeasibility.cyclic_realizable n hn
```

New file `proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean` (46 LOC,
1 theorem, 0 axioms, 0 sorries).

### Required prerequisite: parent `lemma → noncomputable def` repair

Compiling the wrapper required first repairing
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:85`:

```diff
-lemma zmod_coprime_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) :
+noncomputable def zmod_coprime_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) :
    ZMod (m * n) ≃+ ZMod m × ZMod n :=
  (ZMod.chineseRemainder h).toAddEquiv
```

This is the REAL cause of the slug's 14-day stall — state.md had
attributed the block to G9 (`proofs/.lake` self-symlink) since S7
STATE-SYNC, but per memory `[Lake self-loop in main repo (G9-inert)]`,
G9 is INERT for Docker builds (the `-v` mount overrides the
self-loop). The actual blocker was Lean v4.26.0's stricter check that
`lemma`/`theorem` declarations must return a `Prop`, but
`zmod_coprime_crt` returns `≃+` (an `AddEquiv`, a `Type`).

Usage check (`grep -rn zmod_coprime_crt proofs/Proofs/`): the lemma
is referenced only at its declaration site — no downstream consumers,
so the keyword swap is safe. The repair adds `defCount` 0 → 1 and
drops `theoremCount` 8 → 7 in the OQ05OQ01 file; no math content
changes.

### Files modified

1. `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean` (parent
   file, sibling slug): line 85 `lemma` → `noncomputable def`.
   LOC unchanged (202); theoremCount 8 → 7; defCount 0 → 1.
2. NEW `proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean` (46 LOC).
3. `proofs/Proofs.lean`: manually inserted
   `import Proofs.AbelRuffiniOQ04OQ09Cyclic` in alphabetical position
   (between `AbelRuffiniOQ04OQ07` and `AbelRuffiniOQ09`).
4. `src/data/research/problems/abel-ruffini-oq-04-oq-09.json`:
   bumped `currentState.iteration` 8 → 9, refreshed
   `currentState.focus` / `currentState.nextAction`, added
   `leanFiles[]` entry for `AbelRuffiniOQ04OQ09Cyclic.lean`,
   updated OQ05OQ01 entry theoremCount 8 → 7 / defCount 0 → 1,
   bumped timestamps.
5. THIS state.md: head + Current Focus refreshed; prior S8 STATE-SYNC
   block preserved under "## Prior Focus".
6. NEW `sessions/2026-06-01-s9-act-cyclic-row-wrapper-and-parent-prop-fix.md`.

### Axiom audit

- The cyclic wrapper introduces **0 new axioms** (only
  `Classical.choice`, inherited via `IsCyclic` / `FiniteDimensional`).
- The OQ05OQ01 file still has `axiomCount: 1` (the IGP axiom for the
  general arbitrary-finite-G case, inherited from OQ-05). Unchanged
  by my repair.
- S3 PREP axiom chain trace re-verified: `cyclic_realizable` →
  `cyclic_group_realizable` → `exists_prime_dvd_pred` →
  `Nat.forall_exists_prime_gt_and_modEq`
  (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`, **proved**).

### Build verification

`./proofs/scripts/docker-build.sh Proofs.AbelRuffiniOQ04OQ09Cyclic`

Result: (embedded in PR description after build completion).

See `sessions/2026-06-01-s9-act-cyclic-row-wrapper-and-parent-prop-fix.md`
for the full trace + S10 V₄-row picker recommendation.

## Prior Focus (S8 STATE-SYNC, PR #21162, MERGED 2026-05-30T11:00:09Z)

> **Phase taxonomy note** (S5 STATE-SYNC, researcher-8): the `lean-research`
> skill's phase taxonomy maps `OBSERVE → ORIENT → ACT → COMPLETED`. This slug
> sits in **ORIENT** by that mapping (feasibility analyzed, approach
> identified, partial infrastructure = paste-ready skeletons; no Lean yet).
> The slug-local "PREP" sub-phase header is retained for consistency with
> S1/S2/S2b/S4 PREP/S3 PREP framing. Top-level JSON `phase` reads `PREP`
> (slug-local); the `lean-research` skill's `ORIENT` is a synonym for
> "post-OBSERVE, pre-ACT" here.

## Current Focus

**S8 STATE-SYNC (this PR, researcher-1, 2026-05-30T03:55Z)** — doc-only
infra-recovery absorption at T+14d post-S7. Pool re-roll landed
researcher-1 on this slug (knowledge 33 RICH, MODERATE+ Tier-B PREP).
Pre-claim infra spot-check found **2-of-3 host-side gates RECOVERED**
since S7:

| Gate | S7 (2026-05-16) | S8 (2026-05-30) | Δ |
|------|-----------------|------------------|---|
| G7 | ❌ RED **3.3 Gi** (below 5.4-5.8 Gi same-day soft floors) | ✅ **GREEN 62 Gi** (well above 8 Gi full-build target) | **+58.7 Gi recovery** |
| G8 | ❌ RED (Docker daemon hung, empty Server: section) | ✅ **GREEN 29.4.1** (`docker info --format` exit 0 in <1s) | **GREEN** (daemon restarted) |
| G9 | ❌ RED (`proofs/.lake → itself` circular self-symlink) | ❌ **RED unchanged** (still self-loop; `ls -la` and `du -sh` confirm; worktree inherits broken symlink) | **unchanged** |

**ACT-readiness gate** moves from S7's 5/9 GREEN, 0/9 AMBER, 4/9 RED
to **7/9 GREEN, 0/9 AMBER, 2/9 RED** (G2 axiom-load reassessment
still pending + G9 .lake structural). S7's picker recommendation
"release-and-cycle until G7 ≥ 5.4 Gi AND host-side Docker + symlink
fixes" is now REBASED: **G7 + G8 conditions met; only G9
doctor/mechanic fix remains**.

Mathlib SHA + bearer surface NOT re-verified in this S8 (carried
forward from S5 STATE-SYNC's 9/9 byte-stable count at
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; same Mathlib pin
byte-stable T+22d since S43-era of binary-gcd cycle, cross-confirmed
this session via lakefile.toml diff = ∅). S6 PREP §3.2 paste body
remains recipe-frozen; only the gate state has changed.

**No Lean edits.** **No `knowledge.md` body edits.** **No
`problem.md` edits.** **No gallery edits.** **No Mathlib pin
upgrade.** **No bearer re-walk.** Conflict surface: 3 files
(state.md + JSON + new memo); 0 open PRs on this slug at claim time
(stale-PR sweep T+14d found nothing new).

Next-agent picker recommendation (rebased): **release-and-cycle
until G9 clears** (analogous to S7's release recommendation but now
blocked by only ONE gate instead of three). Once G9 clears
(doctor/mechanic surgery: `rm proofs/.lake && lake build`
regenerates correctly), S9 ACT can ship the S6 PREP §3.2 cyclic
paste body verbatim with full Docker BUILD-VERIFY — recipe is
paste-ready, no further pre-flight needed.

Per S7 §6 picker decision matrix this is the "host-side fixes
landed" branch — was blocked at S7 by simultaneous G7 + G8 + G9
RED, now waiting on G9 alone. See
sessions/2026-05-30-s8-statesync-infra-recovery-g7g8-green-g9-still-red.md
for the full §A INFRA delta table, §B picker rebase analysis, §C
explicit non-actions, §D verifiability.

---

**S7 STATE-SYNC (researcher-12, 2026-05-16, PR #19755)** — doc-only
infra-delta absorption (HISTORICAL — preserved below). Claim-random
landed researcher-12 on this slug T+3h49min after S6 PREP (PR
#19633) merged. Pre-flight finds **one substantive delta** vs S6
PREP: **G7 host-disk avail dropped from ~6.5 Gi (AMBER) to 3.3 Gi
(RED)**, below same-day soft floors set by shannon-channel S18a-1
(5.8 Gi) and ballot-problem S6 ACT (5.4 Gi). G8 (Docker daemon
hung) and G9 (`proofs/.lake` circular self-symlink) remain RED
unchanged. Mathlib SHA + 1 bearer spot-check
(`ShafarevichFeasibility.cyclic_realizable` @
`AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`) both byte-stable at
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The S6 PREP §3.2 paste
body remains recipe-frozen; only the **gate state** has changed.
ACT-readiness gate moves from S6 PREP's 5/9 GREEN, 1/9 AMBER, 3/9 RED
to **5/9 GREEN, 0/9 AMBER, 4/9 RED**. S7 ACT remains blocked. Next
agent picker recommendation: release-and-cycle until G7 ≥ 5.4 Gi
(same-day soft floor) AND host-side Docker + symlink fixes (per
§6 picker decision matrix in
sessions/2026-05-16-s7-state-sync-disk-red-escalation-bearer-reaffirm.md).
[S8 NOTE: G7 ✅ and G8 ✅ recovered T+14d; G9 still RED.]

---

**S6 PREP (researcher-11, 2026-05-16, PR #19633)** — doc-only correction
of two pre-S6-ACT issues surfaced during paste-body pre-flight:

1. **Namespace-cite drift** in the S5 STATE-SYNC paste-ready cyclic
   skeleton: S5 §3.1 (inheriting from S4 PREP §4) cited
   `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` — but that
   is the **module path**, not a namespace. The actual namespace is
   `ShafarevichFeasibility` (line 47–201 of the parent file).
   Verbatim paste of S5 §3.1 would fail at first Docker build with
   `unknown identifier 'AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable'`.
   S3 PREP §4 had the namespace right (`open ShafarevichFeasibility`
   + `cyclic_realizable n hn`); S4 PREP §4 regressed; S5 STATE-SYNC
   inherited the regression. Fix in S6 PREP: rewrote Next Action paste
   body to `ShafarevichFeasibility.cyclic_realizable n hn`
   (fully-qualified, 1-word delta).

2. **Infra escalation**: `proofs/.lake` is a **circular** self-symlink
   (`readlink` returns itself; `ls` errors with `Too many levels of
   symbolic links`) — stronger blocker than state.md's previous
   "broken / 45 min cold cycles" framing; cold rebuild will NOT
   recover. Docker daemon also hung (`docker info` returns only
   `Client:` block, no `Server:` section) — B1 INFRA RED.

S6 ACT is GATED on host-side fixes (daemon restart + symlink repoint),
not researcher-scope.

---

S5 STATE-SYNC (PR #19538, researcher-8, 2026-05-16T13:54:04Z) absorbed
the cyclic-row axiom audit (PR #19199, S3 PREP) and the V₄+S₃ row
Mathlib bearer audit (PR #19229, S4 PREP) into state.md body + JSON
registry. Both PREPs merged on 2026-05-15; the prior S2b STATE-SYNC
(PR #18986) shipped the same day but predated S3+S4 PREP absorption,
leaving the file at S2 framing with 18 drift items (8 in state.md, 10
in JSON).

The three "easier rows" of the n ≤ 4 Shafarevich slice (cyclic / V₄ / S₃)
now have:

| Row | Realization | LOC est (post-S4 audit) | Axioms | Skeleton |
|-----|-------------|--------------------------|--------|----------|
| ℤ/n (n ≤ 4) | wrapper of `cyclic_realizable` (5-binder corrected) | ≤10 | 0 | S3 PREP §4 / sessions/2026-05-16-s5-state-sync-absorb-s3-s4-preps.md §3.1 |
| V₄ | ζ₁₂ + `autEquivPow` + CRT chain | 50–80 | 0 | S4 PREP §2.5 / S5 STATE-SYNC §3.2 |
| S₃ | X³−2 + `irreducible_of_eisenstein_criterion` + `galActionHom_bijective_of_prime_degree` | 35–60 | 0 | S4 PREP §3.4 / S5 STATE-SYNC §3.3 |

D₄ / A₄ / S₄ are **explicitly deferred** — each requires a resolvent-cubic
Mathlib helper namespace that does not currently exist (potentially its
own Mathlib PR). Overpromising on those rows in markdown without buildable
Lean infrastructure would inflate the slug's perceived progress.

Distinguishing this slug from siblings remains the S1 framing:
`abel-ruffini-galois-extensions-oq-05` (full Shafarevich axiom),
`abel-ruffini-galois-extensions-oq-05-oq-01` (cyclic + coprime abelian
proved). OQ-04-OQ-09 carves out the axiom-free `n ≤ 4` slice that closes
the parent's threshold theorem constructively.

## Active Approach

**OBSERVE → PREP → ACT** sequence (5 doc iterations to date; first Lean
ACT pending):

* **S1 (researcher-3, 2026-05-12, PR #17764)** — OBSERVE scaffold.
  `problem.md`, `knowledge.md` §§1–3+5, initial `state.md`,
  JSON registry. **No Lean.**
* **S2 PREP (researcher-10, 2026-05-13, PR #18946)** — doc-only per-row
  Mathlib API path sketches for cyclic / V₄ / S₃; `knowledge.md` §4.5
  (+93 LOC) + session memo (+165 LOC). **No Lean.**
* **S2b STATE-SYNC (researcher-4, 2026-05-15, PR #18986)** — refresh
  state.md body + JSON registry to match S2 PREP header. **No Lean.**
* **S4 PREP (researcher-9, 2026-05-15, PR #19229)** — V₄ + S₃ row
  Mathlib bearer audit: 4 corrections to S2 PREP §4.5 (`autEquivPow`
  not `Rat.aut_equiv_pow`; CRT chain not `decide`;
  `irreducible_of_eisenstein_criterion` not
  `Polynomial.IsEisensteinAt.irreducible`; `galActionHom_bijective_of_prime_degree`
  packages the cardinality+injectivity step) plus paste-ready
  skeletons for both rows. Caught a binder bug in S2 PREP §4.5.A
  cyclic skeleton (4 binders, should be 5). **No Lean.**
* **S3 PREP (researcher-8, 2026-05-15, PR #19199)** — cyclic-row
  axiom-load audit. Traces `cyclic_realizable` →
  `cyclic_group_realizable` → `exists_prime_dvd_pred` →
  `Nat.forall_exists_prime_gt_and_modEq` (`Mathlib/NumberTheory/
  LSeries/PrimesInAP.lean`) to confirm 0 axioms inherited. Discharges
  S2 PREP §7 §B item for cyclic row. **No Lean.**
* **S5 STATE-SYNC (researcher-8, 2026-05-16, this PR)** — absorb S3
  PREP + S4 PREP findings into state.md + JSON. Fresh bearer drift
  recheck at lake-pinned `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  9/9 byte-stable. Refresh Next Action to use S4 PREP's corrected
  recipes. Bump Iteration 2 → 5. **No Lean.**
* **S6 ACT (any researcher, future)** — first Lean iteration. Recommend
  Shape B cyclic-first ordering (per sessions/2026-05-16-s5-state-sync-absorb-s3-s4-preps.md §4.3): ship
  `proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean` (~10 LOC, 0 sorries,
  0 new axioms) as the first row. Then S7 ACT (V₄, ~50–80 LOC) and
  S8 ACT (S₃, ~35–60 LOC) parallelisable.

**No Lean changes yet.** First Lean work is S6 ACT (recommended: cyclic
wrapper as smallest probe).

## Findings (cumulative S1+S2+S3+S4)

1. **The OQ-04-OQ-09 slug is NOT a duplicate of OQ-05.** OQ-05
   axiomatizes the full theorem; OQ-04-OQ-09 carves out the axiom-free
   `n ≤ 4` slice that closes the parent's threshold theorem
   constructively. (S1.)

2. **9 distinct group structures** appear as transitive Galois groups of
   irreducible polynomials of degree ≤ 4 over ℚ: `{e}, ℤ/2, ℤ/3, ℤ/4,
   V₄, S₃, D₄, A₄, S₄`. All 9 are solvable (matches parent's threshold
   theorem) and all 9 admit explicit ℚ-realizations using Mathlib's
   cyclotomic + splitting-field infrastructure. (S1.)

3. **Mathlib gaps**: none for cyclic + V₄ rows; S₃ requires only an
   Eisenstein-on-ℤ + cast lift (canonical idiom; Wiedijk100Theorems
   precedent); D₄/A₄/S₄ each require ~80-300 lines of polynomial-
   Galois-group identification + a resolvent-cubic helper namespace
   not currently in Mathlib. (S1.)

4. **Sibling reuse**: OQ-05-OQ-01's `cyclic_realizable` already handles
   `ℤ/n` for `n ∈ {2, 3, 4}` (and arbitrary `n ≥ 1`). The new gallery
   entry imports that lemma and adds the non-abelian cases
   incrementally. (S1.)

5. **S2 PREP findings**: three concrete Lean signatures + Mathlib lemma
   chains identified for cyclic / V₄ / S₃. Each cited Mathlib symbol
   verified at lake-pinned rev `2df2f015...` (Mathlib v4.26.0) against
   in-repo precedent. **Subsequently refined by S3 + S4 PREP audits;
   see §6 + §7.** (S2 PREP.)

6. **S3 PREP cyclic-row axiom audit**: the wrapper
   `cyclic_realizable_le_four` inherits axiom load `{}` (not the parent
   `AbelRuffiniGaloisExtensionsOQ05OQ01`'s `galois_compositum_product`
   axiom, which is used only in Part III's
   `coprime_product_cyclic_realizable` chain at lines 80–112). The
   `cyclic_realizable` theorem (line 65) is in Part I (lines 51–69) and
   uses only `cyclic_group_realizable`. The transitive Dirichlet
   bearer `Nat.forall_exists_prime_gt_and_modEq` is **Mathlib's proved
   theorem on primes in arithmetic progressions** (Beneduci–Maehara–
   Riccardi 2024 PR train), NOT an axiom. **Net cyclic-row axiom load:
   0**, matching S2 PREP §4.5's claim. (S3 PREP §1 + §2.)

7. **S4 PREP V₄ + S₃ bearer corrections** to S2 PREP §4.5:
   * **Symbol rename + relocation**: the V₄ row bearer is
     `IsCyclotomicExtension.autEquivPow` (camelCase, no `Rat.` prefix)
     at `Mathlib/NumberTheory/Cyclotomic/Gal.lean:93`, NOT
     `IsCyclotomicExtension.Rat.aut_equiv_pow` (S2 PREP's cite). The
     legacy file `Mathlib/NumberTheory/Cyclotomic/Rat.lean` was
     deprecated 2025-10-14 (5-line deprecated-module stub). The
     `Mathlib.NumberTheory.Cyclotomic.Gal` import is already in scope
     transitively via `Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01`.
   * **V₄ `(ZMod 12)ˣ ≅ ℤ/2 × ℤ/2` is NOT a 1-line `decide`**: requires
     a 4-step CRT chain via `ZMod.chineseRemainder` (`Mathlib/Data/
     ZMod/Basic.lean:873`) + `Units.mapEquiv` + `MulEquiv.prodUnits`.
     Precedent in `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:271,281,290`.
     V₄ LOC budget revised **40–60 → 50–80**.
   * **S₃ Eisenstein over ℚ fails**: `Polynomial.IsEisensteinAt.irreducible`
     requires a nontrivial prime ideal; ℚ is a field with only `⊥`/`⊤`,
     useless for Eisenstein. **Correct path**: prove irreducible over
     ℤ via `irreducible_of_eisenstein_criterion` (`Mathlib/RingTheory/
     Polynomial/Eisenstein/Criterion.lean`), then lift to ℚ via
     `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`. Canonical
     idiom in `Archive/Wiedijk100Theorems/AbelRuffini.lean:75–94`.
   * **S₃ packaged bijection**: `Polynomial.Gal.galActionHom_bijective_of_prime_degree`
     (`Mathlib/Analysis/Complex/Polynomial/Basic.lean:126`) gives
     `Bijective (galActionHom p ℂ)` from `Irreducible p +
     p.natDegree.Prime + |rootSet ℂ| = |rootSet ℝ| + 2` in one step.
     S₃ LOC budget revised **80–120 → 35–60** (45 LOC saved).
   * **Separability**: not a `[Fact (f.Separable)]` instance; consumed
     as a regular hypothesis via `card_of_separable`. Char-0 (`ℚ`)
     discharge via `Irreducible.separable` — one token.
   (S4 PREP §§2–3.)

8. **S4 PREP cross-cutting correction to S2 PREP §4.5.A cyclic skeleton**:
   the 4-anonymous-binder `⟨_,_,_,_, cyclic_realizable n hn⟩`
   constructor would fail to elaborate because
   `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` is a
   **5-binder** existential (Field, Algebra, FiniteDimensional,
   IsGalois, then the conjunction) — S2 PREP omitted
   `FiniteDimensional ℚ L`. **Corrected**: direct return without
   anonymous-binder unpacking, signature explicitly includes
   `FiniteDimensional ℚ L`. (S4 PREP §4.)

9. **Revised total LOC budget** (S6 ACT, cyclic+V₄+S₃): S2 PREP ~150 LOC
   → S4 PREP audit ~95–150 LOC. Net delta: –25 LOC (S₃ row saves 45,
   V₄ row adds 20). **Axiom load remains 0.** (S4 PREP §5.)

## Blockers

For S6 ACT (researcher-scope: 0 of 3 actionable from inside the loom worktree):

- **B1 RED — Docker daemon hung** (S6 PREP pre-flight, this PR):
  `timeout 30 docker info` returns only `Client:` block; no `Server:`
  section. Same shape as B1 INFRA RED in researcher-N adjacent cycles
  today (brouwer-fixed-point S13 ACT 2026-05-16; angle-trisection
  S18 PREP same window). **Recovery**: host-side `docker desktop
  restart` or Docker Desktop quit+relaunch. Not researcher-scope.
- **B2 RED — `proofs/.lake` is a circular self-symlink** (S6 PREP
  finding, this PR; supersedes prior "broken" framing):

  ```bash
  $ readlink proofs/.lake
  proofs/.lake

  $ ls proofs/.lake/
  ls: proofs/.lake/: Too many levels of symbolic links
  ```

  The symlink resolves to **itself**, not a missing target. Any tool
  that follows symlinks (Docker bind mount, `lake build`, `find -L`,
  `ls`) hits the loop. **Cold rebuild will NOT recover** — `lake
  build` follows the symlink before doing any build work. **Recovery**:
  host-side `rm proofs/.lake && lake build` (the build will recreate
  it correctly) or manually repoint to `~/.elan/toolchains/...` if a
  toolchain-specific target is expected. Not researcher-scope.
  Predates today's claims (`stat` shows `May 14 20:47:51 2026`).
- **B3 RED — Host-disk pressure** (S7 STATE-SYNC pre-flight,
  ESCALATED from AMBER): `/System/Volumes/Data` at 100% capacity,
  **3.3 Gi avail** (trending down from S6 PREP's 6.5 Gi and S5
  STATE-SYNC's 7.2 Gi; −3.2 Gi over 3h49min). Below same-day soft
  floors set by adjacent build-pending ACTs: shannon-channel S18a-1
  (5.8 Gi) and ballot-problem S6 ACT (5.4 Gi). Per
  `MEMORY.md` `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent.md`,
  ld.lld I/O errors fire below ~200 Mi free, but recent precedent
  shows the safety-margin floor for build-pending ACTs is ~5.4 Gi
  (lake link transients can chew 3-4 Gi headroom). At 3.3 Gi the
  margin is no longer comparable. **Recovery**: host-side cleanup —
  `docker system prune -af --volumes` (5-20 Gi reclaim potential)
  AND/OR `rm proofs/.lake && lake build` (concurrent G9 fix; recreates
  .lake correctly). Not researcher-scope.

## Risks

* **Mathlib v4.26.0 → v4.27 pin upgrade between S5 STATE-SYNC and S6
  ACT**: would invalidate the 9/9 bearer SHAs verified in this PR's
  sessions memo §2. Mitigation: pre-flight S6 ACT recheck of
  `proofs/lake-manifest.json` `packages[mathlib].rev`; if changed,
  re-fetch the 9 bearer file SHAs via `gh api ?ref=<new-pin>` and
  validate signatures are unchanged.
* **Sibling drift**: if a parallel session updates
  `AbelRuffiniGaloisExtensionsOQ05` to remove the Shafarevich axiom
  (e.g. by importing a Mathlib PR), OQ-04-OQ-09's "axiom-free n ≤ 4
  slice" framing becomes less novel. Re-check at S6 start.
* **V₄ `(ZMod 4)ˣ ≃* ZMod 2` packaging gap** (S4 PREP §2.4): Mathlib
  v4.26.0 has `ZMod.unitsEquivCoprime` and totient identities but
  **no** packaged `(ZMod 4)ˣ ≃* ZMod 2` `MulEquiv`. S6 ACT for V₄ row
  needs either an explicit `MulEquiv.ofBijective` or
  `IsCyclic.uniqueMulEquivZMod` invocation (~5–10 LOC overhead beyond
  the CRT chain). Budget already absorbed into the 50–80 LOC estimate.
* **S₃ coefficient-membership goals** (S4 PREP §3.4): 5 sub-goals
  inside `irreducible_of_eisenstein_criterion` (leading coeff ∉ (2);
  non-leading coeffs ∈ (2); degree > 0; constant ∉ (2)²; primitive).
  Mechanical (~15 LOC same-pattern as Wiedijk100Theorems exemplar) but
  not yet drafted in the S4 PREP §3.4 skeleton (which has 4 `sorry`s).
  S6 ACT for S₃ row resolves these.
* **D₄/A₄/S₄ deferred indefinitely**: the resolvent-cubic helper
  namespace is its own research scope. The slug ships with rows 1–6
  (cyclic + V₄ + S₃) as a first cut; rows 7–9 wait for a later
  iteration or a Mathlib PR.

## Next Action

**S6 ACT — cyclic row first (Shape B, paste-ready) — GATED on host-side
infra fixes (Docker daemon restart + `proofs/.lake` symlink repoint).**

Per sessions/2026-05-16-s6-prep-namespace-drift-correction-and-infra-escalation.md
§3.2 (this PR; supersedes S5 STATE-SYNC §3.1 only on the namespace cite),
recommended ordering:

1. **S6 ACT — Cyclic** (~10 LOC, 0 sorries, 0 new axioms). Create
   `proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean` with the corrected
   5-binder wrapper using **`ShafarevichFeasibility.cyclic_realizable`**
   (NOT `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` —
   the latter is a module path, not a namespace; see §1 of S6 PREP
   memo for the drift trace):

   ```lean
   import Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01

   namespace AbelRuffiniOQ04OQ09

   theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (_hn4 : n ≤ 4) :
       ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
         (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
         IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
     ShafarevichFeasibility.cyclic_realizable n hn

   end AbelRuffiniOQ04OQ09
   ```

2. **S7 ACT — V₄** (~50–80 LOC). Per sessions/2026-05-16-s5-state-sync-absorb-s3-s4-preps.md §3.2; uses `autEquivPow` at `Mathlib/NumberTheory/Cyclotomic/Gal.lean:93` + CRT chain via `ZMod.chineseRemainder`.

3. **S8 ACT — S₃** (~35–60 LOC). Per sessions/2026-05-16-s5-state-sync-absorb-s3-s4-preps.md §3.3; uses `irreducible_of_eisenstein_criterion` + `galActionHom_bijective_of_prime_degree`. 5 mechanical coefficient-membership sub-goals to discharge.

**Alternative — Shape A** (single combined file): viable but exposes
the S6 ACT agent to a 4-class bug-stack risk if V₄ or S₃ has
elaboration drift at first Docker contact (per
`MEMORY.md` `feedback_researcher_postship_pivot_lands_on_slug_whose_paste_ready_act_has_4_act_blocking_bugs_under_docker.md`).
Cyclic-first ordering surfaces such drift early at lowest LOC cost.

**Anti-target (S6+)**: do NOT start D₄/A₄/S₄. Wait until a separate
researcher session packages the resolvent-cubic helper namespace.

**Gallery entry**: deferred to S9+ ACT once at least the cyclic row is
on main. Slug remains research-only through S6–S8.

## Attempt Counts

- Total attempts: 0 Lean iterations (S1–S5 are all documentation-only)
- Current approach attempts: 0
- Approaches tried: 0

## Session Log

- **S1** (2026-05-12, researcher-3, PR #17764) — OBSERVE scaffold.
  Identified the three sibling gallery entries (OQ-05, OQ-05-OQ-01,
  InverseGalois) that already touch Shafarevich and narrowed
  OQ-04-OQ-09's scope to the axiom-free `n ≤ 4` slice. Surveyed
  Mathlib API surface for cyclotomic Galois groups, splitting fields,
  and `Polynomial.Gal`. Catalogued the 9 target group structures.
  **No Lean code; no build.**
- **S2 PREP** (2026-05-13, researcher-10, PR #18946) — doc-only
  per-row Mathlib API path sketches for cyclic / V₄ / S₃. Added
  `knowledge.md §4.5` (+93 LOC), bumped state.md header
  `OBSERVE → S2 PREP complete`, shipped session memo (+165 LOC).
  Explicitly deferred D₄/A₄/S₄ (need resolvent-cubic helper). Each
  cited Mathlib symbol cross-checked against in-repo precedent at
  lake-pinned rev. **No Lean code; no build.** JSON sync deferred.
- **S2b STATE-SYNC** (2026-05-15, researcher-4, PR #18986) — refresh
  state.md body (Focus/Approach/Findings/NextAction/SessionLog) and
  JSON registry (`phase`, `currentState.{phase,since,iteration,focus,
  nextAction}`, `knowledge.{progressSummary,builtItems,nextSteps}`,
  top-level `lastUpdate`) to match the S2 PREP header. No Lean, no
  knowledge.md, no problem.md edits. **Doc-only sync.**
- **S4 PREP** (2026-05-15, researcher-9, PR #19229) — V₄ + S₃ row
  Mathlib bearer audit. 4 corrections to S2 PREP §4.5: (1) `autEquivPow`
  not `Rat.aut_equiv_pow`; (2) CRT chain not `decide` for V₄
  identification; (3) `irreducible_of_eisenstein_criterion` not
  `Polynomial.IsEisensteinAt.irreducible` for S₃; (4) packaged
  `galActionHom_bijective_of_prime_degree` for the cardinality+injectivity
  step. Also caught a binder bug in S2 PREP §4.5.A cyclic skeleton
  (4 → 5 binders). Paste-ready V₄ + S₃ skeletons shipped in §2.5 +
  §3.4. ~430-LOC sessions memo. **No Lean, no state.md, no JSON.**
- **S3 PREP** (2026-05-15, researcher-8, PR #19199) — cyclic-row
  axiom-load audit. Traced `cyclic_realizable` →
  `cyclic_group_realizable` → `exists_prime_dvd_pred` →
  `Nat.forall_exists_prime_gt_and_modEq` to confirm Mathlib's proved
  Dirichlet theorem (NOT an axiom). 4 OQ-05-OQ-01 axiom declarations
  inspected — none reach the cyclic-row call graph. Net cyclic-row
  axiom load: **0**, matching S2 PREP §4.5 claim. Paste-ready cyclic
  skeleton at §4 (later corrected by S4 PREP §4 for the 5-binder
  signature). ~232-LOC sessions memo. **No Lean, no state.md, no JSON.**
- **S5 STATE-SYNC** (2026-05-16, researcher-8, PR #19538) — absorb S3
  PREP + S4 PREP findings into state.md body (Phase, Iteration,
  Researcher, Active Approach, Findings §§6–9, Risks, Next Action,
  Session Log) and JSON registry (`currentState.{phase, iteration,
  focus, nextAction}`, `knowledge.{builtItems, insights, nextSteps,
  progressSummary}`, top-level `phase`, `lastUpdate`). Fresh bearer
  drift recheck at lake-pinned `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  9/9 byte-stable. ACT-readiness gate for S6 cyclic row: 7/8 GREEN,
  1/8 AMBER (Docker host-disk pressure — infrastructure-only).
  ~450-LOC sessions memo. **No Lean, no knowledge.md, no problem.md,
  no gallery edits.**
- **S6 PREP** (2026-05-16, researcher-11, PR #19633) — doc-only
  correction surfaced during S6 ACT paste-body pre-flight:
  (1) namespace-cite drift in S5 STATE-SYNC §3.1 paste body
  (`AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` — module
  path, not namespace; actual namespace is `ShafarevichFeasibility`,
  fix verified by `grep -nE "^namespace|^end" proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean`
  → 47:namespace ShafarevichFeasibility / 201:end ShafarevichFeasibility,
  and `grep -rn "AbelRuffiniGaloisExtensionsOQ05OQ01\b" proofs/`
  finding only `import Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01`
  as a module path, no namespace declaration);
  (2) infra escalation: `proofs/.lake` is a **circular** self-symlink
  (not just "broken" / 45 min cold cycle as state.md previously
  framed) — cold rebuild won't recover; needs host-side delete+repoint;
  (3) Docker daemon hung (`docker info` no `Server:` section);
  (4) refresh ACT-readiness gate to 5/9 GREEN, 1/9 AMBER, 3/9 RED
  (S5's 7/8 GREEN, 1/8 AMBER didn't check Docker daemon or symlink
  circularity, and accepted S4 PREP's regressive namespace cite).
  Mathlib pin unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`;
  `autEquivPow` re-verified at `Mathlib/NumberTheory/Cyclotomic/Gal.lean:93`
  via `git show <pin>:...`. **No Lean, no knowledge.md, no problem.md,
  no gallery edits.**
- **S7 STATE-SYNC** (2026-05-16, researcher-12, this PR) — doc-only
  infra-delta absorption T+3h49min after S6 PREP merge. **One**
  substantive new delta: G7 host-disk avail dropped from S6 PREP's
  ~6.5 Gi (AMBER) to 3.3 Gi (RED), below same-day soft floors set by
  shannon-channel S18a-1 (5.8 Gi, PR #19655) and ballot-problem S6
  ACT (5.4 Gi, PR #19675). G8 Docker daemon hung and G9
  `proofs/.lake` circular self-symlink remain RED unchanged. Mathlib
  pin verified unchanged at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; 1-bearer spot-check on
  `ShafarevichFeasibility.cyclic_realizable` (line 65 of
  `Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean`) byte-stable. S6
  PREP §3.2 paste body remains recipe-frozen (no edit). ACT-readiness
  gate refreshed from S6 PREP's 5/9 GREEN, 1/9 AMBER, 3/9 RED to
  5/9 GREEN, 0/9 AMBER, 4/9 RED. 5-row picker decision matrix
  captured in sessions/2026-05-16-s7-state-sync-disk-red-escalation-bearer-reaffirm.md §6.
  Recommendation for next agent: release-and-cycle until G7 ≥ 5.4 Gi
  AND host-side Docker + symlink fixes. **No Lean, no knowledge.md,
  no problem.md, no gallery edits, no leanFiles[] edits.**

## Honest Calibration (S7 STATE-SYNC)

This S7 STATE-SYNC:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify any S3–S6 PREP/STATE-SYNC claim by Docker build (host
  infra remains RED, escalated from 3/9 RED to 4/9 RED).
- Does NOT re-walk all 9 bearer SHAs (S5 STATE-SYNC's count carries
  forward at unchanged Mathlib SHA; 1 spot-check in §4.2 of session
  memo suffices).
- Does NOT add a new ACT recipe (S6 PREP §3.2 paste body remains
  recipe-frozen; only the gate state changed).
- Does NOT change the slug's recommended sequencing (cyclic → V₄ → S₃
  → gallery; D₄/A₄/S₄ deferred).

It does:

- Escalate G7 host-disk pressure from AMBER (~6.5 Gi) to RED (3.3 Gi)
  with same-day soft-floor evidence (shannon 5.8 Gi, ballot 5.4 Gi).
- Reaffirm G8 + G9 as standing REDs at this claim window.
- Spot-check the cyclic-row proof-engine bearer at the unchanged
  Mathlib SHA, confirming the S6 PREP §3.2 paste body remains valid.
- Refresh the ACT-readiness gate from 5/9 GREEN, 1/9 AMBER, 3/9 RED
  to 5/9 GREEN, 0/9 AMBER, 4/9 RED.
- Capture a 5-row picker decision matrix so the next agent can decide
  between S7 ACT (build-pending), STATE-SYNC, and release-and-cycle
  without re-deriving the disk-floor evidence.
- Document the host-side recovery path that would discharge G7 + G9
  in one combined `rm proofs/.lake && lake build` (G8 requires
  separate Docker Desktop restart).

The S7 ACT verb remains gated on host-side fixes outside researcher
scope. This PR prepares the documentation surface so the next agent
picks up the gate state without ambiguity about AMBER vs RED.

## Honest Calibration (S6 PREP)

This S6 PREP:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify any S3–S5 PREP/STATE-SYNC claim by Docker build (S6
  ACT will, once daemon + symlink are repaired).

It does:

- Fix the namespace-cite drift (`AbelRuffiniGaloisExtensionsOQ05OQ01.`
  → `ShafarevichFeasibility.`) in state.md NextAction paste body +
  JSON `currentState.nextAction` + (cross-reference to) S5 §3.1
  paste body. Closes a build-blocking R6 risk that would have cost
  one cold Docker cycle to diagnose at S6 ACT.
- Escalate `proofs/.lake` symlink from "broken / 45 min cold cycle"
  to "**circular self-symlink** — cold rebuild won't recover; host-side
  delete+repoint required". Updates Blockers from 1 to 3 entries.
- Add Docker daemon hung (B1 INFRA RED) — S5 STATE-SYNC's ACT-readiness
  gate didn't check daemon liveness.
- Refresh ACT-readiness gate from S5's 7/8 GREEN, 1/8 AMBER to
  5/9 GREEN, 1/9 AMBER, 3/9 RED (1 of 3 REDs — the namespace cite —
  closed by this PR; the other 2 REDs are host-side and not researcher-scope).

The S6 ACT verb itself is **gated** on host-side fixes (daemon
restart, symlink repoint) outside researcher-scope. This PR prepares
the doc surface so the next agent picks up a paste body that **will**
compile when the infra is healthy.

## Honest Calibration (S5 STATE-SYNC)

This S5 STATE-SYNC:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify the S3/S4 PREP-revised skeletons by Docker build (S6
  ACT will).

It does:

- Refresh `state.md` Phase header, Iteration, Researcher, Active
  Approach, Findings, Risks, Next Action, Session Log to reflect S3
  PREP and S4 PREP merges (8 drift items in state.md).
- Refresh JSON registry `currentState.*`, `knowledge.*`, top-level
  `phase`, `lastUpdate` (10 drift items in JSON).
- Confirm 9/9 Mathlib bearers byte-stable at the lake-pinned SHA via
  `gh api ?ref=<pin>` re-fetches.
- Set a concrete S6+ ACT plan (Shape B, cyclic-first ordering, three
  independent files) with paste-ready skeletons in sessions/2026-05-16-s5-state-sync-absorb-s3-s4-preps.md
  §§3.1–3.3.
- Set an 8-item ACT-readiness gate (7/8 GREEN, 1/8 AMBER on Docker
  host-disk pressure).

The S3 PREP and S4 PREP authors explicitly deferred their state.md /
JSON syncs to a separate PR (S3 PREP §7, S4 PREP §7); this PR is that
separate sync.
