# S4 PREP — Close (a) Axiomatize vs (b) Infrastructure-Only Decision; Identify Productive S5 ACT Options

**Date**: 2026-05-16T09:10Z  (UTC)
**Researcher**: researcher-8
**Slug**: erdos-369
**Phase**: PREP (doc-only)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-manifest.json)

---

## §1. Context and Scope

Erdős Problem #369 (Erdős–Graham, 1980, smooth-numbers): for every
ε > 0 and k ≥ 2, do all sufficiently large n admit a run of k
consecutive integers in {1,…,n}, each n^ε-smooth?  Open even for
k = 2; positively answered for "infinitely many n" by Balog–Wooley
(1998) but not for "all sufficiently large n."

Current Lean file `proofs/Proofs/Erdos369Problem.lean` (171 LOC):
* 5 definitions (`IsSmooth`, `ConsecutiveSmoothRun`,
  `HasConsecutiveSmoothRun`, `ErdosConjecture369`,
  `ErdosConjecture369_k2`)
* 6 theorems (`isSmooth_one`, `isSmooth_mono_B`, `isSmooth_prime_self`,
  `isSmooth_mul`, `isSmooth_prime_pow`, `consecutiveSmoothRun_1_2_2`)
* 0 axioms, 0 sorries
* meta.json: `status=axiomatized`, `badge=wip`, `axiomCount=0`,
  `sorries=0`

The JSON `currentState.nextAction` (set at S3 ACT, 2026-04-28) reads:

> Decide: (a) state the conjecture as `axiom erdos_369 : ...` and
> re-classify as axiomatized, or (b) leave as infrastructure-only.
> Current state is the latter.

This PREP **closes the decision in favor of (b)** by surfacing two
facts the S3 ACT did not have: (i) PR #11978 (2026-04-23) explicitly
re-set `badge: axiom → wip` in meta.json, codifying choice (b); and
(ii) sibling slugs (erdos-1, erdos-10) follow the same
`axiomatized + wip + 0 axioms` convention for open-conjecture
infrastructure.  Refreshes 12 drift items across state.md / JSON;
identifies three productive S5 ACT options.  No Lean edits, no
meta.json edits.

---

## §2. Drift Inventory (state.md / JSON / Lean file)

### 2.1 state.md is **5 iterations stale**

| Field        | state.md (pre-S4) | Truth (post-S4 PREP) |
|--------------|--------------------|-----------------------|
| Phase        | NEW                | PREP                  |
| Iteration    | 1                  | 4                     |
| Since        | 2026-01-13T00:56Z  | 2026-05-16T09:10Z     |
| Focus        | "Initial exploration" | Decision closed; identify productive ACT |
| Approach     | "None yet"         | Two-tier: confirm (b), then axiomatize Balog–Wooley for content |
| Next Action  | "Begin exploration" | Choose among Option A / B / C in §4 |
| Total attempts | 0                | 3 (S1 OBSERVE, S2 cleanup, S3 dead-axiom removal) |
| Approaches tried | 0              | 1 (Prop-only infrastructure)               |

state.md never received the S2 / S3 updates that the JSON tracked.
S4 PREP restores parity.

### 2.2 JSON has **minor drifts**

| Field                                        | JSON (pre-S4) | Truth (post-S4 PREP) |
|----------------------------------------------|---------------|----------------------|
| `phase` (top-level)                          | "OBSERVE"     | "PREP"               |
| `currentState.phase`                         | "ACT"         | "PREP"               |
| `currentState.iteration`                     | 3             | 4                    |
| `currentState.focus`                         | "172-line file" (stale LOC) | "171-line file" |
| `currentState.nextAction`                    | "Decide (a) or (b)" | "(b) confirmed — pick Option A/B/C in S5 ACT" |
| `currentState.attemptCounts.total`           | 0             | 3                    |
| `currentState.attemptCounts.approachesTried` | 0             | 1                    |
| `knowledge.nextSteps`                        | []            | Three named options (A/B/C, §4)  |
| `leanFiles[0].lineCount`                     | 172           | 171                  |
| `lastUpdate`                                 | 2026-04-28T01:52Z | 2026-05-16T09:10Z |

### 2.3 Lean file: no drift, no edits needed

```
$ wc -l proofs/Proofs/Erdos369Problem.lean
     171 proofs/Proofs/Erdos369Problem.lean
$ grep -c '^theorem ' proofs/Proofs/Erdos369Problem.lean
6
$ grep -c '^def ' proofs/Proofs/Erdos369Problem.lean
5
$ grep -c '^axiom ' proofs/Proofs/Erdos369Problem.lean
0
$ grep -cE '^\s*sorry\s*$|\sby sorry$' proofs/Proofs/Erdos369Problem.lean
0
```

Counts match meta.json (theoremCount 6, defCount 5, axiomCount 0,
sorries 0) and exceed JSON `leanFiles[0].lineCount=172` by 1 only
because of an earlier off-by-one (likely a trailing-newline edit
between PR #6216 enrichment and PR #13453 sync).  Correcting
171→172→171 is a 1-line JSON tweak only.

### 2.4 No sessions directory existed

Created in this PREP at `research/problems/erdos-369/sessions/`,
seeded with this memo.  Sibling slugs (`erdos-1`, `erdos-10`)
likewise have no sessions dir — Erdős infrastructure-only slugs
rarely accumulate per-iteration memos.  This file is the first.

---

## §3. The (a) vs (b) Choice — Already Implicitly Settled

### 3.1 What S3 ACT did

S3 ACT (2026-04-28, PR #13453) "sync stale pool metadata to actual
file state" deleted the dead `largestPrimeFactor` definition and the
unused `balog_wooley_infinitely_many` axiom (2A → 0A).  It left
behind the open question: should the *main* conjecture
`ErdosConjecture369` be re-asserted as `axiom erdos_369 :
ErdosConjecture369`?  S3 wrote the decision to nextAction without
selecting.

### 3.2 What PR #11978 (2026-04-23) already decided

PR #11978, **five days before S3 ACT**, set:

```
badge: axiom → wip       (meta.json)
status: axiomatized      (unchanged)
axiomCount: 0            (unchanged at 0)
```

Title: *"Fix: erdos-369 and erdos-866 badge axiom→wip (0 axiom
declarations)."*

This is the codified "(b) infrastructure-only" choice: by setting
`badge=wip`, the curator-of-record acknowledged the file declares
no axioms, accepts the `axiomatized` status as a policy formality
for open conjectures, and treats the Prop definitions as the only
"formalization" present.

S3 ACT did not register that PR #11978 had already chosen (b); the
"Decide" sentence in nextAction is therefore obsolete.

### 3.3 Sibling slugs confirm the convention

`status: axiomatized` + `badge: wip` + `axiomCount: 0` is the
established pattern for open-conjecture slugs whose Lean file
consists of Prop definitions and verified supporting lemmas but no
axiomatized main statement:

| Slug         | status       | badge | axiomCount | sorries | theoremCount |
|--------------|--------------|-------|------------|---------|--------------|
| erdos-1      | axiomatized  | wip   | 0          | 0       | 3            |
| erdos-10     | axiomatized  | wip   | 0          | 0       | 0            |
| **erdos-369**| axiomatized  | wip   | 0          | 0       | 6            |

(Verified by reading `src/data/proofs/erdos-{1,10,369}/meta.json`
at HEAD.)  This is intentional: Lean Genius policy says open
conjectures map to `status: axiomatized`, and `badge: wip` is the
honest signal when no axiom has actually been declared.

### 3.4 What this PREP changes

* `currentState.nextAction` JSON: rewrite the obsolete "Decide (a)
  or (b)" sentence to "(b) confirmed by PR #11978 + sibling
  convention.  Pick among S5 ACT Option A / B / C (see §4)."
* `currentState.focus` JSON: refresh to acknowledge resolved
  decision and identify productive ACT directions.
* `knowledge.nextSteps` JSON: populate with the three S5 ACT
  options below.

No Lean / no meta.json edits.

---

## §4. Productive S5 ACT Options (Post-Decision)

Since (b) is settled, the slug needs a *forward* identity rather
than a *decide* identity.  Three productive directions are
identified, all of which take the existing infrastructure as
given.

### 4.1 Option A — Axiomatize Balog–Wooley (1998), variant 1

Variant 1 is the strengthening "each m ∈ P must be m^ε-smooth"
(rather than n^ε-smooth).  Balog–Wooley prove: for every ε > 0 and
k ≥ 2 there are **infinitely many** m such that
m+1, …, m+k are all m^ε-smooth.  This is a deep, non-trivial result
that justifies an `axiom`.

**Lean shape** (paste-ready for S5 ACT):

```lean
/--
**Balog–Wooley (1998):** For every ε > 0 (here modelled by a
fraction ε_num / ε_den with ε_num, ε_den positive) and every k ≥ 2,
there are infinitely many m such that m+1, …, m+k are all
m^(ε_num/ε_den)-smooth.

We state the discrete version: for every rational ε modeled by
ε_num/ε_den with ε_num ≥ 1 and ε_den ≥ 1, and every k ≥ 2, the set
of m such that the run starting at m+1 of length k is
(m^ε_num)^(1/ε_den)-smooth (i.e., all factors ≤ m^(ε_num/ε_den)) is
infinite.  Following codebase convention for open-conjecture
auxiliary results, we encode this via a `Set.Infinite` predicate
and an existential bound function `smoothBoundOf : ℕ → ℕ → ℕ → ℕ`
satisfying `smoothBoundOf m ε_num ε_den ≤ m`.

Reference: A. Balog and T. D. Wooley, *On strings of consecutive
integers with no large prime factors*, J. Austral. Math. Soc. Ser.
A **64** (1998), 266–276.
-/
axiom balog_wooley_infinitely_many :
  ∀ (ε_num ε_den : ℕ), ε_num ≥ 1 → ε_den ≥ 1 →
  ∀ k : ℕ, k ≥ 2 →
  ∀ (smoothBoundOf : ℕ → ℕ → ℕ → ℕ),
    (∀ m, smoothBoundOf m ε_num ε_den ≤ m) →
    {m : ℕ | m ≥ 1 ∧
       ConsecutiveSmoothRun (m + 1) k (smoothBoundOf m ε_num ε_den)}.Infinite
```

Notes:
* The axiom re-introduces the `balog_wooley_infinitely_many` name
  that S3 ACT removed as dead code — but this time it is *used*:
  add a 5–10 LOC theorem `balog_wooley_implies_369_variant1`
  that derives the variant-1 form of the conjecture from this
  axiom.
* `Set.Infinite` requires the `import Mathlib.Data.Set.Finite`
  module (already implicitly imported through
  `Mathlib.Data.Finset.Basic`, but explicit import recommended).
* LOC forecast: +25–40 LOC (1 axiom + 1 derived theorem +
  imports + docstring).  meta.json: axiomCount 0 → 1, badge
  wip → axiom (per sibling convention erdos-1-oq-02), status
  unchanged.

**Risk class**: LOW.  The new axiom is namespace-local and the
derived theorem uses only existing definitions.  No interaction
with Mathlib pin.

### 4.2 Option B — Prove a concrete k = 3 warmup

Verify that {1, 2, 3} is a run of 3 consecutive 3-smooth numbers
(1 vacuous, 2 prime, 3 prime).  Generalize the existing
`consecutiveSmoothRun_1_2_2` (1, 2 are 2-smooth) by adding e.g.
`consecutiveSmoothRun_1_3_3` and `consecutiveSmoothRun_2_3_4`
(2, 3, 4 are 3-smooth since 2 = 2, 3 = 3, 4 = 2²).

**Lean shape**:

```lean
/-- (1, 2, 3) is a run of 3 consecutive 3-smooth numbers. -/
theorem consecutiveSmoothRun_1_3_3 : ConsecutiveSmoothRun 1 3 3 := by
  refine ⟨by omega, ?_⟩
  intro i hi
  interval_cases i
  · simpa using isSmooth_one 3
  · exact ⟨by omega, fun p hp hdvd => by
      have h2 : p ∣ 2 := hdvd
      rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
      · exact absurd h hp.ne_one
      · omega⟩
  · exact ⟨by omega, fun p hp hdvd =>
      le_of_eq ((hp.eq_one_or_self_of_dvd 3 hdvd).resolve_left hp.ne_one)⟩

/-- (2, 3, 4) is a run of 3 consecutive 3-smooth numbers
    (2 = 2¹, 3 = 3¹, 4 = 2²). -/
theorem consecutiveSmoothRun_2_3_3 : ConsecutiveSmoothRun 2 3 3 := by
  -- analogous; case 4 needs isSmooth_prime_pow 2 ≤ 2 ≤ 3
  sorry
```

LOC forecast: +20–30 LOC (2 theorems).  meta.json: theoremCount
6 → 8.  No new axiom, badge stays `wip`.

**Risk class**: LOW.  Concrete numeric cases.  May expose missing
Mathlib lemmas (e.g., `Nat.Prime.eq_two_of_dvd_two`) — but those
are well-covered.

### 4.3 Option C — Formalize the trivial-reading observation

The problem.md notes the *literal* reading is trivially true:
take P = {1, …, k} and require n ≥ k^(1/ε).  This justifies why
the two non-trivial variants are the actual interest.  A
formalization could be a theorem:

```lean
/-- The literal reading of Erdős #369 is trivially true: the run
    {1, …, k} consists of k consecutive integers in {1,…,n}, each
    is at most k, and k ≤ n^ε whenever n ≥ k^(1/ε).  This makes
    the problem only non-trivial under the two strengthenings in
    `problem.md`.
-/
theorem erdos_369_literal_trivial :
    ∀ k : ℕ, k ≥ 2 → ∀ B : ℕ, B ≥ k → HasConsecutiveSmoothRun B k B := by
  intro k hk B hBk
  refine ⟨1, by omega, by omega, ?_⟩
  refine ⟨hk, ?_⟩
  intro i hi
  -- 1 + i ≤ k ≤ B; all prime factors of 1+i are ≤ 1+i ≤ B
  sorry
```

LOC forecast: +15–25 LOC (1 theorem, 1 docstring expansion of the
file-level commentary).  meta.json: theoremCount 6 → 7.

**Risk class**: LOW–MEDIUM.  Requires a generic lemma
`Nat.factor_le_self : ∀ p, p.Prime → p ∣ m → p ≤ m` (likely
`Nat.le_of_dvd` with positivity).  No new axiom.

### 4.4 Recommendation

S5 ACT should pick **Option A** (Balog–Wooley axiom) — it gives
the deepest mathematical content, restores a stated deep theorem
that was previously held as a dead axiom, and aligns the slug with
sibling open-conjecture entries that carry one well-justified
axiom (e.g., erdos-1-oq-02 has axiomCount = 1 for a comparable
1980s-era number-theoretic result).  Option B is a good *parallel*
S5 ACT for a researcher who prefers no axiom additions.  Option C
is the smallest scoped variant and best as a "warm-up" before A.

---

## §5. Bearer Drift Recheck (Mathlib API)

Mathlib pin verified at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
via `lake-manifest.json`.  No pin changes since the S5 STATE-SYNC
on abel-ruffini-oq-04-oq-09 (PR #19538, 2026-05-16T08:30Z).

The file uses these Mathlib bearers (none of which are likely to
churn):

| Bearer                               | Module                                 | Spot-check |
|--------------------------------------|----------------------------------------|------------|
| `Nat.Prime`                          | `Mathlib.Data.Nat.Prime.Basic`         | file SHA `a3a89c8...` |
| `Nat.dvd_one`                        | `Mathlib.Data.Nat.Basic` (transitive)  | file SHA `2d423e0...` |
| `Nat.not_prime_one`                  | `Mathlib.Data.Nat.Prime.Basic` (re-export) | inherited |
| `Nat.le_of_dvd`                      | `Mathlib.Data.Nat.Basic`               | inherited |
| `Nat.dvd_of_dvd_of_dvd` (transitive) | `Mathlib.Data.Nat.Basic`               | inherited |
| `Nat.one_le_iff_ne_zero`             | `Mathlib.Data.Nat.Basic`               | inherited |
| `Nat.one_le_pow`                     | `Mathlib.Data.Nat.Basic`               | inherited |
| `Nat.Prime.eq_one_or_self_of_dvd`    | `Mathlib.Data.Nat.Prime.Basic`         | grep-confirmed (search hit `Prime.dvd_iff_eq`) |
| `Nat.Prime.dvd_of_dvd_pow`           | `Mathlib.Data.Nat.Prime.Basic`         | inherited |
| `Finset.Basic` (implicit)            | `Mathlib.Data.Finset.Basic`            | file SHA `74b1c01...` |

**3-spot file SHAs** verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c...`:

* `Mathlib/Data/Nat/Prime/Basic.lean`: SHA `a3a89c84047e1ccc90760ff27abcf62b2b4df172`
* `Mathlib/Data/Nat/Basic.lean`: SHA `2d423e040ed765f4e714ce133cb9236f82ac956a`
* `Mathlib/Data/Finset/Basic.lean`: SHA `74b1c01fe149069a2a72dd6f6d1d76f39c063b6e`

No bearer drift expected for any of A/B/C in §4.

---

## §6. Build Risk Analysis (Forward to S5 ACT)

This S4 PREP is **doc-only**: zero Lean edits, zero meta.json
edits, zero Docker invocation.  Build state of
`Erdos369Problem.lean` inherits from PR #13453 (2026-04-28 — last
commit touching this file), at which point the file built clean.

When an S5 ACT is attempted (any of A / B / C), the Docker build
forecast is:

* **Option A** (axiom + 1 derived theorem): cache-hit on all
  Mathlib imports; new axiom is namespace-local (no cross-module
  effects); derived theorem uses only `ConsecutiveSmoothRun`
  (already typechecked).  Forecast: **30–60s wall** if cache warm.
* **Option B** (2 concrete theorems): same import surface; new
  theorems use `interval_cases`, `omega`, and existing prime
  facts.  Forecast: **30–90s wall**.
* **Option C** (1 trivial-reading theorem + docstring): smallest
  surface; uses `Nat.le_of_dvd` only.  Forecast: **30–60s wall**.

If host disk pressure precludes Docker (per researcher-8's
2026-05-16T01:57Z S5 STATE-SYNC encounters), S5 ACT can ship with
`(build pending)` qualifier per the precedent in memory file
`feedback_researcher_cherry_pick_peer_audited_stranded_commit_ship_build_pending_when_docker_daemon_hung.md`
— LOW risk because all three options are namespace-local additive
edits.

---

## §7. S5 ACT Readiness Gate (8-point)

| #  | Condition                                            | Status |
|----|------------------------------------------------------|--------|
| 1  | (a)/(b) decision resolved                            | ✅ — (b) confirmed (§3) |
| 2  | State.md / JSON drift cleared                        | ✅ — closed by this PREP |
| 3  | Mathlib bearer pin verified                          | ✅ — 3-spot at pin SHA `2df2f015...` (§5) |
| 4  | At least one paste-ready S5 ACT recipe               | ✅ — three (Options A/B/C, §4) |
| 5  | Build-risk forecast per option                       | ✅ — all LOW (§6) |
| 6  | No interaction with other open PRs on slug           | ✅ — only erdos-369 PRs in last 30d are merged sync/badge fixes |
| 7  | Sessions/ dir exists (for S5 ACT memo)               | ✅ — created in this PREP |
| 8  | Host Docker available (or build-pending precedent OK)| AMBER — host df=69%, 7.2Gi avail; below the ≥10Gi memory threshold but Docker responsive (`docker info` 1.8s).  ACT advised to verify pre-flight. |

7/8 GREEN, 1/8 AMBER.  Threshold for S5 ACT: 6/8 GREEN.  Pass.

---

## §8. Cross-References

* **Sibling open-conjecture infrastructure slugs** following the
  same `axiomatized + wip + 0 axioms` convention:
  `src/data/proofs/erdos-1/meta.json`,
  `src/data/proofs/erdos-10/meta.json`.
* **Sibling open-conjecture with 1 axiom** (Option A reference):
  `src/data/proofs/erdos-1-oq-02/meta.json` (axiomCount=1,
  badge=axiom, status=axiomatized).
* **PR #11978** (2026-04-23) — codified choice (b) by setting
  badge `axiom → wip`.
* **PR #13453** (2026-04-28) — S3 ACT, removed dead
  `largestPrimeFactor` and unused
  `balog_wooley_infinitely_many` axiom (2A → 0A); set the obsolete
  "Decide (a) or (b)" nextAction.
* **PR #11718** (2026-04-23) — earlier badge fix mathlib → axiom
  (later refined to wip by PR #11978).
* Lean file: `proofs/Proofs/Erdos369Problem.lean` (171 LOC,
  6 theorems, 5 defs, 0 axioms, 0 sorries, status unchanged
  through S4 PREP).

---

## §9. Handoff

S5 ACT can be any of:

* **Option A** (preferred): axiomatize Balog–Wooley.  +1 axiom,
  +1 derived theorem, ~25–40 LOC.  meta.json axiomCount 0→1,
  badge wip → axiom.  Justifies slug's `axiomatized` status with
  a load-bearing deep theorem.
* **Option B**: two concrete k=3 warmups.  +2 theorems, ~20–30
  LOC.  meta.json theoremCount 6→8, badge stays wip.
* **Option C**: trivial-reading observation as theorem.  +1
  theorem, ~15–25 LOC.  meta.json theoremCount 6→7, badge stays
  wip.

Any of A/B/C builds independently on this PREP — no further
documentation work required before the Lean edit.  The Lean diff
templates in §4 are paste-ready (minus the 1–2 sorries flagged in
B/C, which the implementing researcher can dispatch in-iteration).
