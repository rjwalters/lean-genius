# Session 21 — S21 DOCTOR-FIX + BUILD-VERIFY — Nat.pow_pos API misuse on S20's bearer (1-token fix → 3058/3058 jobs clean)

**Date**: 2026-06-01
**Mode**: REVISIT (claim → triage → Docker-verify-finds-bug → 1-token doctor fix → re-verify clean → ship)
**Researcher**: researcher-1
**Outcome**: progress (S20 ACT bearer unblocked — `pow_factorization_mul_choose_le` now formally verifies; S21 ACT plan from S20 nextAction now genuinely actionable)
**Cycle time**: ~12 min claim → fix → verify → ship
**Predecessor**: S20 ACT (PR shipped 2026-05-31 with `(build pending — G9 lake self-loop)` qualifier; the qualifier was misleading — G9 is INERT for Docker per cross-slug evidence, and the file had a real `Nat.pow_pos` bug Docker would have caught).

---

## §1 — Trigger

Pool re-roll on randomized claim landed on
`basel-problem-oq-01-oq-01-oq-02-oq-02` (RICH 91-pt knowledge, MODERATE+
Tier-A PREP phase, lastUpdate null). S20 narrative claimed `(build
pending — G9 lake self-loop)` for the just-pasted
`pow_factorization_mul_choose_le` bearer.

**Pre-claim recency probe**:
* INFRA gates GREEN per researcher-1 S50 binary-gcd-oq-03-oq-02 evidence (T-50m).
* Filesystem `wc -l proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` → **972** (matches S20 narrative 905+67=972; `leanFiles[4].lineCount` JSON value is stale at 905 — flagged as mechanic territory).
* Filesystem theorem count → **38** (matches S20 narrative 36+2; JSON `leanFiles[4].theoremCount=36` stale).

**Decision**: directly run `./proofs/scripts/docker-build.sh
Proofs.BaselProblemOQ01OQ01OQ02OQ02` to verify S20's "build pending"
state, matching the MEMORY pattern
`[G9 qualifier masks real bugs — ALWAYS Docker-verify]`.

---

## §2 — Docker build #1: REAL BUG FOUND

```
error: Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean:959:54: Function expected at
  Nat.pow_pos (Prime.pos hp)
but this term has type
  0 < p ^ ?m.377

Note: Expected a function because this term is being applied to the argument
  i
[…]
error: Lean exited with code 1
Some required targets logged failures:
- Proofs.BaselProblemOQ01OQ01OQ02OQ02
=== Build failed with exit code 1 ===
```

**Bug**: at line 959 inside S20's pasted `pow_factorization_mul_choose_le`
proof body (Stage 5, subset argument), the call

```lean
exact absurd hi_cond (not_le.mpr (Nat.mod_lt _ (Nat.pow_pos hp.pos i)))
```

passes an explicit `i` to `Nat.pow_pos`, but Mathlib v4.26.0's
`Nat.pow_pos` has signature `Nat.pow_pos : {p : ℕ} (hp : 0 < p) → 0 < p ^ n`
with `n` **implicit**. The application `Nat.pow_pos hp.pos i` therefore
tries to apply the already-fully-formed term `0 < p ^ ?m.377` (a Prop)
to `i` (a `ℕ`), which fails as "Function expected".

**Confirming Mathlib API search** (per
[[reference_mathlib_source_paths_outside_g9_loop]]):

```
~/Projects/lean-genius-proofs/.lake/packages/mathlib/Mathlib/Data/Nat/Prime/Basic.lean:297:
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := d) c0)).trans_lt ?_
~/Projects/lean-genius-proofs/.lake/packages/mathlib/Mathlib/Data/Nat/Log.lean:101:
  exacts [(pow_le_iff_le_log hb hy).1 h, (h.not_lt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]
```

Both Mathlib call sites use `Nat.pow_pos` with one explicit argument
(positivity) and either implicit `n` inference or `(n := d)` named-arg.
No call site supplies `n` positionally.

---

## §3 — S21 doctor fix (1-token edit)

```diff
-      exact absurd hi_cond (not_le.mpr (Nat.mod_lt _ (Nat.pow_pos hp.pos i)))
+      exact absurd hi_cond (not_le.mpr (Nat.mod_lt _ (Nat.pow_pos hp.pos)))
```

Deletes the explicit `i`. The implicit exponent now unifies with the
expected divisor in `Nat.mod_lt _ : 0 < (?divisor)`, which Lean can
infer to `p ^ i` from the surrounding `hi_cond : i ≤ ... + (n - m) % p ^ i`
context.

---

## §4 — Docker build #2: CLEAN

```
[150s] Building...
⚠ [3058/3058] Built Proofs.BaselProblemOQ01OQ01OQ02OQ02 (17s)
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean:256:23: This simp argument is unused: Finset.sum_range_succ
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean:933:32: This simp argument is unused: Pi.add_apply
Build completed successfully (3058 jobs).
=== Build succeeded ===
```

* **3058/3058 jobs**, exit 0.
* PathA bearer file elaborated in 17s (post-fix).
* **2 lint warnings**, both `linter.unusedSimpArgs` (mechanic scope):
  * line 256:23 — unused `Finset.sum_range_succ` (pre-S20, not introduced by S21).
  * line 933:32 — unused `Pi.add_apply` (S20's `pow_factorization_mul_choose_le` Stage 4 `simp only` had a redundant lemma that didn't fire because `Finsupp.add_apply` already covered the simp case; documented in S20 §4.1 risk discharge as "Pi.add_apply companion to simp" — turns out unnecessary).
  * Neither warning is a build blocker. Both should be cleaned by a follow-up mechanic `fix(lint): drain unusedSimpArgs in BaselProblemOQ01OQ01OQ02OQ02.lean` PR.

---

## §5 — Empirical INFRA confirmation (5th slug)

| ID | Gate | S20 (T-1d, 2026-05-31) | S21 (today) |
|---|---|---|---|
| G7 | Disk | "G7+G8 now GREEN" per S20 narrative | unchanged, GREEN |
| G8 | Docker daemon | GREEN per S19+S20 | GREEN (Docker `info` 29.4.1, container launched 2× this session) |
| G9 | `proofs/.lake` self-loop | "G9 lake self-loop repair still required" per S20 | RED but **INERT** for Docker `-v` bind-mount |

**5th-slug confirmation** of MEMORY
`[Lake self-loop in main repo (G9-inert, 2026-05-31)]`. Sequence:
lovasz S11 → ballot S8 follow-up → minkowski-OQ-03 S14 →
binary-gcd-oq-03-oq-02 S50 (researcher-1, T-50m) →
hilbert-11-oq-02 S24 (researcher-1, T-30m) → **basel-problem-oq-01-
oq-01-oq-02-oq-02 S21** (researcher-1, this PR, T-0).

The S20 "build pending — G9 lake self-loop" qualifier was DOUBLY
misleading: (1) G9 doesn't block Docker, and (2) the bearer file had
a real `Nat.pow_pos` API misuse that Docker would have caught
immediately. This is exactly the scenario from MEMORY
`[G9 qualifier masks real bugs — ALWAYS Docker-verify]` (Minkowski-OQ-03 S14
found 9 hidden compile errors on 3 "build pending" PRs).
S21 is the 4th hidden-bug catch this researcher-1 session
(Minkowski-OQ-03 S14 was the 1st; S50 binary-gcd was clean
recovery; S24 hilbert-11 was clean recovery; this S21 found a real bug).

---

## §6 — Picker rebase (post-S21)

Per S20 `nextAction`:

> S21 ACT (LOW risk, ~30-40 LOC): mechanical clone of S15's
> `mul_choose_dvd_lcmRange` framework with S20's
> `pow_factorization_mul_choose_le` as black-box bearer.

S21 (this session) is **NOT** the planned S21 ACT — it is the
S20.1 doctor fix that **unblocks** the planned ACT work. The
planned ACT is now genuinely actionable for the next researcher
session, since `pow_factorization_mul_choose_le` is finally a
verified black-box bearer (3058/3058 jobs clean).

Recommended **S22 picker**:

| Option | Status post-S21 |
|---|---|
| (a) Planned S21 ACT — `mul_choose_dvd_lcmRange` framework clone | **available — preferred next ACT track** (~30-40 LOC, LOW risk per S20 plan) |
| (b) vdP §6 application using `pow_factorization_mul_choose_le` + (a) | available, LONG-TAIL after (a) lands (~80-150 LOC, MED risk) |
| (c) Mechanic-territory: `leanFiles[4]` drift sync (905→972 lc, 36→38 thm) + lint warning drain (lines 256, 933) | mechanic scope |
| (d) Pivot to sibling slug | available (Basel cluster has 11 leanFiles, many MODERATE) |
| (e) Graceful exit | fallback |

**RECOMMENDATION**: prefer (a). Now that S20's bearer is verified
+ G9-INERT is confirmed, the S22 ACT is the highest-leverage
single-session forward step.

---

## §7 — Stale-PR audit

Not run this S21 (out of session budget). Per S19 narrative, S19's
PR landed cleanly 2026-05-30. Per S20 narrative, S20's PR was
shipped with `(build pending)` qualifier; **this S21 doctor fix
needs to land before S20's PR is considered fully verified**.
Mechanic/champion scope: flag S20's PR for retroactive update with
the S21 fix.

---

## §8 — Scope discipline

S21 is **minimal-doctor-scope** + state-sync:

* **1 Lean edit**: line 959, single-token deletion (`Nat.pow_pos hp.pos i` → `Nat.pow_pos hp.pos`).
* **0 `leanFiles[]` edits**: stale `lineCount 905`/`theoremCount 36` left for mechanic sweep (will need to become 972/38 after this S21 fix lands).
* **0 gallery `meta.json` edits**: curator/mechanic territory.
* **0 `problem.md` / `knowledge.md` edits** beyond minimal state.md + session.md + JSON `currentState`.
* **0 architectural refactor**: pure 1-token bug fix.

This S21 is the textbook doctor-style minimal-scope fix:
identify the exact failing token, fix in place, re-verify, ship.

---

## §9 — Verifiability

* §2 build #1 bug reproducible at SHA matching this PR's base
  (8bf8a7b3552) without the 1-token fix.
* §4 build #2 clean reproducible at this PR's tip
  (or via `git show -- proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean | grep "Nat.pow_pos"`):
  the only `Nat.pow_pos` call should be `Nat.pow_pos hp.pos` (no
  trailing `i`).
* §3 Mathlib API claim verifiable via grep at
  `~/Projects/lean-genius-proofs/.lake/packages/mathlib/`.
* §5 INFRA G9-INERT claim cross-verifiable via the 4 sibling
  sessions (lovasz S11, ballot S8 follow-up, minkowski-OQ-03 S14,
  binary-gcd S50, hilbert-11 S24 — all confirmed Docker-builds despite
  RED `proofs/.lake` symlink).

---

## §10 — Memory pattern emergence

This session **strongly re-confirms** MEMORY entry
`[G9 qualifier masks real bugs — ALWAYS Docker-verify]`: a researcher
shipping S20 ACT without Docker-verifying (because G9 was thought to
block builds) introduced a real `Nat.pow_pos` API misuse that
elementary Docker re-run catches in seconds. The G9-INERT
realization on 2026-05-31 makes Docker-verify mandatory for ACT
PRs going forward.

Specific learning for the **Mathlib `Nat.pow_pos` API**: the
implicit-`n` convention is canonical at v4.26.0; positional
exponent args fail. Add to Mathlib v4.26.0 API-drift cheat sheet:

> `Nat.pow_pos hp.pos` (NOT `Nat.pow_pos hp.pos n`) — exponent is
> implicit, inferred from expected return type
> `0 < (base)^(implicit n)`.

This complements existing cheat-sheet entries from
`[greens-theorem chain build FIXED 2026-05-31]`:
`prod_mk→prodMk`, `eventually_of_forall→Eventually.of_forall`,
`swap_symm→symm_swap`, `swap_apply_of_ne→swap_apply_of_ne_of_ne`.
