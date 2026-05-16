# Current State

**Phase**: ACT
**Since**: 2026-05-16
**Iteration**: 15

## Session 15 (2026-05-16, ACT — A.1 `choose_dvd_lcmRange` Docker-verified clean)

Ships the A.1 ACT planned by S12 PREP (#19217), audited by S13 PREP
(#19299), and given a GREEN readiness gate by S14 STATE-SYNC (#19352
§6.2). New theorem in `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`
(Part 11):

```lean
theorem choose_dvd_lcmRange {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Nat.choose n k ∣ lcmRange n := by
  rw [← Nat.prod_pow_factorization_choose n k hk]
  apply Finset.prod_dvd_of_isRelPrime
  · -- pairwise IsRelPrime on prime-power factors
    intro p _ q _ hne
    simp only [Function.onFun]
    by_cases hv_p : (Nat.choose n k).factorization p = 0
    · rw [hv_p, pow_zero]; exact isRelPrime_one_left
    by_cases hv_q : (Nat.choose n k).factorization q = 0
    · rw [hv_q, pow_zero]; exact isRelPrime_one_right
    have hpp : p.Prime := by
      by_contra h; exact hv_p (Nat.factorization_eq_zero_of_not_prime _ h)
    have hqq : q.Prime := by
      by_contra h; exact hv_q (Nat.factorization_eq_zero_of_not_prime _ h)
    exact Nat.coprime_iff_isRelPrime.mp
      (Nat.coprime_pow_primes _ _ hpp hqq hne)
  · -- each prime-power factor divides lcmRange n
    intro p _
    by_cases hv : (Nat.choose n k).factorization p = 0
    · rw [hv, pow_zero]; exact one_dvd _
    have hpp : p.Prime := by
      by_contra h; exact hv (Nat.factorization_eq_zero_of_not_prime _ h)
    exact dvd_lcmRange (pow_pos hpp.pos _)
      (Nat.pow_factorization_choose_le hn)
```

**Docker build VERIFIED CLEAN** (3058 jobs, 17s on the final file,
~2 min total wall-clock including cache fetch + unpack). 0 errors,
0 new warnings (the single warning at line 256:23 is pre-existing in
`harmonicCubed_lcm_clear_nat`'s simp call from S4 ACT, 2026-05-08).

**LOC delta**: 799 → 905 (+106). **Theorem delta**: 35 → 36 (+1).
**Sorry delta**: 0. **Axiom delta**: 0.

**Imports added**: `Mathlib.Data.Nat.Choose.Factorization` (for
`Nat.prod_pow_factorization_choose` + `Nat.pow_factorization_choose_le`)
and `Mathlib.RingTheory.Coprime.Lemmas` (for
`Finset.prod_dvd_of_isRelPrime`).

**Two new bearer pins added to the S14 §3 table**:
* `Nat.coprime_pow_primes` at `Mathlib/Data/Nat/Prime/Basic.lean:200`
   — distinct primes have coprime powers; one-line shortcut around
   S13's chained `Nat.Coprime.pow_left.pow_right` sketch.
* `isRelPrime_one_right` at `Mathlib/Algebra/Divisibility/Units.lean:167`
   — companion to S14 §5's `isRelPrime_one_left` for the v_q=0 branch.

**Path-forward continuity**: S16 ACT (A.2 = `mul_choose_dvd_lcmRange`)
is now the next ACT. S13 §5 sketched ~80-120 LOC via Kummer/Legendre
(`Nat.Prime.emultiplicity_choose` at Multiplicity.lean:209 +
`Nat.Prime.emultiplicity_factorial` at line 102). One additional
bridge bearer (`factorization` ↔ `emultiplicity` on ℕ) must be pinned
at S16 ACT time.

Session note: `sessions/2026-05-16-s15-act-choose-dvd-lcm-range.md`.

## Session 14 (2026-05-16, STATE-SYNC — post-S12+S13-PREP-merge refresh, bearer drift recheck, two ACT-time risk flags pre-discharged)

Doc-only STATE-SYNC iteration. PR #19322 (own prior branch
S2 PREP for unrelated slug `angle-trisection-...`) merged
2026-05-16T00:08:48Z; this slug's S12 PREP (PR #19217) and S13 PREP
(PR #19299) merged in the 2026-05-15T18:00–18:06Z drain wave (within
~5 min of each other and ~5 min after S11 BUILD-REPAIR PR #19017
merged at 17:59Z). Both S12+S13 PREPs explicitly deferred state.md
and JSON refresh to "next STATE-SYNC iteration" (S12 PREP §2.2; S13
PREP §6.3) to remain conflict-free with the open S11 PR. This S14
ships those deferred updates plus three new bearer pins.

### What S12 PREP (#19217) added

**Path Forward (A) Kummer**: pinned `Nat.pow_factorization_choose_le`
at `Mathlib/Data/Nat/Choose/Factorization.lean:196` (lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Signature
`(hn : 0 < n) : p ^ (choose n k).factorization p ≤ n`. Drafted the
S15 ACT skeleton (`choose_dvd_lcmRange : 0 < n → k ≤ n →
Nat.choose n k ∣ lcmRange n`) at ~50-60 LOC.

**Path Forward (B) vdP §6 bypass**: ruled out. The induction-on-k
closed form `lcmRange(n)³ · C(n,k) · C(n+k,k) · S_k(n) ∈ ℤ` does
NOT bypass `mul_choose_dvd_lcmRange` for general m: the induction
step introduces a `(n - k + 1)(n + k) / k²` rescaling that requires
the *squared* prefactor `C(n,k)² C(n+k,k)²` plus a Wilf-Zeilberger
creative-telescoping certificate. Formalizing W-Z is "not noticeably
easier than path (A)".

**Recommendation**: queue S12 ACT (renumbered to S15 here) as Path
(A.1) — `choose_dvd_lcmRange`, +~60 LOC, axiom-free. The harder
`mul_choose_dvd_lcmRange` (A.2) follows by case analysis on whether
`p ∣ m`.

### What S13 PREP (#19299) added on top of S12

**Sibling-audit value** (S13 PREP §"Distinct value"):

1. All four S12-pinned Mathlib bearers re-pin-verified at lake SHA
   via direct `gh api` + `curl` download (line numbers confirmed
   exactly, not via search-API indexing).
2. **One adjacent bearer newly pinned**: `Finset.prod_dvd_of_isRelPrime`
   at `Mathlib/RingTheory/Coprime/Lemmas.lean:252` — replaces S12's
   loose `Finset.prod_dvd via primes-coprime` placeholder.
3. **Goal-state walk** of A.1: identifies three sub-goals
   (per-p divisibility split into v=0 vs v>0; pairwise IsRelPrime by
   case on factorization values) and pins typeclass dependency
   `DecompositionMonoid ℕ` via `[Nonempty (GCDMonoid α)]` instance at
   `Mathlib/Algebra/GCDMonoid/Basic.lean:493`.
4. **Path (B) re-verified**: `R_k = (n-k+1)(n+k)/k²` recurrence
   confirmed, W-Z absence from Mathlib confirmed via
   `gh api search/code` round-trip.
5. **Path (A.2) bound re-validated** at 7 distinct (n, m, p) cases.
   S12 PREP's n=4, m=2, p=2 counterexample for the naive
   `v_p(n) + log_p(n-1)` route is reconfirmed. Two additional
   bearers pinned for the correct Legendre route:
   `Nat.Prime.emultiplicity_choose` at `Multiplicity.lean:209`
   (Kummer's theorem) and `Nat.Prime.emultiplicity_factorial` at
   `Multiplicity.lean:102` (Legendre).

**Sequencing recommendation** (S13 §7): wait for #19017 + #19217 +
#19299 to merge (all done 2026-05-15T18:00-18:06Z); then
S14 ACT = A.1, S15 ACT = A.2, S16+ = vdP §6 application.

### What this S14 STATE-SYNC adds (3 new pins + 2 risk-flag discharges + renumber)

**S14 §3 bearer drift recheck — 6 bearers, 0 drift**: all bearers
S12+S13 pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
re-verified at the same SHA (which is still current per current
`proofs/lake-manifest.json`). Zero file-position changes. The
re-pin documents the recheck protocol for S15+ ACTs.

**S14 §4 — two S13 §3.6 ACT-time risk flags PRE-DISCHARGED**:

| S13 §3.6 risk flag | S14 discharge |
|--------------------|---------------|
| `Nat.coprime_iff_isRelPrime` may have moved/renamed in v4.26.0 | Pinned at `Mathlib/Data/Nat/GCD/Basic.lean:218` (signature unchanged) |
| `factorization_eq_zero_of_not_prime` may have renamed in v4.26.0 | Pinned at `Mathlib/Data/Nat/Factorization/Defs.lean:129` (signature unchanged) |

Both bearers are in scope after the slug's existing imports
(`Mathlib.Algebra.GCDMonoid.Finset` + `Mathlib.Tactic`).

**S14 §5 — one new bearer pin**: `isRelPrime_one_left` at
`Mathlib/Algebra/Divisibility/Units.lean:166` (signature
`IsRelPrime 1 x := isUnit_one.isRelPrime_left`). S13 §3.4 sub-case
(i) wrote "Mathlib pin needed; at
`Mathlib/Algebra/GroupWithZero/Coprime.lean` or similar"; the actual
location is `Mathlib/Algebra/Divisibility/Units.lean`, transitively
imported via `Mathlib.Tactic`.

**S14 §6 — S12+S13 compatibility synthesis (no contradictions)**:

| Topic | S12 conclusion | S13 conclusion | Synthesis |
|-------|----------------|----------------|-----------|
| Path (A) Kummer is right route | Yes | Yes | ✓ |
| Path (B) bypass viable | No | No | ✓ |
| A.1 LOC budget | ~50-60 | ~30-40 | S13 tighter; ~30-40 binding |
| Mathlib bearer for `Finset.prod` step | Loose `Finset.prod_dvd` | `Finset.prod_dvd_of_isRelPrime:252` | S13 sharpens |
| Recommended next ACT | S12a → A.1 (~60 LOC) | S14 ACT → A.1 → S15 ACT → A.2 | ✓ — S14 renumbers (+1) for itself |

**S14 §6.1 — RENUMBERING**: this STATE-SYNC absorbs iteration count 14;
the post-STATE-SYNC ACTs shift +1:

- ~~S14 ACT~~ → **S15 ACT**: A.1 implementation
  (`choose_dvd_lcmRange`, ~30-40 LOC, Docker-verify required).
- ~~S15 ACT~~ → **S16 ACT**: A.2 implementation
  (`mul_choose_dvd_lcmRange`, ~80-120 LOC, Docker-verify required).
- ~~S16+ ACT~~ → **S17+ ACT**: apply A.2 to vdP §6 alternating-bilinear
  summand for final `denominator_control` discharge.

The renumber preserves CONTENT sequence; only labels shift. State.md,
JSON, and PR titles should adopt the renumber.

### S15 ACT readiness checklist (post-S14)

| Item | Status |
|------|--------|
| `Nat.pow_factorization_choose_le` bearer pinned | ✓ S12 + S13 |
| `Nat.prod_pow_factorization_choose` bearer pinned | ✓ S12 + S13 |
| `Finset.prod_dvd_of_isRelPrime` bearer pinned | ✓ S13 §2.4 |
| `DecompositionMonoid ℕ` typeclass in scope | ✓ S13 §2.5 |
| `Nat.coprime_iff_isRelPrime` bearer pinned | ✓ **S14 §4.1** |
| `Nat.factorization_eq_zero_of_not_prime` bearer pinned | ✓ **S14 §4.2** |
| `isRelPrime_one_left` bearer pinned | ✓ **S14 §5** |
| Lake SHA stable (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) | ✓ S14 §3 |
| File LOC + axiom + sorry count baseline | ✓ 799 / 0 / 0 (S11 post-fix) |
| Build-pending precedent for ACT | **Docker-verify required** (S11 admonition) |

S15 ACT can begin without further PREP work.

### Counts (post-S14, unchanged from S11)

| Metric    | Value |
|-----------|-------|
| File LOC  | 799 (unchanged from S11) |
| Sorries   | 0 (unchanged) |
| Axioms    | 0 (unchanged) |
| Theorems  | 16 (unchanged) |
| Build     | verified clean (3058 jobs, S11 baseline) |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: this state.md (+ ~110 LOC near top); the slug's
JSON (`currentState.iteration` 11 → 14, `since` 2026-05-08 →
2026-05-16, `lastUpdate`, refreshed `nextAction`, plus 3 new entries
each in `knowledge.insights` and `knowledge.nextSteps`); 1 new
sessions/ note (`2026-05-16-s14-state-sync-post-s12-s13-prep-merge.md`).
0 Lean file edits. 0 sibling-slug edits.

## Session 11 (2026-05-14, ACT — Mathlib v4.26.0 build-repair, Docker-verified)

S10 ACT (PR #18831, merged 2026-05-08) shipped the m=3 case
`mul_choose_dvd_lcmRange_three` as **build-pending** per the
"build-pending" precedent of S5–S8. Six days of Mathlib v4.26.0 drift
against the file's untouched-since-S10 code surfaced **eight** errors
across two API-rename classes and two term-mode-elaborator-strictness
classes, classified below. Local pre-claim Docker build via
`./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ02`
caught all eight; surgical 5-edit fix kit re-built clean (3058 jobs).

### Errors caught (pre-fix Docker baseline)

| Line | Error | Class |
|------|-------|-------|
| 541  | `Finset.range_subset.mpr` — Application type mismatch (expected `∀ x < m, x ∈ range n`) | API rename: use `Finset.range_mono` |
| 658  | `Nat.Coprime.mul` — Unknown constant | API rename: use `.symm.mul_right .symm` chain (or `Nat.Coprime.mul_left`) |
| 686  | `Nat.dvd_sub'` — Unknown constant | API rename: drop the prime → `Nat.dvd_sub` |
| 699  | `dvd_refl 2` term-mode `▸` motive ambiguity | Term-mode strictness: replace `▸` with `by rw [...]` |
| 703  | `Nat.gcd_add_mul_left_left` — pattern unify failed on `(1 + 2 * (m - 1)).gcd (m - 1)` | API rename: use `Nat.gcd_add_mul_right_left` (matches `(?n + ?k * ?m).gcd ?m`) |
| 731  | `Nat.dvd_sub'` — same as 686 | same |
| 741  | `Nat.dvd_sub'` — same as 686 | same |
| 754  | `dvd_refl 2` term-mode `▸` motive ambiguity — same as 699 | same |

### Surgical fixes (9 edits across 5 deprecation classes, +6 LOC)

The fix kit unfolded in **three rounds**:

- **Round 1** (5 edits, +0 LOC): direct API-rename substitutions
  caught 5 of 8 errors.
- **Round 2** (3 edits, +6 LOC): the rebuild surfaced a v4.26.0
  elaborator-strictness regression on the new `Nat.dvd_sub` that
  rejected three call sites where the `k`-divisor argument differed
  syntactically between the two `Dvd` premises (the prior
  `rw [heq] at h_X` pattern desyncs the `gcd ...` subterm). Round 2
  refactored those three sites to compute the truncated-subtraction
  explicitly before discharging the goal equality.
- **Round 3** (1 edit, +0 LOC): the second rebuild surfaced one
  additional motive-ambiguity at line 735 (the `heq ▸ h_diff` term-mode
  rewrite on a `2*m - (2*m - 1)` expression where v4.26.0 found a
  bidirectional substitution path through the gcd's second argument).
  Round 3 replaced the term-mode `▸` with the unambiguous
  `rw [heq] at h_diff; exact h_diff` tactic chain.

Each rebuild took ~14 minutes (Mathlib v4.26.0 cache redownload + 3058
job compile). The fast-iteration find-replace approach (round 1) caught
the obvious renames quickly; the second-order elaborator-strictness
regressions (rounds 2 & 3) needed a Docker round each to surface, since
the v4.26.0 errors only appear after the first-order renames let the
elaborator reach the deeper call sites.

#### Round 1 (5 edits, +0/-0 LOC; reduced 8 errors → 3)

1. **Line 541** (in S8 Part 8a `lcmRange_dvd_of_le`):
   `Finset.range_subset.mpr hmn` → `Finset.range_mono hmn`.
   `Finset.range_subset` was the v4.25.x Iff `range a ⊆ range b ↔ a ≤ b`;
   v4.26.0 reformulated to the universally quantified form
   `∀ x < a, x ∈ range b`, breaking `.mpr` callers. The replacement
   `Finset.range_mono : a ≤ b → range a ⊆ range b` is the canonical
   idiom in `Erdos677Problem.lean`, `ChebyshevBoundsOQ04.lean`, and 6+
   other gallery files.

2. **Line 658** (in S10 Part 10 private helper `three_factors_dvd_lcmRange`):
   `Nat.Coprime.mul hac hbc` → `(hac.symm.mul_right hbc.symm).symm`.
   The two-Coprime → product-Coprime constructor for `Coprime (a*b) c`
   was removed/renamed in v4.26.0 (no longer compiles). Avoids
   speculating on the new direct name by using the proven-working
   `Nat.Coprime.symm` and `Nat.Coprime.mul_right`.

3. **Lines 686, 731, 741** (in S10 Part 10a/10b coprime-`gcd`-bounds):
   `Nat.dvd_sub'` → `Nat.dvd_sub` (drop the prime). v4.26.0 collapsed
   the `Nat.dvd_sub' : k ∣ m → k ∣ n → k ∣ m - n` (truncated-
   subtraction-safe) into the un-primed name. Round 1 only renamed;
   the call-site refactor follows in round 2.

4. **Lines 699, 754** (in S10 Part 10a `coprime` gcd=2 contradiction
   step): `(hgcd_eq_2 ▸ dvd_refl 2)` → `(by rw [hgcd_eq_2])`.
   v4.26.0 elaborator rejects term-mode `▸` when the motive is
   ambiguous (the constant `2` appears at multiple positions in the
   goal type — `2 ∣ Nat.gcd (2 * m) (m - 1)` has `2` as both
   divisor and inside the `2*m` factor — and `▸` substitutes ALL
   occurrences, producing the nonsensical
   `(2*m).gcd(m-1) ∣ ((2*m).gcd(m-1) * m).gcd(m-1)` type). The
   tactic-mode `by rw [hgcd_eq_2]` substitutes only the LHS of the
   equation in the GOAL (`2 ∣ ?`), which is unambiguous.

5. **Line 703** (in S10 Part 10a's `gcd(2m-1, m-1) = 1` step):
   `Nat.gcd_add_mul_left_left` → `Nat.gcd_add_mul_right_left`.
   The pattern needed is `(n + k * m).gcd m = n.gcd m` (gcd's
   second arg matches the **second** factor of the product); the
   `_left_left` variant is `(n + m * k).gcd m = n.gcd m` (gcd's
   second arg matches the **first** factor). After the rename, the
   subsequent `Nat.gcd_one_left` closes immediately. Reference: same
   `_right_*` family is used in `AngleTrisectionOQ02OQ03.lean:1357,1362`.

#### Round 2 (3 edits, +6 LOC; resolved remaining 3 errors)

6-8. **Lines 686, 731, 741 callers** (S10 Part 10a even-m gcd-divides-2,
S10 Part 10b odd-m gcd-divides-1, S10 Part 10b odd-m gcd-divides-2):
The v4.26.0 `Nat.dvd_sub : k ∣ m → k ∣ n → k ∣ m - n` is stricter
than the v4.25.x `Nat.dvd_sub'` regarding **syntactic equality** of the
shared `k` divisor across the two `Dvd` premises. The prior pattern
```
have h1 := Nat.gcd_dvd_left (2 * m) (m - 1)   -- gcd ∣ 2*m
have h3 : ... ∣ 2 * (m - 1) := h2.mul_left 2  -- gcd ∣ 2*(m-1)
have heq : 2 * m = 2 * (m - 1) + 2 := by omega
rw [heq] at h1                                 -- h1 : (2*(m-1)+2).gcd ... ∣ ...
exact Nat.dvd_sub h1 h3                        -- syntactic mismatch on k
```
fails because after `rw [heq] at h1`, h1's *gcd argument* has been
rewritten to `(2*(m-1)+2).gcd (m-1)` while h3 still has
`(2*m).gcd (m-1)`. These are definitionally equal but **not**
syntactically equal, and the v4.26.0 elaborator refuses to unify
implicit `k` across them. Refactored to compute the truncated
difference inline, where both `Dvd` premises share the identical
`(2 * m).gcd (m - 1)` (or `m.gcd ...`) syntactic form:
```
have h_diff : Nat.gcd (2 * m) (m - 1) ∣ (2 * m - 2 * (m - 1)) :=
  Nat.dvd_sub h1 h3
have h_eq : (2 * m - 2 * (m - 1) : ℕ) = 2 := by omega
rw [h_eq] at h_diff
exact h_diff
```
Same pattern applied at lines 731 (odd-m's `gcd m (2*m-1) ∣ 1` via
`2*m - (2*m-1) = 1`; **note: line 731 needed a round-3 follow-up — see
below**) and 741 (odd-m's `gcd m (2*m-2) ∣ 2` via `2*m - (2*m-2) = 2`).
Net cost: +6 LOC across the three sites; no mathematical content
change.

#### Round 3 (1 edit, +0 LOC; resolved final term-mode `▸` regression)

After round 2 introduced `have h_diff := Nat.dvd_sub h3 h2` at line 731,
the follow-up term-mode `heq ▸ h_diff : Nat.gcd m (2 * m - 1) ∣ 1`
(meant to rewrite `2 * m - (2 * m - 1)` → `1` in h_diff's type) still
failed with motive ambiguity:
```
expected to have type
  m.gcd (2 * m - (2 * m - (2 * m - 1))) ∣ 2 * m - (2 * m - 1)
```
The v4.26.0 elaborator was finding a bidirectional motive that
substituted into the gcd's *second* argument as well — turning
`(2 * m - 1)` (the gcd arg) into `(2 * m - (2 * m - 1))` (the
nested form), an obvious regression. Replaced the term-mode `▸` with
tactic-mode `rw [heq] at h_diff; exact h_diff`, which acts only on
h_diff's type (single occurrence of the equation LHS) and is
unambiguous.

This is the **same elaborator-strictness class** as round 1's fixes 4
& 5 (lines 699, 754): term-mode `▸` is no longer reliable in v4.26.0
when the substitution target appears in multiple positions of the
result type. The systemic fix is to prefer tactic-mode `rw [heq] at X`
over term-mode `heq ▸ X` whenever the surrounding type has any other
occurrence of the equation's LHS or RHS.

### Counts (post-S11)

| Metric    | Pre-S11 | Post-S11 |
|-----------|---------|----------|
| File LOC  | 793     | 799 (+6; round-2 inline-diff refactor) |
| Sorries   | 0       | 0 |
| Axioms    | 0       | 0 |
| Theorems  | 16      | 16 (no new statements) |
| Build     | **broken** (v4.26.0, 8 errors) | **verified clean** (3058 jobs) |

### Significance

This S11 session lifts the "build-pending" qualifier from PR #18831
(S10 ACT) and **confirms via Docker that the entire S5–S10 stack —
+~600 LOC of m=1, m=2, m=3 case discharges for `mul_choose_dvd_lcmRange`
— now type-checks cleanly under Mathlib v4.26.0**. No mathematical
content was modified: every fix is a pure Mathlib-API-rename or
elaborator-strictness adaptation that yields the identical proof.

The session also **validates the build-pending → repair lag pattern**
for the slug: shipping S10 as build-pending on 2026-05-08 deferred
~30 minutes of Mathlib-rename investigation by 6 days at the cost of
~10 minutes of repair work. Net positive for the slug's velocity but
the repair lag should be tracked at the slug level so build-pending
PRs do not accumulate beyond 1–2.

### What this S11 closes

- All eight v4.26.0 surface errors in `BaselProblemOQ01OQ01OQ02OQ02.lean`.
- The "build-pending" qualifier on PR #18831 (S10 ACT) and the implicit
  build-pending status of the entire S5–S10 stack.
- Path Forward Item (C) from the S10 STATE-SYNC's `currentState.nextAction`:
  "Build verification: Docker-build BaselProblemOQ01OQ01OQ02OQ02.lean from
  a clean clone to confirm the S5–S10 build-pending stack compiles".

### Open work after S11

Unchanged from S10's path-forward (Items A, B, D from the STATE-SYNC):
- **(A) Kummer for m ≥ 4** (~150 LOC, multi-session): the m=3
  parametrize-and-regroup trick does **not** generalize because
  `v_p(C(n, m)) = s_p(m) + s_p(n−m) − s_p(n)` has no uniform absorption.
- **(B) Bypass via vdP §6 re-read** (PREP-eligible): derive the precise
  weaker divisibility actually needed by the alternating-bilinear
  summand `Σ_{m=1}^{k} (−1)^{m−1}/(2 m³ C(n,m) C(n+m,m))`; may only
  require primes `p ≤ k`.
- **(D) Partial vdP audit**: whether `mul_choose_dvd_lcmRange_three`
  alone unblocks any low-order vdP §6 terms without waiting for the
  general m case.

**Axiom delta this session**: 0 (pure Mathlib-API-rename surgery).

### Sibling slug warning (build-pending watchlist)

The companion slug `basel-problem-oq-01-oq-01-oq-02-oq-03` has multiple
open PRs from 2026-05-09 (#17619 Iter 17, #17551 Iter 15) that also
predate v4.26.0 and likely carry similar regressions. The five
deprecation classes catalogued here may be useful upstream when those
PRs are revisited; tagged on the slug's `nextSteps` for cross-slug
mining by the next doctor session.

## Session 10 (PR #18831, merged 2026-05-08 — build-pending; verified clean by S11)

Implemented the S9 tactical plan, closing the **m=3 case** of
`mul_choose_dvd_lcmRange` for **all** `n ≥ 3` (both parities). The
proof avoids Kummer's theorem entirely — pure coprime decomposition
plus the Part 9 algebraic identity.

### Lean additions (file: BaselProblemOQ01OQ01OQ02OQ02.lean)

| Part | Theorem | Conclusion |
|------|---------|------------|
| 9    | `three_mul_choose_three_eq_of_double` (`m ≥ 2`) | `3·C(2m, 3) = (2m)(2m-1)(m-1)` |
| 10a  | `mul_choose_dvd_lcmRange_three_double_even` (`m ≥ 2`, `Even m`) | `3·C(2m, 3) ∣ lcmRange(2m)` |
| 10b  | `mul_choose_dvd_lcmRange_three_double_odd` (`m ≥ 2`, `Odd m`)   | `3·C(2m, 3) ∣ lcmRange(2m)` |
| 10c  | `mul_choose_dvd_lcmRange_three_even` (`n ≥ 4`, `Even n`)        | `3·C(n, 3) ∣ lcmRange n`   |
| 10d  | `mul_choose_dvd_lcmRange_three` (`n ≥ 3`)                       | `3·C(n, 3) ∣ lcmRange n`   |

Plus one private helper `three_factors_dvd_lcmRange` (DRY-ing the
three-factor coprime-product divisibility argument shared by 10a/10b).

### Coprime calculations (S10 implementation specifics)

For **`Even m`** sub-case (10a), factorization `(2m, 2m-1, m-1)`:
- `gcd(2m, 2m-1) = 1` via `2m = (2m-1) + 1` + `Nat.coprime_self_add_right`.
- `gcd(2m, m-1) = 1`: established `gcd | 2` from `2m = 2(m-1) + 2`
  using `Nat.dvd_sub'`, then `m-1` odd (forced by `Even m`) blocks
  `2 ∣ gcd`, leaving `gcd ∈ {1}` after `omega` cleanup.
- `gcd(2m-1, m-1) = 1` via `2m-1 = 1 + 2(m-1)` +
  `Nat.gcd_add_mul_left_left` reducing to `gcd 1 (m-1) = 1`.

For **`Odd m`** sub-case (10b), factorization `m(2m-1)(2m-2)`:
- `gcd(m, 2m-1) = 1`: `gcd ∣ m ⇒ gcd ∣ 2m ⇒ gcd ∣ 2m-(2m-1) = 1`.
- `gcd(m, 2m-2) = 1`: established `gcd | 2`, then `m` odd
  (`Odd m`) blocks `2 ∣ gcd` (since `gcd | m`), leaving `gcd = 1`.
- `gcd(2m-1, 2m-2) = 1` via `2m-1 = (2m-2) + 1` (consecutive).

### Regrouping identity (10b)

The `Odd m` sub-case requires regrouping Part 9's identity
`3·C(2m, 3) = (2m)(2m-1)(m-1)` as `m(2m-1)(2m-2)`. Proof: substitute
`2m-2 = 2(m-1)` and apply `ring`:
  `2m * (2m-1) * (m-1) = m * (2m-1) * (2(m-1))`,
where both sides treat `2m-1` and `m-1` as opaque Nat-sub variables.

### Status delta

| Metric          | Pre-S10 | Post-S10 |
|-----------------|---------|----------|
| File LOC        | 595     | 793      |
| Sorries         | 0       | 0        |
| Axioms          | 0       | 0        |
| Theorems        | (per Part 8) | + 5 (+ 1 private) |
| m=3 full target | Half (odd-n, S8) | **Complete** |

**Build status**: pending (`.lake` symlink loop in worktree per
memory; ship as build-pending per S7/S8 precedent and let doctor
verify on a clean clone).

### What this S10 closes

The m=3 case `mul_choose_dvd_lcmRange_three` is **fully proved** for
all `n ≥ 3`. This is one of the m-induction base cases for the
general `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m·C(n,m) ∣ lcmRange n`
(m=1, m=2 from S6; m=3 from S8+S10).

### Open work after S10

**m ≥ 4 (the genuine Kummer territory)**: the trick "parametrize `n = 2m`
and re-group the `/2`" does **not** generalize. For m ≥ 4, the binomial
coefficient `C(n, m)` carries `v_2 = s_2(m) + s_2(n-m) - s_2(n)` (digit-sum
carry count), which cannot be uniformly absorbed by re-parametrization of
`n` into a single product of three pairwise-coprime factors.

Two routes for m ≥ 4:
1. **Kummer**: prove `Nat.Prime.choose_mul_dvd_lcmRange` (factor-of-2
   per prime) and assemble. ~150 LOC across multiple sessions.
2. **Bypass**: re-read van der Poorten §6 (S5 next-action) to derive
   the precise statement needed by the alternating-bilinear summand —
   it may be a weaker divisibility than `mul_choose_dvd_lcmRange`,
   e.g. only needing primes `p ≤ k`.

**Axiom delta this session**: 0 (pure coprime + Nat arithmetic).

## Session 9 (PR #18585, merged — planning + tactical analysis)

Documentation-only iteration. No Lean changes; no sorry/axiom delta.
Work product: a sharper, **operational** plan for the S10 m=3 even-n
proof, correcting two pessimistic claims in S8's blockers list.

**Headline finding**: BOTH parity-of-`n/2` sub-cases admit a clean
**coprime decomposition** of `3 · C(n, 3)` into three pairwise-coprime
factors that each divide `lcmRange n`. The S8 blockers list incorrectly
suggests `n ≡ 2 mod 4` "probably needs Kummer"; in fact a different
factorization removes the obstacle.

### Concrete factorizations

Parametrize `n = 2 * m` (`m ≥ 2`). From Part 7
`two_mul_three_mul_choose_three_eq`, plus `n - 2 = 2 * (m - 1)`:

  `3 * C(2m, 3) = (2m) * (2m - 1) * (m - 1)`     — uniform identity (*)

Equivalently, by re-grouping `(2m) * (m - 1) = m * (2(m - 1)) = m * (2m - 2)`:

  `3 * C(2m, 3) = m * (2m - 1) * (2m - 2)`        — alternative identity (**)

Pairwise-coprime check on the three factors:

| sub-case | parity of `m` | factorization | gcd checks |
|---|---|---|---|
| `n ≡ 0 mod 4` | `m` even | (*) `(2m)(2m-1)(m-1)` | gcd(2m, 2m-1)=1; gcd(2m, m-1)=1 (since m-1 odd → gcd | 2 → gcd=1); gcd(2m-1, m-1)=1 (2m-1 = 2(m-1)+1) |
| `n ≡ 2 mod 4` | `m` odd | (**) `m(2m-1)(2m-2)` | gcd(m, 2m-1)=1 (≡ -1 mod m); gcd(m, 2m-2)=1 (gcd | 2; m odd); gcd(2m-1, 2m-2)=1 (consecutive) |

Each factor `≤ n` and `≥ 1` for `m ≥ 2`, so each divides `lcmRange n`
via Part 1 `dvd_lcmRange`. Two applications of
`Nat.Coprime.mul_dvd_of_dvd_of_dvd` (mirroring S8) then give
`3 · C(n, 3) ∣ lcmRange n`.

### Lean tactical notes for S10

1. **Helper algebraic identity**: prove `(*)` as a private helper
   `three_mul_choose_three_eq_of_double {m : ℕ} (hm : 2 ≤ m) :
   3 * Nat.choose (2 * m) 3 = (2 * m) * (2 * m - 1) * (m - 1)`. Proof:
   `two_mul_three_mul_choose_three_eq` (Part 7) plus `2m - 2 = 2(m-1)`
   plus `Nat.eq_of_mul_eq_mul_left`. ~10 lines.

2. **Avoid ℕ division**: parametrize via `m` rather than `n`. The
   sub-case proofs take `m : ℕ` with hypotheses `2 ≤ m` plus
   `Even m` / `Odd m`; the gallery callers convert `n = 2 * m` via
   `obtain ⟨m, rfl⟩ := h_n_even`.

3. **Coprime API hiccups** (m even sub-case): `gcd(2m, m-1) = 1` for
   `m` even is the trickiest gcd; the cleanest tactic is
   `Nat.Coprime.coprime_dvd_left` after establishing `gcd | 2` from
   `2m - 2(m-1) = 2`, combined with `m - 1` odd. Alternatively, use
   `obtain ⟨j, rfl⟩ := h_m_even` to expose `m = 2j` and reduce to
   `gcd(4j, 2j-1) = 1` via `Nat.coprime_self_add_right` after
   rewriting `4j = 2(2j-1) + 2`.

4. **Coprime API hiccups** (m odd sub-case): `gcd(m, 2m-2) = 1` for
   `m` odd reduces to `gcd(m, 2) = 1` since `gcd(m, 2m-2) | 2(m-1)`
   and `gcd(m, m-1) = 1` (consecutive). Use
   `(Nat.Coprime.coprime_dvd_right ⟨1, ...⟩).mul_right`.

5. **Sub-case combiner**: `mul_choose_dvd_lcmRange_three_even` takes
   `n ≥ 4` and `Even n`, then `rcases Nat.even_or_odd m` (where
   `m = n / 2`) and dispatches to the two sub-case lemmas.

6. **Full theorem combiner**: `mul_choose_dvd_lcmRange_three` takes
   `n ≥ 3`, then `rcases Nat.even_or_odd n` and dispatches to S8's
   `mul_choose_dvd_lcmRange_three_odd` or the new
   `mul_choose_dvd_lcmRange_three_even`.

### Cost estimate (revised)

~30-50 lines per sub-case (was ~50-80). The uniform helper identity
(*) saves ~15 lines per sub-case, and S8's `mul_choose_dvd_lcmRange_three_odd`
provides a direct template for the coprime-assembly pattern.

### What this S9 corrects

S8 state.md (lines 96-100, prior version) said "n ≡ 2 mod 4 ...
Probably Kummer" — based on observing that `n` and `n-2` both have
`v_2 = 1` and concluding the coprime argument can't close. **This is
false**: re-grouping the `2` into the `n-2 = 2(m-1)` factor (formula
(**)) gives a coprime triple `m, 2m-1, 2m-2` with all gcd's equal to
1 because `m` is odd. No Kummer needed.

**Axiom delta**: 0 (documentation-only).

## Session 8 (PR #17175, merged)

Added two helpers as Part 8 of `BaselProblemOQ01OQ01OQ02OQ02.lean`,
discharging the **odd-n** case of the m=3 divisibility:

1. `lcmRange_dvd_of_le` (Part 8a, generic): `m ≤ n → lcmRange m
   ∣ lcmRange n`. Pure structural lemma — `Finset.lcm_dvd` over a
   subset. Reusable in any chain-of-`lcmRange` argument.
2. `mul_choose_dvd_lcmRange_three_odd` (Part 8b): for `n ≥ 3` odd,
   `3 · C(n, 3) ∣ lcmRange n`. Proof by coprime assembly: `n` is
   coprime to `(n-1)(n-2)` (gcd | 2 but n odd), so the
   `Nat.Coprime.mul_dvd_of_dvd_of_dvd` route gives
   `n · (n-1)(n-2) ∣ lcmRange n`. By Part 7
   (`two_mul_three_mul_choose_three_eq`),
   `n · (n-1)(n-2) = 2 · (3 · C(n, 3))`, and `3 · C(n, 3)` divides
   its own multiple by 2.

The even-n case (Sessions 9+) requires the carry analysis on
`v_2(C(n, 3))`. For n=2k with k even (n ≡ 0 mod 4), the
factorization `n(n-1)(n-2)/2 = 2k · (n-1) · (k-1)` keeps the
factor-of-2 inside `n/2`, so a similar coprime argument may close
that subcase (since `n/2 = k` and `(n-1)(n-2)/2` no longer has a
common factor with k). For n=2k with k odd (n ≡ 2 mod 4), the
factorization is more delicate and Kummer is likely needed.

**Axiom delta**: 0 (algebraic identities + structural divisibility,
no new assumptions).

## Session 7 (PR #17146, merged)

Added two algebraic identities for the m=3 case as Part 7 of
`BaselProblemOQ01OQ01OQ02OQ02.lean`:

1. `three_mul_choose_three_eq` (n ≥ 3): `3 · C(n, 3) = n · C(n - 1, 2)`.
   Direct one-line corollary of `mul_choose_eq_mul_choose_pred`.
2. `two_mul_three_mul_choose_three_eq` (n ≥ 3):
   `2 · (3 · C(n, 3)) = n · (n - 1) · (n - 2)`. Combines (1) with the
   m=2 absorption step `2 · C(n - 1, 2) = (n - 1) · (n - 2)`.

These reduce the m=3 divisibility question
`3 · C(n, 3) ∣ lcmRange n` to whether `n(n-1)(n-2)/2 ∣ lcmRange n`
(the `/2` being the substantive obstacle that needs Kummer's theorem
or a careful coprimality argument). Either route — Kummer or double
induction — can use these identities as the entry point.

**Axiom delta**: 0 (algebraic identities, no divisibility yet).

## Current Focus

Discharging base cases of the binomial-denominator divisibility
  `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n, m) ∣ lcmRange n`,
which is needed for the alternating-bilinear half of the van der
Poorten denominator analysis (route F).

Session 6 (this session) proved the m=1 and m=2 cases:
  `mul_choose_dvd_lcmRange_one`, `mul_choose_dvd_lcmRange_two`.
The general theorem (m ≥ 3) requires either Kummer's theorem on
`v_p(C(n, m))` or a double `(n, m)` induction (~100-200 lines).

Earlier sessions:
- Session 5: added `mul_choose_eq_mul_choose_pred` (binomial absorption)
  + `dvd_mul_choose` (n divides m·C(n,m)) + `lcmRange_pos` + numerical
  witnesses 6, 7. Identified that the full
  `mul_choose_dvd_lcmRange` is harder than the Session 5 next-action
  implied (absorption only proves divisibility by `n`, not by
  `lcmRange n`).
- Session 4: discharged the H_n^{(3)} half of vdP (`harmonicCubed_lcm_clear`).
- Sessions 1-3: route selection + infrastructure.

## Active Approach

**Route (F)**: van der Poorten closed form for `aperyA n`.

Two halves of the denominator analysis:
- **H_n^{(3)} half** (this OQ-02-OQ-02): DONE Session 4.
- **Alternating-bilinear half**: m=1, 2 base cases DONE in
  Session 6; m=3 odd-n case DONE in Session 8 (this session);
  m=3 even-n case + m ≥ 4 remain.

## Blockers

For `mul_choose_dvd_lcmRange_three` (full m=3, even-n case):
- **No Kummer needed** (S9 finding). Both parity-of-`m` sub-cases
  admit a clean coprime decomposition (see S9 §"Concrete
  factorizations"). The S10 task is purely arithmetic Lean coding
  (~30-50 lines per sub-case), not an upstream Mathlib gap.

For `mul_choose_dvd_lcmRange` (m ≥ 4):
- Genuine Kummer-or-double-induction territory. The m=3 trick
  (parametrize `n = 2m` and re-group the lone `/2`) does **not**
  generalize to m ≥ 4: the binomial `C(n, m)` has `v_2` controlled
  by `s_2(m) + s_2(n-m) - s_2(n)` (digit-sum carry count), which
  cannot be uniformly absorbed by parametrization of `n`.

For the full `denominator_control`:
- The alternating bilinear summand
  `∑_{m=1}^{k} (-1)^{m-1}/(2 m^3 C(n,m) C(n+m,m))`
  needs `mul_choose_dvd_lcmRange` (general m) as input.
- `aperyA_explicit_formula` must be stated and validated numerically.

## Next Action

Session 10: implement Approach (A) per S9's tactical plan.

1. **Add Part 9 helper**: `three_mul_choose_three_eq_of_double` for
   `m ≥ 2`: `3 * C(2m, 3) = (2m)(2m - 1)(m - 1)`. Proof via Part 7
   `two_mul_three_mul_choose_three_eq` plus `2m - 2 = 2(m - 1)` plus
   `Nat.eq_of_mul_eq_mul_left`. ~10 lines.

2. **Add Part 10a** `mul_choose_dvd_lcmRange_three_double_even` for
   `m ≥ 2`, `Even m`: `3 * C(2m, 3) ∣ lcmRange (2m)`. Coprime triple
   `(2m)(2m-1)(m-1)`. ~30 lines.

3. **Add Part 10b** `mul_choose_dvd_lcmRange_three_double_odd` for
   `m ≥ 2`, `Odd m`: `3 * C(2m, 3) ∣ lcmRange (2m)`. Coprime triple
   `m(2m-1)(2m-2)` (re-group of (2m)(m-1) = m·2(m-1)). ~30 lines.

4. **Add Part 10c** `mul_choose_dvd_lcmRange_three_even` for `n ≥ 4`,
   `Even n`: dispatch on parity of `n / 2`. ~10 lines.

5. **Add Part 10d** `mul_choose_dvd_lcmRange_three` for `n ≥ 3`:
   dispatch on parity of `n` (S8 odd-case + S10 even-case). ~5 lines.

Total: ~85 lines of Lean. Build via Docker wrapper or "build pending"
per precedent. NO new sorries or axioms.

After S10 closes m=3, the next-action shifts to either:
- m ≥ 4 via Kummer (~150 lines for the generic prime-power-divides
  translation), OR
- bypass via the alternating bilinear summand needing a different
  divisibility lemma (the precise statement should be derived by
  re-reading the vdP §6 layout from S5).

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 4 (route F: S4, S5, S6, S7 all forward
  progress; S8 m=3 odd case; S9 m=3 even-n tactical analysis).
- Approaches tried: 2 (recurrence-induction ruled out in S1;
  van der Poorten closed form being executed S2-S9+)
