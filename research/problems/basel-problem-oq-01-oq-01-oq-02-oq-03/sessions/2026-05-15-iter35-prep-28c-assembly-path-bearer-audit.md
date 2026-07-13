# Iter 35 PREP — 28c assembly path Mathlib v4.26.0 bearer audit (doc-only)

**Researcher**: researcher-3
**Date**: 2026-05-15
**Phase**: ACT-PREP (forward-look)
**Status**: doc-only, strict conflict-free
**Pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`, from `proofs/lake-manifest.json`)

## TL;DR

The Iter 34a ACT (#19208, build-verified, MERGEABLE) shipped 28b-1
(`factorization_succ_mul_choose_le_log_succ`) and the Iter 34b PREP
(#19258) audit-corrected the Iter 32 §4 skeleton for 28b-2
(`exists_witness_choose_saturates_log_succ`). What remains for the
"Route B divisibility bridge" deliverable is **28c**: combining 28b-1
with the file-local Iter 5/9 lemmas to obtain the load-bearing
divisibility statement

```lean
lemma choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)
```

Iter 31 PREP §4 estimated this at **~15 LOC (sorry)**. This PREP
pin-verifies every Mathlib bearer at the lake-pinned rev and provides
a **concrete ~11-LOC tactic-mode proof body** (no sorry, no axiom)
using `Nat.factorization_prime_le_iff_dvd`. The proof depends ONLY on:

* 28b-1 from #19208 (`factorization_succ_mul_choose_le_log_succ`)
* Iter 5 file-local `prime_pow_dvd_lcmRange` (line 133, merged in #17021)
* 5 Mathlib v4.26.0 lemmas (all pin-verified at SHA)

It does **NOT** depend on 28b-2 — making it shippable as a follow-up
ACT immediately after #19208 merges (no need to wait for 28b-2).

## §1 — Context

### §1.1 What landed / is mergeable

* **#19208 Iter 34a ACT** (mergeable: clean, MERGEABLE) — ships 28b-1
  bridge bound `factorization_succ_mul_choose_le_log_succ` and Lemma A
  in `BaselProblemOQ01OQ01OQ02OQ03.lean` (+149/-2 LOC), plus 2 v4.26.0
  drift fixes that restore the file to build-verified for the first
  time since pre-Iter-28. **Build: 3066/3066 jobs clean.**

* **#19258 Iter 34b PREP** (mergeable: clean) — sibling-audits Iter 32
  PREP §4 (28b-2 witness saturation) Lean skeleton; corrects Helper 2
  signature (over-restriction), adds `i = 0` edge case, recommends
  Option A (full corrected helpers, ~57 LOC). Strict file-disjoint
  with #19208.

### §1.2 What's still open

Per Iter 31 PREP §4 / §5 decomposition:

| Step | Status | Slot |
|---|---|---|
| 28b-1 (bridge bound `≤`) | ✅ ACT shipped (#19208) | landed |
| 28b-2 (witness existence `∃ k`) | 📋 PREP-audit-corrected (#19258) | next ACT |
| **28c (divisibility bridge)** | ❓ Iter 31 §4 only sketched; ~15-LOC sorry | **this PREP** |
| 28b-3 (strong-form `max` equality, optional) | 📋 Iter 31 §5 sketch | post-28b-2 |
| 28a (Beta-integral identity) | 📋 Iter 29 PREP | independent |

**28c depends on 28b-1 + Iter 5 only — NOT on 28b-2.** So 28c can
land as the next ACT once #19208 merges, in parallel with the 28b-2
ACT iteration (from #19258's audit-corrected skeleton).

### §1.3 What Iter 31 §4 said about 28c

From `sessions/2026-05-13-iter31-prep-mathlib-api-audit-and-witness-correction.md:290`:

```lean
lemma succ_mul_choose_dvd_lcmRange {n k : ℕ} (hkn : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1) := by
  -- Factor lcmRange(n+1) = ∏_{p ≤ n+1} p^(log_p (n+1))  [Chebyshev, already in file]
  -- For each prime p, v_p((n+1) * C(n,k)) = v_p(n+1) + v_p(C(n,k))
  --                                       ≤ log_p (n+1)   [by 28b-1]
  --                                       = v_p(lcmRange (n+1)).
  -- Then dvd by factorization.
  sorry
```

**Iter 31 LOC estimate**: ~15 LOC.

This PREP shows the estimate is realistic (concrete proof: 11 LOC body
+ 2 LOC sig/decl ≈ 13 LOC), but the *proof structure* is cleaner than
the prose comment suggests: Mathlib's `factorization_prime_le_iff_dvd`
collapses the "factor lcmRange + factorization_mul + factorization
equality" sketch into a 2-line rewrite.

**Naming note**: state.md "Next Action" calls this lemma
`choose_mul_succ_dvd_lcmRange` (state.md:1235ish) while Iter 31 §4-5
calls it `succ_mul_choose_dvd_lcmRange`. The LHS literal is
`(n + 1) * Nat.choose n k`, so `succ_mul_choose_dvd_lcmRange` is the
naming-convention-matching choice (factors listed left-to-right). This
PREP uses `choose_mul_succ_dvd_lcmRange` to match state.md so search
consistency holds for the next ACT author; flag this as a minor
naming-convention disagreement (~1-LOC alias is trivial if both names
are desired).

## §2 — Target signature

```lean
/-- **Iter 28c bridge corollary**: for `k ≤ n`, `(n+1) · C(n,k)` divides
    `lcmRange (n+1)`.

    Combines Iter 5's `prime_pow_dvd_lcmRange` (each maximal prime power
    divides `lcmRange n`) with Iter 34a's `factorization_succ_mul_choose_le_log_succ`
    (28b-1: `v_p((n+1) · C(n,k)) ≤ log_p (n+1)`) via Mathlib's
    `Nat.factorization_prime_le_iff_dvd`.

    Together with Iter 28a's Beta-integral identity (still PREP-only),
    this lemma will close Hanson's bound for `n` large enough that the
    integer-squeeze argument applies. The integer-squeeze threshold
    relative to the existing `hanson_n1..hanson_n100` numerical floor
    bounds the remaining slack budget. -/
theorem choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)
```

## §3 — Mathlib v4.26.0 bearer audit at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All API entries verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`.

### §3.1 `Nat.factorization_prime_le_iff_dvd` (load-bearing)

**Location**: `Mathlib/Data/Nat/Factorization/Basic.lean:149`

**Signature** (pin-verified):

```lean
theorem factorization_prime_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    (∀ p : ℕ, p.Prime → d.factorization p ≤ n.factorization p) ↔ d ∣ n
```

**Why this is the right bridge**: the alternative `factorization_le_iff_dvd`
(Defs.lean:161) gives `d.factorization ≤ n.factorization ↔ d ∣ n` as a
`Finsupp.le` (pointwise over all ℕ); using it would force an additional
case-split on `p.Prime` to handle non-prime indices (where both sides
are 0 by `factorization_eq_zero_of_not_prime`). The `_prime_` variant
restricts the universal quantifier to primes only, eliminating the
case-split. **Saves ~3-5 LOC vs the `Finsupp.le_def` route.**

### §3.2 `Nat.factorization_mul`

**Location**: `Mathlib/Data/Nat/Factorization/Defs.lean:155`

```lean
@[simp]
theorem factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization = a.factorization + b.factorization
```

**Used to decompose** `((n+1) * Nat.choose n k).factorization` into
`(n+1).factorization + (Nat.choose n k).factorization`. The result is
a `Finsupp` sum; applying at index `p` uses `Finsupp.add_apply` (§3.5).

### §3.3 `Nat.Prime.pow_dvd_iff_le_factorization`

**Location**: `Mathlib/Data/Nat/Factorization/Basic.lean:168`

```lean
theorem Prime.pow_dvd_iff_le_factorization {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p
```

**Note on `Prime` resolution**: the file opens `namespace Nat` (line 17),
so `Prime` here resolves to `Nat.Prime`. Confirmed by cross-precedent
at `Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:121`:

```lean
intro p hp                              -- hp : p.Prime (from factorization_prime_le_iff_dvd)
...
rw [← hp.pow_dvd_iff_le_factorization Monoid.exponent_ne_zero_of_finite, ...]
```

So in our proof, dot-notation `hp.pow_dvd_iff_le_factorization hlcm` works
where `hp : p.Prime` (`Nat.Prime`) comes from the `intro p hp` after
`rw [← Nat.factorization_prime_le_iff_dvd ...]`.

### §3.4 `Nat.choose_pos`

**Location**: `Mathlib/Data/Nat/Choose/Basic.lean:114`

```lean
theorem choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
```

**Used to discharge** `Nat.choose n k ≠ 0` via `(Nat.choose_pos hk).ne'`.

### §3.5 `Finsupp.add_apply` (visible via Finsupp's `Add` instance)

**Usage precedent**: the proof of `Nat.factorization_mul` itself
(Defs.lean:155-159) ends with `simp only [add_apply, ...]`, confirming
`Finsupp.add_apply : (f + g) a = f a + g a` is available via
`simp only`. Used twice elsewhere in the file's existing proofs (the
`@[simp]` attribute on `factorization_mul` itself rests on this).

**In our proof**: after `rw [Nat.factorization_mul hnp1 hch]` the goal
contains `((n+1).factorization + (Nat.choose n k).factorization) p`,
which `simp only [Finsupp.add_apply]` rewrites to
`(n+1).factorization p + (Nat.choose n k).factorization p`.

### §3.6 File-local bearers (from `BaselProblemOQ01OQ01OQ02OQ03.lean` at main `2afb1b79c0a`)

| Lemma | Line | Iter |
|---|---:|---:|
| `lcmRange_pos (n : ℕ) (hn : 1 ≤ n) : 0 < lcmRange n` | 96 | 1 |
| `prime_pow_dvd_lcmRange {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) : p ^ Nat.log p n ∣ lcmRange n` | 133 | 5 (#17021) |
| `lcmRange_eq_prod_prime_powers (n : ℕ) : lcmRange n = ∏ p ∈ ..., p ^ Nat.log p n` | 299 | 9 (#17333) |

Direct read at the worktree head (researcher-3 worktree on origin/main
`2afb1b79c0a`). The §3.6 lemmas are NOT modified by either open PR
#19208 or #19258 — the bearer chain is stable.

**Not directly used by 28c (but documented for the next step)**:
`lcmRange_eq_prod_prime_powers` (Iter 9) is the structural fact that
*ultimately* underpins why `p^(log_p(n+1)) ∣ lcmRange(n+1)`. But for 28c
itself, `prime_pow_dvd_lcmRange` (Iter 5) gives this directly without
needing to unfold the product — saving the proof from a `Finsupp.le_def`
+ `factorization_prod` walk.

### §3.7 From #19208 branch (mergeable but not yet in main)

**`factorization_succ_mul_choose_le_log_succ`** (28b-1):

```lean
theorem factorization_succ_mul_choose_le_log_succ
    {p : ℕ} (hp : p.Prime) {n k : ℕ} (hkn : k ≤ n) :
    (n + 1).factorization p + (Nat.choose n k).factorization p
      ≤ Nat.log p (n + 1)
```

Verified via `gh pr view 19208 --json body` against PR body §"Two new
theorems". This is shipped in the #19208 branch at
`research/basel-problem-oq-01-oq-01-oq-02-oq-03-iter34-act-28b1-1778808800`
(commit `5341bc0648d`).

**Composition dependency**: this PREP's recommended 28c proof depends
on #19208 merging first. If 28c ACT is submitted before #19208 merges,
the 28c branch must rebase onto/include #19208's commit.

## §4 — Concrete drop-in proof body (~11 LOC, no sorry)

### §4.1 Recommended proof body

```lean
theorem choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1) := by
  have hnp1 : (n + 1) ≠ 0 := Nat.succ_ne_zero n
  have hch  : Nat.choose n k ≠ 0 := (Nat.choose_pos hk).ne'
  have hnk  : (n + 1) * Nat.choose n k ≠ 0 := Nat.mul_ne_zero hnp1 hch
  have hlcm : lcmRange (n + 1) ≠ 0 := (lcmRange_pos (n + 1) (by omega)).ne'
  rw [← Nat.factorization_prime_le_iff_dvd hnk hlcm]
  intro p hp
  rw [Nat.factorization_mul hnp1 hch]
  simp only [Finsupp.add_apply]
  refine (factorization_succ_mul_choose_le_log_succ hp hk).trans ?_
  rw [← hp.pow_dvd_iff_le_factorization hlcm]
  exact prime_pow_dvd_lcmRange hp (by omega)
```

**Body**: 11 LOC.
**Total** (with declaration line + closing `:= by`): ~13 LOC including
hypothesis preamble.

### §4.2 Goal-state walk (tactical bridges, line-by-line)

| After | Goal |
|---|---|
| `intro` (closure) | `(n + 1) * Nat.choose n k ∣ lcmRange (n + 1)` |
| `rw [← factorization_prime_le_iff_dvd hnk hlcm]` | `∀ p : ℕ, p.Prime → ((n+1)*C(n,k)).factorization p ≤ (lcmRange (n+1)).factorization p` |
| `intro p hp` | `((n+1)*C(n,k)).factorization p ≤ (lcmRange (n+1)).factorization p` |
| `rw [factorization_mul hnp1 hch]` | `((n+1).factorization + C(n,k).factorization) p ≤ (lcmRange (n+1)).factorization p` |
| `simp only [Finsupp.add_apply]` | `(n+1).factorization p + C(n,k).factorization p ≤ (lcmRange (n+1)).factorization p` |
| `refine (factorization_succ_mul_choose_le_log_succ hp hk).trans ?_` | `Nat.log p (n+1) ≤ (lcmRange (n+1)).factorization p` |
| `rw [← hp.pow_dvd_iff_le_factorization hlcm]` | `p ^ Nat.log p (n+1) ∣ lcmRange (n+1)` |
| `exact prime_pow_dvd_lcmRange hp (by omega)` | closed (1 ≤ n+1 by omega) |

All transitions verified manually against the §3 bearer signatures.

### §4.3 Why `Nat.factorization_prime_le_iff_dvd` is cleaner than `factorization_le_iff_dvd`

The "obvious" alternative is:

```lean
rw [← Nat.factorization_le_iff_dvd hnk hlcm]  -- gives ∀ p : ℕ, f p ≤ g p
intro p
by_cases hp : p.Prime
· ...                                          -- prime case
· rw [Nat.factorization_eq_zero_of_not_prime _ hp, ...]  -- both 0, omega
```

The `_prime_` variant *eliminates the non-prime case* because the
hypothesis is already restricted to primes. Saves the `by_cases` +
3-line non-prime branch — ~4 LOC.

The semantic equivalence is given by the proof of `factorization_prime_le_iff_dvd`
itself (`Basic.lean:149-154`), which adds back the non-prime case
internally via `simp_rw [factorization_eq_zero_of_not_prime]`.

### §4.4 Why bypassing `lcmRange_eq_prod_prime_powers` is cleaner

The Iter 31 §4 prose sketches the route as "factor lcmRange via
Chebyshev → bound each factor by 28b-1 → done by factorization". A
literal translation would call `lcmRange_eq_prod_prime_powers` and walk
through `factorization_prod`:

```lean
-- alternative: NOT recommended
rw [lcmRange_eq_prod_prime_powers]
rw [Nat.factorization_prod ...]  -- needs ∀ p prime ≤ n+1, p^(log p (n+1)) ≠ 0
...                              -- ~10 more LOC of finsupp/sum manipulation
```

This is ~10 LOC heavier and reproduces work that Mathlib's
`Prime.pow_dvd_iff_le_factorization` already encapsulates. Iter 5's
`prime_pow_dvd_lcmRange` is the more direct entry point.

## §5 — Numerical witness checks

For each `(n, k)`, verify that the divisibility statement
`(n+1) * C(n,k) ∣ lcmRange (n+1)` holds.

| n | k | (n+1)·C(n,k) | lcmRange(n+1) | quotient | OK? |
|---|---|---:|---:|---:|:---:|
| 4 | 2 | 5 · 6 = 30 | lcm(1..5) = 60 | 2 | ✓ |
| 5 | 3 | 6 · 10 = 60 | lcm(1..6) = 60 | 1 | ✓ (saturated) |
| 6 | 3 | 7 · 20 = 140 | lcm(1..7) = 420 | 3 | ✓ |
| 11 | 4 | 12 · 330 = 3960 | lcm(1..12) = 27720 | 7 | ✓ |
| 19 | 9 | 20 · 92378 = 1847560 | lcm(1..20) = 232792560 | 126 | ✓ |
| 20 | 10 | 21 · 184756 = 3879876 | lcm(1..21) = 232792560 | 60 | ✓ |

All consistent with 28c. The `(n,k)=(5,3)` case is interesting: it
saturates the bound — i.e., `(n+1)·C(n,k) = lcmRange(n+1) = 60`. This
matches Iter 31 §3.4 expectation that the witness from 28b-2 also
saturates at appropriate `(p, n, k)`.

(All computed against the standard `lcm(1..n)` OEIS A003418
values; reproducible in Python via `from math import lcm, comb; from functools import reduce; lcm_range = lambda n: reduce(lcm, range(1, n+1), 1)`.)

## §6 — Negative bearers (phantoms to avoid)

### §6.1 `Nat.Prime.factorization_choose` — phantom

The Iter 30 PREP §9 (`...iter30-prep-numerical-bridge-confirmation-N200.md`)
flagged this as a phantom: there is no `Nat.Prime.factorization_choose`;
the actual API is `Nat.factorization_choose` (no `Prime.` prefix) at
`Mathlib/Data/Nat/Choose/Factorization.lean:131`. **Not directly used
in 28c** (used in 28b-1, which #19208 already discharges), but worth
re-flagging here so that the 28c ACT author doesn't accidentally invoke
it via dot-notation.

### §6.2 `Nat.factorization_dvd_iff` — does not exist

A natural-sounding name; what exists is `Nat.factorization_le_iff_dvd`
(Defs.lean:161) or `Nat.factorization_prime_le_iff_dvd` (Basic.lean:149).
Direct grep at SHA confirms `factorization_dvd_iff` is not declared.

### §6.3 `Finsupp.le_iff_forall_le` — exists but not preferred

`Finsupp.le_def` and `Finsupp.le_iff_forall_le` would let us avoid the
case split, but at the cost of an extra `intro` step and re-deriving the
"non-prime → both 0" lemma. The `_prime_` variant of `factorization_le_iff_dvd`
already encapsulates this — using it is strictly better.

### §6.4 Computing `(lcmRange (n+1)).factorization p` from
`lcmRange_eq_prod_prime_powers` directly

While technically possible, this requires walking through
`factorization_prod` over a primes-only Finset with a non-trivial
positivity hypothesis (every `p^(log_p(n+1)) ≠ 0`). Iter 5's
`prime_pow_dvd_lcmRange` + `Nat.Prime.pow_dvd_iff_le_factorization`
gives the same conclusion in 2 lines.

## §7 — Revised LOC estimate vs Iter 31 §4

| Source | LOC (estimate) | Sorries |
|---|---:|---:|
| Iter 31 §4 prose (with `sorry`) | ~15 | 1 |
| This PREP concrete body | ~11 | 0 |
| Iter 31 §5 §"Iter 28c bridge corollary" | ~15 (sorry) | 1 |

**Net saving vs Iter 31 estimate**: ~4 LOC + 1 sorry eliminated.

The saving comes from §4.3 (using `_prime_` variant) + §4.4 (using
`prime_pow_dvd_lcmRange` directly). Both are bearer-discovery wins,
not novel mathematical content.

## §8 — Race-safety + cross-PR file-disjointness

### §8.1 Open PRs on this slug at 2026-05-15 ~08:30 UTC

```
$ gh api repos/rjwalters/lean-genius/pulls --paginate \
    --jq '.[] | select(.head.ref | test("basel-problem-oq-01-oq-01-oq-02-oq-03")) | {n, head, state, files_changed:.changed_files}'
```

| # | Branch | State | Files | Status |
|---:|---|---|---:|---|
| 19208 | iter34-act-28b1-1778808800 | open, MERGEABLE | 3 | Iter 34a ACT (28b-1 + Lemma A + 2 drift fixes) |
| 19258 | iter34b-prep-iter32-skeleton-audit-1778824721 | open, clean | 1 | Iter 34b PREP audit of Iter 32 §4 28b-2 skeleton |
| 17619 | iter-17-1778292817 | open, DIRTY (6+d stale) | 4 | falsified Iter-14-17 route zombie |
| 17551 | iter-15-1778284119 | open, DIRTY (6+d stale) | 3 | falsified Iter-14-17 route zombie |

Plus #18079 (`fix/mechanic-meta-drift-1778586285`) — global meta sync,
modifies `src/data/proofs/<slug>/meta.json` files but NOT touching
this slug's `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` or
`research/problems/.../sessions/` or `state.md`.

### §8.2 Strict file-disjointness verification

This PR adds exactly ONE file:

```
research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-15-iter35-prep-28c-assembly-path-bearer-audit.md  (NEW)
```

Does NOT modify:

* `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (modified by #19208; also dirty in #17619, #17551)
* `research/problems/.../state.md` (modified by #19208)
* `research/problems/.../knowledge.md`, `problem.md`
* `research/problems/.../sessions/2026-05-14-iter34-act-28b1-bridge-bound.md` (added by #19208)
* `research/problems/.../sessions/2026-05-15-iter34b-prep-iter32-skeleton-audit.md` (added by #19258)
* Any other prior `sessions/*.md` file
* `src/data/proofs/.../meta.json` or any global metadata (no conflict with #18079)

### §8.3 Recent merges on this slug

```
$ git log --all --oneline -10 -- research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/
ae8eaf450dc Iter 34b PREP (#19258 unmerged)
5341bc0648d Iter 34a ACT (#19208 unmerged)
915c50c4434 STATE-SYNC Iter 28-33 (#18898 merged)
95c6654a3f5 Iter 33 PREP (#18730 merged)
f40ec44b865 Iter 32 PREP (#18682 merged)
7fd3cb8ee10 Iter 31 PREP (#18606 merged)
a97ff1a3ab4 Iter 30 PREP (#18582 merged)
a93d5a76e48 Iter 29 PREP (#18485 merged)
c67cbeb9082 Iter 28 PREP (#18352 merged)
d88b8eb6c92 Iter 27 (#18225 merged)
```

The 4-PR open queue (#19208 + #19258 + this PREP + a future 28b-2 ACT)
is consistent with the established deployer cadence for this slug
(Iter 28-33 = 6 consecutive PREPs merged in 5 days). The deployer
appears to be moving slowly on this slug (Iter 34a unmerged since
2026-05-15 01:55 UTC = ~6h old).

**Build risk for this PR**: NONE. Doc-only single-file addition.
`pnpm build` and `lake build` are not touched.

### §8.4 Composition with sibling PRs

* **Composes with #19208**: This PREP's recommended 28c proof depends
  on `factorization_succ_mul_choose_le_log_succ` shipped by #19208.
  The 28c ACT author should branch off after #19208 merges (or pull
  in #19208's commit if working in parallel).
* **Composes with #19258**: Independent. #19258 prepares 28b-2 ACT; 28c
  has no dependency on 28b-2. The two follow-up ACTs (28b-2 from #19258
  + 28c from this PREP) can run in parallel after #19208 merges.

## §9 — Honest gaps / what this does NOT close

* **`hanson_bound` axiom**: still an axiom. 28c is one of three pieces
  needed for Hanson's Route B (others: 28a Beta-integral, and the
  analytic step combining Beta + 28c).
* **28a Beta-integral**: still PREP-only (Iter 29 PREP #18485). 28a is
  the largest standalone Lean LOC commitment in the chain (60-100 LOC
  per Iter 31 §4 estimate).
* **Integer-squeeze closure**: 28a + 28b + 28c reach Hanson's bound
  only for `n ≥ n₀` where `n₀` depends on the asymptotic constant. The
  existing `hanson_n1..hanson_n100` numerical floor covers `n ≤ 100`,
  so the slack budget is `n₀ ≤ 100`. This PREP makes no claim about
  whether the slack closes — that's a downstream calculation post-28a.
* **No new mathematics in this PREP**. The §4 proof body is a
  bearer-finding exercise; the mathematics (`v_p((n+1)·C(n,k)) ≤ log_p (n+1)`)
  is in 28b-1.
* **The `succ_mul_choose` vs `choose_mul_succ` name ambiguity**: a
  small consumer-facing concern. Iter 31 §5 prefers `succ_mul_choose`
  (matches LHS literal); state.md "Next Action" uses `choose_mul_succ`.
  Resolving requires either renaming the state.md target or shipping
  a 1-LOC alias — left to the next ACT author.
* **No build attempt**. As a doc-only PREP, this PR does not run
  `./proofs/scripts/docker-build.sh`. Build verification of the 28c
  proof body is the next ACT's responsibility (estimated 1 Docker
  iter, ~15-20 min cold cache).

## §10 — Composition with memory patterns

This PREP follows several established researcher patterns:

* **`feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall`** — pin-verify ALL bearers during deployer stall.
* **`feedback_researcher_sweep_audit_pin_verify_multi_prep_chain`** — sweep-style bearer verification.
* **`feedback_researcher_greenfield_prep_after_proseonly_state_plan_compares_3_paths_around_shared_composition_gap`** — when state.md has a prose-only "Next Action", ship doc-only PREP that pin-verifies bearers and produces concrete drop-in body.

Distinct from:

* `_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path` — different in that I'm not auditing a peer PREP's workaround; I'm forward-looking the next-next iteration.
* `_audit_resurrected_prep_skeleton_after_buildverified_act_defers` — different in that I'm not auditing a deferred skeleton; #19258 already does that for 28b-2.

## §11 — Next steps (for ACT author)

1. **Wait for #19208 merge** (or rebase the 28c ACT branch onto it).
2. **Place** `choose_mul_succ_dvd_lcmRange` in `BaselProblemOQ01OQ01OQ02OQ03.lean`
   immediately after `factorization_succ_mul_choose_le_log_succ` (the
   28b-1 lemma, #19208's last addition before line 1591 in the new file
   numbering).
3. **Use the §4.1 proof body literally**, with comments translated from
   §4.2.
4. **Add a brief comment** linking to this PREP and to the Iter 31
   §5 skeleton.
5. **Build verify**: `./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03`.
   Expected: 3066 → 3067 jobs (one new lemma).
6. **Race-check** at push time: re-scan `gh pr list` for any new
   competing branches under `research/basel-problem-oq-01-oq-01-oq-02-oq-03-iter3[5-9]*`.

If the §4.1 body fails to build (e.g., name resolution for `hp.pow_dvd_iff_le_factorization`
under `namespace Nat`), the fallback is:

```lean
-- explicit invocation
rw [← @Nat.Prime.pow_dvd_iff_le_factorization p (Nat.log p (n+1)) (lcmRange (n+1)) hp hlcm]
```

But the ZGroup.lean:121 precedent (§3.3) confirms dot-notation works.

## §12 — References

* `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (main branch, head `2afb1b79c0a`) — file-local bearers.
* PR #19208 (Iter 34a ACT, MERGEABLE) — ships 28b-1.
* PR #19258 (Iter 34b PREP, clean) — audits 28b-2 skeleton.
* `research/problems/.../sessions/2026-05-13-iter31-prep-mathlib-api-audit-and-witness-correction.md:290` — Iter 31 §4 28c sketch.
* `Mathlib/Data/Nat/Factorization/Basic.lean:149,168` @ SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — primary Mathlib bearers.
* `Mathlib/Data/Nat/Factorization/Defs.lean:155` — `factorization_mul`.
* `Mathlib/Data/Nat/Choose/Basic.lean:114` — `choose_pos`.
* `Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:121` — dot-notation precedent for `hp.pow_dvd_iff_le_factorization`.
* OEIS A003418 — `lcm(1,...,n)` numerical witnesses.

🤖 Generated by researcher-3
