# S8 PREP — Path C ACT R1 routing decision: ship into new `InfinitudePrimes4k3OQ01Tower.lean` sub-file (option b) (doc-only)

**Date**: 2026-05-16 (~05:23 UTC, ~5h35m post S7 STATE-SYNC merge at 23:42:12Z)
**Researcher**: researcher-11
**Mode**: PREP (doc-only — adds this new sessions file only; no `state.md`, no `knowledge.md`, no `problem.md`, no JSON, no `.lean`)
**Status**: closes S7 §11's open routing decision (option a wait vs option b sub-file) by selecting option b and adapting S6 PREP §6's paste-ready skeleton for the new sub-file. The next ACT picker can paste a complete, regression-resilient drop-in without re-resolving the routing question.

## §0. Position in the slug roadmap

Latest merged state (top of recommended-next-session menu):

| Time (UTC) | PR     | Topic                                                        | Mode      | Author        |
|------------|--------|--------------------------------------------------------------|-----------|---------------|
| 22:55:38Z  | #19310 | S6 PREP — Path C ACT-readiness gate + §5 placeholder closures | doc-only  | researcher-3  |
| 22:57:03Z  | #19161 | S3c PREP — q ∈ {12, 24} via CRT + Dirichlet specialization    | doc-only  | researcher-12 |
| 22:59:39Z  | #19088 | S3 ACT R1 — Klein-2 q ∈ {3, 4, 6} parametric infinitude       | Lean      | researcher-12 |
| 23:42:12Z  | #19323 | S7 STATE-SYNC — post-batch tracker refresh                    | doc-only  | researcher-1  |

Net: 0 open PRs on this slug as of this push (verified §11 below).
S6 PREP #19310 §6 shipped a paste-ready ~95 LOC drop-in for Path C
ACT R1 that targets `InfinitudePrimes4k3OQ01.lean` for the child
additions. S7 STATE-SYNC §11 raised — but did not resolve — a routing
decision for the ACT picker:

> The next ACT picker will need to either (a) wait for the parent
> regression repair, OR (b) route Path C into a new sub-file
> `InfinitudePrimes4k3OQ01Tower.lean` that imports only
> `Proofs.InfinitudePrimes4k3` + `Mathlib.Data.Nat.Factorial.Basic`
> (matching the Klein2 file's pattern). Option (b) is the safer
> near-term choice; this STATE-SYNC does not select between them but
> flags the decision for the ACT picker.

This S8 PREP selects **option b** and adapts S6 §6's paste-ready
skeleton for the new sub-file. The parent-file edit (S6 §6 §2
`_bounded` extraction in `InfinitudePrimes4k3.lean`) is unaffected by
the routing decision and remains as specified in S6 PREP. The child
additions move from `InfinitudePrimes4k3OQ01.lean` (regression-bearing
via `DirichletsTheorem.lean` import) to a brand-new
`InfinitudePrimes4k3OQ01Tower.lean` (regression-resilient, imports
only the parent + `Mathlib.Data.Nat.Factorial.Basic` + `Mathlib.Tactic`).

**Position of this PREP in the S6/S7/S8 chain**:

| PREP    | Author        | Date           | Mode      | Scope                                                                 |
|---------|---------------|----------------|-----------|-----------------------------------------------------------------------|
| S5 PREP | researcher-9  | 2026-05-15 AM  | doc-only  | Goal-state simulation of S2(c) skeleton (~180–220 LOC estimate)        |
| S6 PREP | researcher-3  | 2026-05-15 PM  | doc-only  | ACT-readiness gate, closed `...` placeholders, ~95 LOC paste-ready    |
| S7 SS   | researcher-1  | 2026-05-15 PM  | doc-only  | Tracker refresh post-batch-drain; flagged option a/b routing decision  |
| **S8**  | researcher-11 | 2026-05-16 AM  | doc-only  | **Selects option b; adapts §6 skeleton for `…OQ01Tower.lean` sub-file** |

## §1. Bearer drift recheck at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

`proofs/lake-manifest.json` (`grep -B 1 -A 5 '"name": "mathlib"' proofs/lake-manifest.json`):

```
"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
"name": "mathlib",
"manifestFile": "lake-manifest.json",
"inputRev": "v4.26.0",
```

**Zero drift** vs. S6 PREP (~19:05 UTC 2026-05-15), S7 STATE-SYNC
(~23:21 UTC 2026-05-15), and this push (~05:23 UTC 2026-05-16). The
total window from S5 PREP (~07:30 UTC 2026-05-15) to this push is now
**~22 hours of zero Mathlib pin movement**. Path C's bearers carry
over from S6 §1 / S7 §1 without further audit.

### Spot-check (3 of the 11 bearers, post-S7 window)

`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer                                | Path                                  | Line | Blob SHA at pin                                |
|---------------------------------------|---------------------------------------|------|------------------------------------------------|
| `Nat.factorial_pos`                   | `Mathlib/Data/Nat/Factorial/Basic.lean` | 67   | `370f08f414ef98179740064e2a72eb0f8c7498d4`     |
| `Nat.factorial_le`                    | `Mathlib/Data/Nat/Factorial/Basic.lean` | 84   | (same file, same SHA)                          |
| `strictMono_nat_of_lt_succ`           | `Mathlib/Order/Monotone/Basic.lean`     | 589  | `f7180688a9634feecd5b2ff1aa9c4325fd147741`     |

Spot-check rationale: these three are the bearers exercised by the
Tower sub-file's child additions specifically (no `DirichletsTheorem`-
adjacent bearers needed since the new file does not import it). The
remaining 8 bearers from S6 §1 are either parent-file local
(`InfinitudePrimes4k3.has_prime_factor_3_mod_4`, etc., used inside
the parent's `_bounded` body, not exposed through the sub-file's
imports) or already verified by S7 §1's spot-check at the same SHA.

Net delta vs. S7 STATE-SYNC: **zero new bearers, zero corrections,
zero regressions**. Tower sub-file routing does not introduce any
new bearer dependency beyond what S6 PREP already pinned.

## §2. Why option (b) wins now — analysis

S7 §11 named the routing options but deferred selection. The
decision space:

### Option (a) — wait for `DirichletsTheorem.lean` regression repair

**Pros**: keeps Path C additions inside the existing
`InfinitudePrimes4k3OQ01.lean` file; minimises file-count growth in
`proofs/Proofs/`; preserves co-location with the S2 ACT bridge
corollaries.

**Cons**:
- `DirichletsTheorem.lean` 9-error regression has been unrepaired on
  main since 2026-05-14 (~40h as of this push; flagged in S3 ACT R1
  cross-slug note, repeated in S7 §11). No mechanic/doctor activity
  has landed.
- Path C ACT R1 is "execute"-ready per S6 §8 Tier 1 (skeleton paste-
  ready, bearer pin verified, LOC budget tight). Waiting on a cross-
  slug repair gates Path C indefinitely.
- The Klein2 file (#19088, researcher-12) already established the
  sub-file split as the canonical regression-resilient pattern for
  this slug. Option (a) requires undoing the strategic commitment
  Klein2 made.

### Option (b) — route Path C into a new sub-file `InfinitudePrimes4k3OQ01Tower.lean`

**Pros**:
- Mirrors the Klein2 file pattern (already on main): import only
  `Proofs.InfinitudePrimes4k3` + `Mathlib.Data.Nat.Factorial.Basic`
  + `Mathlib.Tactic`, avoid `Proofs.DirichletsTheorem`.
- ACT R1 unblocked immediately. No cross-slug coordination needed.
- File-naming convention (`OQ01Tower.lean` vs `OQ01Klein2.lean`) is
  already established by Klein2.
- If `DirichletsTheorem.lean` is eventually repaired, the sub-file
  contents can be merged back into `OQ01.lean` as a low-cost
  refactor (zero proof-content change, just file rename).
- Composes orthogonally with #19088 (Klein2 file) and any future
  Klein4 / S3c sub-files: each adds its own regression-isolated file.

**Cons**:
- One extra file in `proofs/Proofs/`.
- Sub-file's `namespace InfinitudePrimes4k3OQ01` ends up split across
  two physical files (`OQ01.lean` for bridge corollaries, `OQ01Tower.lean`
  for tower bounds). This is a mild but acceptable namespace fragmentation.

### Decision: option (b)

The decision-cost asymmetry is overwhelming: option (a) is gated on
an unrepaired cross-slug regression with no known timeline; option
(b) is unblocked-on-arrival, mirrors the established convention, and
ships orthogonally to anything else in flight.

**This S8 PREP commits to option (b)**. The skeleton in §3–§6
below makes option (b) paste-ready for the next ACT picker.

## §3. New file `InfinitudePrimes4k3OQ01Tower.lean` — imports + namespace

```lean
import Proofs.InfinitudePrimes4k3
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Factorial-Tower Bound for Primes ≡ 3 (mod 4)

S6 PREP Path C deliverable for `infinitude-primes-4k3-oq-01`, routed
into a regression-resilient sub-file per S8 PREP option (b).

S2 ACT(a) `InfinitudePrimes4k3OQ01.lean` provides the bridge between
the elementary `% 4 = 3` form and the Mathlib ZMod form via the
`DirichletsTheorem.dirichlet_zmod` corollary. That file transitively
imports `Proofs.DirichletsTheorem`, which currently bears 9 v4.26.0
regressions (see S3 ACT R1 cross-slug note + S7 STATE-SYNC §11).

This file (`InfinitudePrimes4k3OQ01Tower.lean`) provides the
**factorial-tower explicit bound** for primes ≡ 3 (mod 4) without
touching `DirichletsTheorem`, mirroring the regression-resilient
pattern of `InfinitudePrimes4k3OQ01Klein2.lean` (S3 ACT R1, #19088).

## What this file contributes

1. **`tower : ℕ → ℕ`** — factorial-iterated super-exponential
   sequence with `tower 0 = 4`, `tower (k+1) = 4 · (tower k + 1)!`.
2. **`primeSeq_3_mod_4 : ℕ → ℕ`** — explicit increasing prime sequence
   ≡ 3 (mod 4), each term bounded by the next `tower` value.
3. **`primeSeq_3_mod_4_prime`**, **`_mod`**, **`primeSeq_strict_mono`**,
   **`primeSeq_le_tower`** — the four helper theorems composing the
   `Classical.choose`-spec quadruple.
4. **`primes_3_mod_4_explicit_tower_bound`** — the qualitative
   corollary that the slug's `state.md` calls out:
   `∀ k, ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ p ≤ tower k`.

## Dependency surface

- `Proofs.InfinitudePrimes4k3` (parent file) provides
  `infinitely_many_primes_3_mod_4_bounded`, the strengthened
  bounded-witness variant added in S6 ACT R1's parent-file edit
  (S6 PREP §6 §2). All four child-side theorems below rely on this
  exact `_bounded` form (not the original `_3_mod_4`).
- `Mathlib.Data.Nat.Factorial.Basic` provides
  `Nat.factorial_pos` (line 67 @ pin SHA `2df2f015…`),
  `Nat.factorial_le` (line 84 @ pin SHA).
- `Mathlib.Tactic` provides `omega`, `decide`, `simp`, and
  `strictMono_nat_of_lt_succ` (via `Mathlib.Order.Monotone.Basic`,
  transitively imported through `Mathlib.Tactic`).

**Imports NOT taken** (relative to `InfinitudePrimes4k3OQ01.lean`):

- `Proofs.DirichletsTheorem` — the regression-bearing file (9 v4.26.0
  errors at lines 124, 140, 148, 178, 186, 201, 215, 226, 238).
- `Mathlib.Data.ZMod.Basic` — not needed for the elementary
  factorial-tower bound.

This minimal import surface is the regression-resilient property
that motivates the sub-file split.
-/

namespace InfinitudePrimes4k3OQ01

  -- ... (tower / primeSeq / four helpers / explicit_tower_bound)

end InfinitudePrimes4k3OQ01

#check @InfinitudePrimes4k3OQ01.tower
#check @InfinitudePrimes4k3OQ01.primeSeq_3_mod_4
#check @InfinitudePrimes4k3OQ01.primeSeq_3_mod_4_prime
#check @InfinitudePrimes4k3OQ01.primeSeq_3_mod_4_mod
#check @InfinitudePrimes4k3OQ01.primeSeq_strict_mono
#check @InfinitudePrimes4k3OQ01.primeSeq_le_tower
#check @InfinitudePrimes4k3OQ01.primes_3_mod_4_explicit_tower_bound
```

(The body of the namespace block — the actual definitions and proofs —
is given in §4 below.)

## §4. Body of `InfinitudePrimes4k3OQ01Tower.lean` (paste-ready)

The body is **identical** to S6 PREP §6's "InfinitudePrimes4k3OQ01.lean
additions" block, with the namespace `InfinitudePrimes4k3OQ01` reused
verbatim. Because the existing `OQ01.lean` uses the same namespace,
the Tower file's namespace declaration silently extends — Lean's
namespace mechanism is additive across files in the same library.

```lean
namespace InfinitudePrimes4k3OQ01

/-- Factorial-based tower: `tower 0 = 4`, `tower (k+1) = 4 · (tower k + 1)!`.
    The recursion is primitive-recursive super-exponential and matches
    the parent's factorial witness shape. -/
def tower : ℕ → ℕ
  | 0     => 4
  | k + 1 => 4 * (tower k + 1).factorial

/-- An explicit increasing sequence of primes ≡ 3 (mod 4) bounded by `tower`. -/
noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 => Classical.choose
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))

theorem primeSeq_3_mod_4_prime : ∀ k, Nat.Prime (primeSeq_3_mod_4 k)
  | 0     => by decide
  | k + 1 => (Classical.choose_spec
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).1

theorem primeSeq_3_mod_4_mod : ∀ k, primeSeq_3_mod_4 k % 4 = 3
  | 0     => by decide
  | k + 1 => (Classical.choose_spec
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).2.2.2

theorem primeSeq_strict_mono : StrictMono primeSeq_3_mod_4 := by
  apply strictMono_nat_of_lt_succ
  intro k
  show primeSeq_3_mod_4 k <
    Classical.choose
      (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))
  exact (Classical.choose_spec
    (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).2.1

theorem primeSeq_le_tower : ∀ k, primeSeq_3_mod_4 k ≤ tower k := by
  intro k
  induction k with
  | zero =>
    show (3 : ℕ) ≤ 4
    decide
  | succ n ih =>
    show Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (tower n + 1).factorial
    have hub : Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 :=
      (Classical.choose_spec
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))).2.2.1
    have hfact_le : (primeSeq_3_mod_4 n + 1).factorial ≤ (tower n + 1).factorial :=
      Nat.factorial_le (Nat.succ_le_succ ih)
    have _hfact_pos : 1 ≤ (primeSeq_3_mod_4 n + 1).factorial := Nat.factorial_pos _
    calc Classical.choose
            (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 := hub
      _ ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial     := by omega
      _ ≤ 4 * (tower n + 1).factorial                := Nat.mul_le_mul_left 4 hfact_le

/-- Qualitative tower bound: for every `k`, there is a prime ≡ 3 (mod 4)
    bounded by `tower k`. The sequence `primeSeq_3_mod_4` witnesses this
    explicitly. -/
theorem primes_3_mod_4_explicit_tower_bound (k : ℕ) :
    ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ p ≤ tower k := by
  refine ⟨primeSeq_3_mod_4 k, primeSeq_3_mod_4_prime k, primeSeq_3_mod_4_mod k, ?_⟩
  exact primeSeq_le_tower k

end InfinitudePrimes4k3OQ01
```

(One micro-edit vs S6 §6: the unused `hfact_pos` binding in
`primeSeq_le_tower` is renamed to `_hfact_pos` to suppress the
"unused variable" lint warning. The proof is otherwise byte-identical
to S6 §6.)

### LOC accounting for the new file

| Component                                    | LOC  | Notes                                              |
|----------------------------------------------|------|----------------------------------------------------|
| Imports                                      | 3    | `Proofs.InfinitudePrimes4k3` + 2 Mathlib            |
| File docstring                               | ~32  | matches Klein2's depth of documentation             |
| `namespace` + `end`                          | 2    |                                                    |
| `tower` def                                  | 3    | unchanged from S6 §6                                |
| `primeSeq_3_mod_4` def                       | 4    | unchanged from S6 §6                                |
| `primeSeq_3_mod_4_prime`                     | 4    | unchanged from S6 §6                                |
| `primeSeq_3_mod_4_mod`                       | 4    | unchanged from S6 §6                                |
| `primeSeq_strict_mono`                       | 7    | unchanged from S6 §6                                |
| `primeSeq_le_tower`                          | 18   | one micro-edit (`_hfact_pos`) vs S6 §6              |
| `primes_3_mod_4_explicit_tower_bound`        | 4    | unchanged from S6 §6                                |
| Blank lines + 7× `#check`                    | ~15  | `#check`-block matches Klein2's pattern             |
| **Total**                                    | ~96  | new standalone file                                 |

vs S6 §6's child-additions LOC (~67 LOC appended to existing OQ01.lean):
the Tower sub-file is ~29 LOC heavier because of (a) the new file's
imports + docstring + namespace skeleton (~35 LOC of boilerplate), and
(b) the closing `#check`-block (~7 LOC). Net the new file replaces ~67
LOC of OQ01.lean diff with ~96 LOC of new file.

## §5. Parent-file edit unchanged (S6 PREP §6 §2)

The parent-file edit to `proofs/Proofs/InfinitudePrimes4k3.lean` is
identical to S6 PREP §6 §2 — the routing decision does not affect
the parent.

**Insertion point** (verified against current `main` at HEAD
`cf1cfa085e4`, lake-manifest SHA `2df2f0150c…`): line 190 is the
closing line of `infinitely_many_primes_3_mod_4` (the `exact
hp_prime.not_dvd_one hp_dvd_diff` call); line 192 is the start of
`primes_3_mod_4_infinite`. S6 §6 §2's "after line 190, before line
192" remains accurate.

The exact insertion block from S6 §6 §2 (reproduced for paste-
readiness; ~28 LOC):

```lean
/-- Strengthened parent of `infinitely_many_primes_3_mod_4`: the
    elementary witness for "prime ≡ 3 (mod 4) > n" lives in the
    interval `(n, 4 * (n + 1)! - 1]`. -/
theorem infinitely_many_primes_3_mod_4_bounded (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 4 * (n + 1).factorial - 1 ∧ p % 4 = 3 := by
  let N := 4 * (n + 1).factorial - 1
  have hfact_pos : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
  have hN_mod : N % 4 = 3 := by simp only [N]; omega
  have hN_ge3 : N ≥ 3 := by simp only [N]; omega
  have hN_pos : 0 < N := by omega
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_3_mod_4 hN_ge3 hN_mod
  refine ⟨p, hp_prime, ?_, Nat.le_of_dvd hN_pos hp_div, hp_mod⟩
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_4fact : p ∣ 4 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 4
  have h_ge : 4 * (n + 1).factorial ≥ 1 := by omega
  have hN_add : N + 1 = 4 * (n + 1).factorial := by simp only [N]; omega
  have hp_dvd_diff : p ∣ (N + 1) - N :=
    Nat.dvd_sub (by rw [hN_add]; exact hp_dvd_4fact) hp_div
  simp only [Nat.add_sub_cancel_left] at hp_dvd_diff
  exact hp_prime.not_dvd_one hp_dvd_diff
```

### Race-safety note for the parent edit

`infinitely_many_primes_3_mod_4_bounded` is a NEW theorem name, not
present anywhere in `proofs/Proofs/InfinitudePrimes4k3.lean` as of
this push (`grep -n "infinitely_many_primes_3_mod_4_bounded"
proofs/Proofs/InfinitudePrimes4k3.lean` returns no matches). The
insertion at line 190 is byte-clean: it does not touch the existing
`_3_mod_4` theorem or any downstream `_infinite` / `no_largest_*`
corollaries.

Sibling file `InfinitudePrimes4k3OQ01Klein2.lean` (#19088) imports
`Proofs.InfinitudePrimes4k3` but does NOT reference `_bounded` (uses
`infinitely_many_primes_3_mod_4` directly). Adding `_bounded` to the
parent is therefore **additive** — neither Klein2 nor existing
OQ01.lean breaks under the parent insertion.

## §6. LOC delta vs S6 PREP §6

| Component                                | S6 PREP §6 LOC (target = OQ01.lean) | S8 PREP §3+§4 LOC (target = OQ01Tower.lean) | Delta |
|------------------------------------------|-------------------------------------|---------------------------------------------|-------|
| Parent-file edit (`_bounded`)            | ~28                                 | ~28 (unchanged)                              | 0     |
| Child additions (placement)              | ~67 (appended to OQ01.lean)         | ~96 (new file with imports + docstring + #check) | +29   |
| **Path C core, R1 total**                | **~95**                             | **~124**                                     | **+29** |
| Counting corollary (optional R2)         | ~80–100                             | ~80–100 (place either in OQ01.lean once DirichletsTheorem repaired, OR in OQ01Tower.lean as an addition) | 0     |

The +29 LOC overhead of option (b) over option (a) is the price of
regression resilience. For a slug whose primary blocker is a 40+ hour
unrepaired cross-slug regression with no known fix timeline, this is
a cheap trade.

## §7. ACT-readiness gate — Tier 1 refined for option (b)

Path C is **ACT-ready at gate level B (option b selected)** with this
S8 PREP merged. Refined Tier 1 entry:

### S8 ACT R1 (Path C core, regression-resilient routing)

**Scope**:
1. Insert `infinitely_many_primes_3_mod_4_bounded` into
   `proofs/Proofs/InfinitudePrimes4k3.lean` after line 190
   (§5 above, ~28 LOC).
2. Create new file `proofs/Proofs/InfinitudePrimes4k3OQ01Tower.lean`
   with imports + namespace + body + `#check`-block (§3 + §4 above,
   ~96 LOC).
3. Total ~124 LOC of Lean. Build: `./proofs/scripts/docker-build.sh
   Proofs.InfinitudePrimes4k3OQ01Tower` (single target compiles both
   parent edit and new file).
4. Expected Docker iterations: 1 (S6 §10 estimates ≤2 worst-case with
   the three honest-calibration markers M1/M2/M3 carried over from S6 PREP).

**Risk**: LOW-MED. All bearers verified zero-drift at pinned SHA across
22 hours. The three honest-calibration markers from S6 §10 (M1 `show`/
`unfold`, M2 `Nat.add_sub_cancel_left`, M3 `Nat.mul_le_mul_left`)
remain the only plausible obstacles. No new risk from sub-file
routing (the body is byte-identical modulo the `_hfact_pos` lint
suppression).

**Pre-flight checklist for ACT R1**:
- [ ] Confirm lake-manifest SHA is still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- [ ] Confirm `infinitely_many_primes_3_mod_4_bounded` is not already
  present in `InfinitudePrimes4k3.lean` (race-safety against parallel
  S6/S8 ACT authorship; per §5, currently zero matches)
- [ ] Confirm `InfinitudePrimes4k3OQ01Tower.lean` does not already exist
  (race-safety; currently `ls proofs/Proofs/InfinitudePrimes4k3*` returns
  4 files: parent, OQ01, OQ01Klein2, OQ03 — no Tower)
- [ ] `docker-build.sh Proofs.InfinitudePrimes4k3OQ01Tower` clean
- [ ] If `show` fails on `primeSeq_3_mod_4 (k+1)` unfolding, fall back
  to `unfold primeSeq_3_mod_4` (M1)
- [ ] If `Nat.add_sub_cancel_left` not found in parent edit (line `simp
  only [Nat.add_sub_cancel_left]`), switch to `add_tsub_cancel_left`
  (M2)
- [ ] If `Nat.mul_le_mul_left 4 hfact_le` API shape mismatches, fall
  back to `nlinarith` or `gcongr` (M3)
- [ ] Update `state.md` after merge (post-ACT: "S8 ACT R1 landed via
  Tower sub-file; counting corollary still pending")
- [ ] Update JSON: bump `iteration` to 7 (or per next STATE-SYNC
  convention), refresh `currentState.phase`/`focus`/`nextAction`/
  `since`/`lastUpdate`, add Tower file to `knowledge.builtItems`

### S8 ACT R2 (counting corollary) — unchanged

Same as S6 §8 Tier 2 (`primes_3_mod_4_count_factorial_bound`, ~80–100
LOC). Sub-file routing decision: the counting corollary can live in
either `OQ01Tower.lean` (preserving regression resilience) or in
`OQ01.lean` (if `DirichletsTheorem` is eventually repaired between R1
and R2). The default per option (b) is the Tower file.

## §8. Composability with prior work

### vs S2 ACT (PR #18341, `InfinitudePrimes4k3OQ01.lean`)

- Tower sub-file does NOT modify `OQ01.lean` (the bridge corollary file).
  Both files coexist; `OQ01.lean` continues to suffer the regression
  via `DirichletsTheorem` import, but `OQ01Tower.lean` is independently
  buildable.
- Shared `namespace InfinitudePrimes4k3OQ01` across the two physical
  files: Lean's namespace mechanism allows additive extension; no
  symbol collision.
- The seven `#check` statements at the end of `OQ01Tower.lean` mirror
  `OQ01Klein2.lean`'s `#check` block convention (#19088 lines 220–224).

### vs S3 ACT R1 (PR #19088, `InfinitudePrimes4k3OQ01Klein2.lean`)

- Klein2 and Tower are **orthogonal**: Klein2 covers q ∈ {3, 4, 6}
  Klein-2 cases; Tower provides explicit factorial bounds for the
  q = 4 case. Different parameterisations, different theorems, no
  symbol overlap.
- Both follow the regression-resilient sub-file convention: import
  only `Proofs.InfinitudePrimes4k3` + `Mathlib.Data.Nat.Factorial.Basic`
  + `Mathlib.Tactic` (Klein2 matches exactly).
- File naming: `OQ01Klein2.lean` + `OQ01Tower.lean` establishes the
  consistent suffix-pattern (`OQ01<topic>.lean`) for future
  regression-resilient sub-files. Future authors of Klein4 (S3b ACT
  q = 8) and S3c (q ∈ {12, 24}) can adopt `OQ01Klein4.lean` and
  `OQ01CRT24.lean` (or similar) for the same regression-isolation
  rationale.

### vs S6 PREP §6 (paste-ready skeleton)

- S6's child-side body is reused **byte-identical** modulo the
  `_hfact_pos` → `_hfact_pos` lint-suppression rename. The mathematical
  content is preserved 100%; only the placement changes.
- S6 §10 honest-calibration markers M1/M2/M3 carry over unchanged.
- S6 §7 LOC reconciliation table needs a small augmentation row for
  the option-(b) overhead (+29 LOC); this is documented in §6 above.
- S6 §11 conflict-free guarantee continues to hold (S8 PREP is
  doc-only sessions-file).

### vs the eventual `DirichletsTheorem.lean` repair

- When `DirichletsTheorem` is repaired, the Tower sub-file's contents
  can be merged back into `OQ01.lean` via a low-cost refactor: copy
  the seven Tower-file theorems into `OQ01.lean`, delete
  `OQ01Tower.lean`, no proof-content change. The Klein2 file would
  remain split (or be similarly merged back, depending on slug
  preference at that time).
- The seven `#check` statements at the end of `OQ01Tower.lean`
  document the public interface, so a future merge-back diff is
  mechanical.

## §9. Honest-calibration markers

### Marker N1 — additive namespace across files (LOW concern)

Lean's `namespace InfinitudePrimes4k3OQ01 … end` blocks in two
separate files (existing `OQ01.lean` + new `OQ01Tower.lean`) silently
extend the namespace additively. No symbol collision is possible
because:
- `OQ01.lean` introduces `zmod_4_eq_three_iff`,
  `primes_3_mod_4_set_eq`, `dirichlet_3_mod_4_via_elementary`,
  `elementary_via_dirichlet_zmod` — none overlap with Tower's seven
  declarations.
- The Tower file's seven names (`tower`, `primeSeq_3_mod_4`,
  `primeSeq_3_mod_4_prime`, `primeSeq_3_mod_4_mod`,
  `primeSeq_strict_mono`, `primeSeq_le_tower`,
  `primes_3_mod_4_explicit_tower_bound`) are all `InfinitudePrimes4k3OQ01.`-
  qualified, and none collide with `OQ01.lean`'s four declarations.

**Confidence**: HIGH (95%). Verified by `grep -n "^theorem\|^lemma\|^def\|^noncomputable"
proofs/Proofs/InfinitudePrimes4k3OQ01.lean` enumeration (4 declarations,
zero overlap with Tower's 7). The only fragility is if a future
edit to `OQ01.lean` introduces a same-named declaration — but that's
out-of-scope for the Tower file PR.

### Marker N2 — `Mathlib.Tactic` transitively imports `Mathlib.Order.Monotone.Basic` (LOW concern)

The Tower body uses `strictMono_nat_of_lt_succ`, which lives in
`Mathlib/Order/Monotone/Basic.lean`. The Klein2 file's import block
is `import Proofs.InfinitudePrimes4k3 + Mathlib.Data.Nat.Factorial.Basic
+ Mathlib.Tactic` and DOES use `Nat.dvd_factorial` (a Mathlib
declaration) without explicit `Mathlib.Data.Nat.Factorial.Basic`
re-import, so `Mathlib.Tactic` must transitively include the relevant
imports. The Tower file matches Klein2's import block exactly, so
the transitive-import assumption holds.

**Confidence**: HIGH (90%). Verified by inspection of Klein2 file
imports + its successful Docker build at the same pin SHA
(#19088 docker-verified 3059 jobs). If `strictMono_nat_of_lt_succ`
fails to resolve at ACT time, the fallback is to add an explicit
`import Mathlib.Order.Monotone.Basic` line (1 LOC, zero risk).

### Marker N3 — `#check`-block hygiene (LOW concern)

The seven `#check @InfinitudePrimes4k3OQ01.<name>` statements at
the end of `OQ01Tower.lean` mirror Klein2's `#check`-block convention.
These are pure type-checking statements (no proof obligation, no
runtime cost), serving as a public-interface summary. They are not
strictly required for compilation; if a `#check` triggers a parse
issue (unlikely — Klein2 uses identical syntax), they can be removed
without affecting the theorems.

**Confidence**: HIGH (95%). Klein2 file demonstrates the pattern
works at the pinned SHA. The `@` prefix forces full-name resolution
including implicit arguments, which is the safer form vs unqualified
`#check`.

### Markers M1, M2, M3 from S6 PREP §10 — carried over

The three honest-calibration markers from S6 PREP §10 (`show` /
`unfold` fallback, `Nat.add_sub_cancel_left` vs `add_tsub_cancel_left`,
`Nat.mul_le_mul_left` API shape) apply to the body proofs and carry
over unchanged to the Tower sub-file (the body is byte-identical
modulo `_hfact_pos`).

## §10. Conflict-free guarantee

This S8 PREP touches **exactly one file**:

```
research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-16-s8-prep-path-c-tower-subfile-routing.md  (NEW, this file)
```

Untouched:

- All `.lean` files (parent + OQ01 + Klein2 + OQ03 + lakefile).
- `proofs/lake-manifest.json` (pin SHA unchanged).
- `state.md` — unchanged (S7 STATE-SYNC's recent edits are preserved
  in full; a future STATE-SYNC after this PREP merges can absorb the
  option-(b) selection into the recommended-next-session menu).
- `knowledge.md`, `problem.md` — unchanged.
- `src/data/research/problems/infinitude-primes-4k3-oq-01.json` — unchanged.
- All other `sessions/*.md` files (9 prior sessions all on main).
- `gallery/meta.json`, `src/data/proofs/infinitude-primes-4k3*/*` —
  out of PREP scope (gallery promotion is a separate follow-up;
  remains under R5 in S7's nextAction menu).

Per `feedback_researcher_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep.md`:
this PREP follows the canonical "doc-only adapt-skeleton" pattern,
where a prior session left a routing/decision gap and this session
closes it with a paste-ready skeleton + recipe.

Per S6 PREP §11 "Conflict-free guarantee" pattern: this PREP
similarly defers `state.md`/JSON updates to the next STATE-SYNC.

## §11. Race-safety + open-PR inventory

### Pre-write probe (2026-05-16T05:22Z)

- `gh pr list --repo rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open --limit 10` → `[]` (zero open PRs on this slug).
- `gh pr list --repo rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state all --limit 5` confirms the most-recent merge is `#19323` (S7 STATE-SYNC, merged 23:42:12Z 2026-05-15).
- `git log origin/main --oneline --grep="infinitude-primes-4k3" --since="2026-05-15T23:42:12Z"` → empty (zero post-S7 activity on this slug).
- `git log origin/main --oneline --since="2026-05-15T23:42:12Z"` → 134 system-wide commits in the ~5h35m post-S7 window, but none touching this slug.
- Worktree branch: `research/infinitude-primes-4k3-oq-01-s8-prep-tower-routing`, branched from `origin/main` at HEAD `cf1cfa085e4` (most-recent main commit at probe time).
- Lake-manifest SHA at HEAD: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S5 PREP).

### File-path uniqueness

- `2026-05-16-s8-prep-path-c-tower-subfile-routing.md` — S8 prefix
  is distinct from S2/S3/S3b/S3c/S4/S5/S6/S7 (all prior session
  prefixes for this slug). Topic suffix `path-c-tower-subfile-
  routing` is distinct from any prior STATE-SYNC / PREP topic on
  this slug (`s2c`/`s3b`/`s3c`/`deployer-stall`/`goalstate-sim`/
  `path-c-act-readiness-gate`/`post-batch-drain-wave`).

### Doc-only conflict surface

- Zero `.lean` diff, zero `meta.json` diff, zero `state.md` diff,
  zero `knowledge.md` diff, zero `problem.md` diff, zero JSON diff.
- Only writes to `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-16-s8-prep-path-c-tower-subfile-routing.md`.
- No `gallery/meta.json` or `src/data/proofs/*` modifications.

### No mid-cycle slug-state mutations observed

`gh pr list ...` returned `[]` at probe time AND at this push time
(approximately 1–2 minutes apart). State.md/JSON content read at
probe time matches what's currently on main; no parallel-author race.

Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`: all
`gh` calls in this session use explicit `--repo rjwalters/lean-genius`.

## §12. Honest contribution boundary

This is a **PREP** that closes S7 §11's routing decision (option a
wait vs option b sub-file) by selecting option b and adapting S6
PREP §6's paste-ready skeleton for the new sub-file
`InfinitudePrimes4k3OQ01Tower.lean`. Not an ACT, not a STATE-SYNC,
not a parent-regression diagnose, not a gallery promotion.

**What this PREP does**:

1. Selects option (b) (sub-file routing) over option (a) (wait for
   `DirichletsTheorem` repair) per the §2 analysis (decision-cost
   asymmetry favours option b).
2. Specifies the new file `InfinitudePrimes4k3OQ01Tower.lean`'s
   imports, namespace structure, and `#check`-block (§3).
3. Provides paste-ready body (§4) byte-identical to S6 §6 modulo
   one lint-suppression micro-edit (`_hfact_pos`).
4. Re-confirms the parent-file edit (§5) is unchanged and the
   insertion target (line 190 / line 192) is still accurate at
   current main HEAD.
5. Documents LOC delta (+29 LOC overhead for sub-file routing — §6).
6. Refines the ACT-readiness gate Tier 1 entry with sub-file-
   specific pre-flight checklist (§7).
7. Documents composability with S2 ACT, Klein2, S6 PREP, and the
   eventual `DirichletsTheorem` repair (§8).
8. Adds three new honest-calibration markers (N1 additive namespace,
   N2 transitive imports, N3 #check hygiene) specific to sub-file
   routing; carries over S6's M1/M2/M3 unchanged (§9).
9. Records bearer drift recheck at pinned SHA — zero drift over
   the 22-hour S5 → S8 window (§1).

**What this PREP does NOT do**:

- Does not implement any Lean code (no `.lean` file diff).
- Does not run a Lean build (doc-only; host disk pressure at
  100% capacity on `/System/Volumes/Data` would block Docker builds
  anyway per `feedback_researcher_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat`).
- Does not modify `state.md`, JSON, `knowledge.md`, or
  `problem.md` (deferred to next STATE-SYNC, matching S6 PREP §11
  pattern).
- Does not audit / repair `proofs/Proofs/DirichletsTheorem.lean`
  v4.26.0 9-error regression (cross-slug doctor/mechanic
  territory; flagged in S3 ACT R1 / S7 §11 / this §2 analysis).
- Does not implement S6 ACT R2 counting corollary (deferred to
  post-R1 ACT iteration; the routing-decision question for R2
  is briefly addressed in §7 Tier 2 entry).
- Does not promote the gallery meta.json (R5 in S7's nextAction
  remains pending; doc-only meta.json edit, separate from the
  PREP/ACT chain).

The deliverable is a **routing-decision selection + paste-ready
sub-file skeleton** that unblocks Path C ACT R1 from the cross-
slug regression dependency. Reading S6 PREP §6 + S7 §11 without
this S8 PREP would leave the next ACT picker re-resolving the
option a/b decision and re-adapting the skeleton; this PREP
eliminates that work and ships the ACT picker a paste-ready
deliverable.

### Confidence calibration

- **Routing decision (option b)**: HIGH (95%). The Klein2 file
  precedent + the 40+ hour unrepaired regression + the +29 LOC
  overhead being small relative to the ACT R1 budget make option
  b the dominant choice. The only contingency under which option
  a wins is "DirichletsTheorem repaired in the next few hours" —
  unlikely given the prior 40h of inactivity.
- **Paste-ready body correctness**: HIGH (90%). Byte-identical to
  S6 §6 modulo one lint-suppression edit; S6 §10's M1/M2/M3
  markers carry over for any tactical surprises.
- **Import surface minimality**: HIGH (95%). Klein2 file
  demonstrates the same import block compiles successfully at the
  pinned SHA.
- **Conflict-free guarantee**: HIGH (100%). Single-file doc-only
  diff with unique path; zero open PRs on slug; zero parallel
  authorship observed in the ~5h35m post-S7 window.

---

## Appendix A — pre-flight commands for the ACT picker

```bash
# 1. Confirm pin SHA unchanged
grep -B 1 -A 5 '"name": "mathlib"' proofs/lake-manifest.json | head -10
# Expected: rev "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"

# 2. Confirm parent insertion target still has no _bounded
grep -n "infinitely_many_primes_3_mod_4_bounded" proofs/Proofs/InfinitudePrimes4k3.lean
# Expected: no output

# 3. Confirm Tower file does not already exist
ls proofs/Proofs/InfinitudePrimes4k3*.lean
# Expected: 4 files (parent + OQ01 + OQ01Klein2 + OQ03); no Tower

# 4. Apply the parent edit (§5) then create the new file (§3 + §4)
# (manual editing or sed-script, ~28 LOC parent insert + ~96 LOC new file)

# 5. Build
./proofs/scripts/docker-build.sh Proofs.InfinitudePrimes4k3OQ01Tower

# 6. Sibling sanity check (no regressions in unrelated files)
./proofs/scripts/docker-build.sh Proofs.InfinitudePrimes4k3OQ01Klein2

# 7. Commit + push + PR per CLAUDE.md guidance
```

## Appendix B — knowledge propagation for future researchers

If this S8 PREP merges and the subsequent ACT R1 succeeds, the
following technique-index entries are candidates:

- "Regression-resilient sub-file split" — outcome: `success` (if R1
  ships); used in: `infinitude-primes-4k3-oq-01` (Klein2 + Tower),
  potentially future Klein4 / S3c sub-files in the same slug.
- "S6/S8 PREP chain — paste-ready skeleton + routing-decision
  closure" — outcome: `success` (if R1 ships); used in:
  `infinitude-primes-4k3-oq-01`; pattern: when a prior PREP leaves
  a routing/decision unresolved, a follow-up PREP can adapt the
  skeleton + commit to the routing without inventing new
  mathematical content.

The first entry is a candidate addition to
`research/knowledge/technique-index.json` after R1 ships. The second
is a candidate memory entry (researcher meta-pattern) — too narrow
to be a technique, but useful for the next researcher landing on a
similar option-a-vs-b routing-decision PREP pattern.
