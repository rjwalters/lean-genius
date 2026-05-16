## Session 2026-05-16 (Session 15 ACT) — A.1 `choose_dvd_lcmRange` via prime-factorization decomposition + per-prime-power divisibility

**Mode**: ACT (Lean-modifying)
**Outcome**: progress (one new theorem; 0 new sorries, 0 new axioms)
**Predecessor**: S14 STATE-SYNC (PR #19352, researcher-4, merged 2026-05-16T01:08:25Z) — pre-discharged all S13 §3.6 ACT-time risk flags, pinned all 9 bearers at lake SHA, renumbered ACT sequence S15=A.1, S16=A.2.

### TL;DR

Ships the A.1 ACT planned by S12 PREP (#19217), audited by S13 PREP (#19299), and given a GREEN readiness gate by S14 STATE-SYNC (#19352, §6.2):

```lean
theorem choose_dvd_lcmRange {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Nat.choose n k ∣ lcmRange n := by
  rw [← Nat.prod_pow_factorization_choose n k hk]
  apply Finset.prod_dvd_of_isRelPrime
  ...
```

Adds Part 11 (~46 LOC of theorem + ~57 LOC of docstring + section header) to `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`. Adds two imports (`Mathlib.Data.Nat.Choose.Factorization` and `Mathlib.RingTheory.Coprime.Lemmas`) — both pinned in S14 §3 bearer table. **0 new sorries, 0 new axioms** (file remains 0/0).

### §1 What this iteration does

Per S14 §6.1, this is the post-renumber S15 ACT = A.1. The theorem statement is exactly S12 PREP §"S12 ACT skeleton" / S13 PREP §3:

  `theorem choose_dvd_lcmRange {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) : Nat.choose n k ∣ lcmRange n`

The proof structure follows the S13 §3 goal-state walk, with one local optimization in sub-goal 1: instead of casing twice (v_p, v_q) and applying coprime-of-distinct-primes inside the nested branch, the proof uses `Nat.coprime_pow_primes _ _ hpp hqq hne` directly (a single Mathlib invocation) to discharge the `Coprime (p^v_p) (q^v_q)` step before bridging to `IsRelPrime` via `Nat.coprime_iff_isRelPrime`. This shaves ~3 LOC vs the S13 sketch.

### §2 Why this lemma is the right A.1 entry point

The full Apéry denominator-control target needs `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m·C(n,m) ∣ lcmRange n` (A.2, ~80-120 LOC, S16). A.2 requires bridging `factorization` (ℕ-valued Finsupp, the form used by `pow_factorization_choose_le`) with `emultiplicity` (ℕ∞-valued, the form used by `Nat.Prime.emultiplicity_choose` = Kummer + `Nat.Prime.emultiplicity_factorial` = Legendre), plus a per-prime case-analysis on whether `p ∣ m`.

The A.1 lemma `choose_dvd_lcmRange` discharges the `m = 0` analogue (the bare `C(n,k)` without the `m` factor), proving in passing that the Mathlib factorization-decomposition + per-prime-power-bound + pairwise-coprime-product workflow is fully present and usable on ℕ. A.2's later case-analysis (when `p ∣ m`) adds an extra `+ v_p(m)` summand to the prime-power exponent but uses the same `Finset.prod_dvd_of_isRelPrime` lifting infrastructure. So A.1 is both a free-standing result and a load-bearing scaffold for A.2.

A.1 also has standalone value: it discharges the `C(n+m, m)` divisibility step in vdP §6's alternating-bilinear summand (S17+ ACT), since `C(n+m, m) ∣ lcmRange (n+m)` by A.1, and then `lcmRange n ∣ lcmRange (n+m)` by the existing `lcmRange_dvd_of_le` (Part 8a) lifts the divisor.

### §3 Proof outline

**Setup**: `rw [← Nat.prod_pow_factorization_choose n k hk]` rewrites the goal from `Nat.choose n k ∣ lcmRange n` to `(∏ p ∈ Finset.range (n+1), p^v_p(C(n,k))) ∣ lcmRange n`.

**Apply lifting lemma**: `apply Finset.prod_dvd_of_isRelPrime` produces two sub-goals:
1. `(↑(Finset.range (n+1)) : Set ℕ).Pairwise (IsRelPrime on fun p => p^v_p(C(n,k)))`
2. `∀ p ∈ ↑(Finset.range (n+1)), p^v_p(C(n,k)) ∣ lcmRange n`

The `DecompositionMonoid ℕ` typeclass needed by `Finset.prod_dvd_of_isRelPrime` is satisfied via the `Mathlib/Algebra/GCDMonoid/Basic.lean:493` instance `[Nonempty (GCDMonoid α)] : DecompositionMonoid α`, in scope via the existing `import Mathlib.Algebra.GCDMonoid.Finset` (already at file top).

**Sub-goal 1 (Pairwise IsRelPrime)**: after `intro p _ q _ hne; simp only [Function.onFun]`:
- If `v_p = 0`: `rw [hv_p, pow_zero]` reduces to `IsRelPrime 1 (q^v_q)`, discharged by `isRelPrime_one_left`.
- If `v_q = 0` (and `v_p ≠ 0`): symmetric, via `isRelPrime_one_right`.
- Both v_p, v_q > 0: each of p, q is prime (by `factorization_eq_zero_of_not_prime` contrapositive: `v ≠ 0 ⇒ p.Prime`). Distinct primes have coprime powers via `Nat.coprime_pow_primes _ _ hpp hqq hne : Nat.Coprime (p^v_p) (q^v_q)`. The bridge `Nat.coprime_iff_isRelPrime` converts to the goal.

**Sub-goal 2 (Per-prime-power divisibility)**: after `intro p _`:
- If `v_p = 0`: `rw [hv, pow_zero]` reduces to `1 ∣ lcmRange n`, discharged by `one_dvd _`.
- If `v_p > 0`: `p` is prime (same contrapositive); `p^v_p > 0` via `pow_pos hpp.pos _`; `p^v_p ≤ n` via `Nat.pow_factorization_choose_le hn`; apply `dvd_lcmRange hpow_pos hpow_le` (the local lemma at file line 148).

### §4 Bearer surface table (pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| # | Bearer | Path | Line | First pinned by | Used in |
|---|--------|------|------|-----------------|---------|
| 1 | `Nat.prod_pow_factorization_choose` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 267 | S12 PREP | A.1 setup `rw` |
| 2 | `Nat.pow_factorization_choose_le` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 196 | S12 PREP | A.1 sub-goal 2 Case B |
| 3 | `Nat.factorization_eq_zero_of_not_prime` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 129 | S13 PREP (risk flag) → S14 PRE-DISCHARGED §4.2 | A.1 sub-goal 1 & 2 (prime cases) |
| 4 | `Nat.coprime_iff_isRelPrime` | `Mathlib/Data/Nat/GCD/Basic.lean` | 218 | S13 PREP (risk flag) → S14 PRE-DISCHARGED §4.1 | A.1 sub-goal 1 (both positive) |
| 5 | `Nat.coprime_pow_primes` | `Mathlib/Data/Nat/Prime/Basic.lean` | 200 | (new this S15 — bypass route) | A.1 sub-goal 1 (both positive) |
| 6 | `Finset.prod_dvd_of_isRelPrime` | `Mathlib/RingTheory/Coprime/Lemmas.lean` | 252 | S13 PREP §2.4 | A.1 main `apply` |
| 7 | `isRelPrime_one_left` | `Mathlib/Algebra/Divisibility/Units.lean` | 166 | S14 §5 (newly pinned) | A.1 sub-goal 1 (v_p = 0) |
| 8 | `isRelPrime_one_right` | `Mathlib/Algebra/Divisibility/Units.lean` | 167 | (new this S15 — paired with #7) | A.1 sub-goal 1 (v_q = 0) |
| 9 | `DecompositionMonoid` instance via `[Nonempty (GCDMonoid α)]` | `Mathlib/Algebra/GCDMonoid/Basic.lean` | 493 | S13 PREP §2.5 | A.1 typeclass resolution |

#### §4.1 New bearer #5: `Nat.coprime_pow_primes`

S13 PREP §3.4 sketched the both-positive sub-case as: `have hcopw : Nat.Coprime (p^v_p) (q^v_q) := (Nat.Coprime.pow_left v_p hcop).pow_right v_q` where `hcop : Nat.Coprime p q` is derived from `(coprime_primes hpp hqq).2 hne`. This S15 ACT uses the direct one-line bearer `Nat.coprime_pow_primes _ _ hpp hqq hne` instead, which is the same Mathlib content packaged with the two-step `.pow_left.pow_right` chain inlined. Pinned at `Mathlib/Data/Nat/Prime/Basic.lean:200`:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Prime/Basic.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '198,205p'
```

Output (excerpt):

```lean
theorem coprime_primes {p q : ℕ} (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p ≠ q := ...

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : Prime p) (pq : Prime q) (h : p ≠ q) :
    Coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _
```

In scope after the existing `import Mathlib.Tactic` (transitively pulls in `Mathlib.Data.Nat.Prime.Basic` via standard prime API).

#### §4.2 New bearer #8: `isRelPrime_one_right` (companion to #7)

S14 §5 pinned `isRelPrime_one_left` at `Mathlib/Algebra/Divisibility/Units.lean:166`. The companion `isRelPrime_one_right` is one line below at the same file:

```lean
-- line 166
theorem isRelPrime_one_left : IsRelPrime 1 x := isUnit_one.isRelPrime_left
theorem isRelPrime_one_right : IsRelPrime x 1 := isUnit_one.isRelPrime_right
```

This S15 ACT uses both: sub-goal 1's v_p=0 branch uses `isRelPrime_one_left`; the v_q=0 branch uses `isRelPrime_one_right`.

### §5 Imports added

Two new imports near the file top:

```lean
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Factorization    -- NEW (S15): for Nat.prod_pow_factorization_choose + Nat.pow_factorization_choose_le
import Mathlib.RingTheory.Coprime.Lemmas         -- NEW (S15): for Finset.prod_dvd_of_isRelPrime
import Mathlib.Tactic
```

`Mathlib.Tactic` already brings in `Nat.coprime_iff_isRelPrime`, `Nat.factorization_eq_zero_of_not_prime`, `Nat.coprime_pow_primes`, and `isRelPrime_one_left/right` transitively. The two new explicit imports cover the lemmas that `Mathlib.Tactic` does not transitively reach.

### §6 LOC + theorem-count delta

| Metric | Before S15 | After S15 | Delta |
|--------|-----------|----------|-------|
| `BaselProblemOQ01OQ01OQ02OQ02.lean` LOC | 799 (S11 post-fix) | 905 | +106 |
| Theorem count | 35 | 36 | +1 |
| Sorry count | 0 | 0 | 0 |
| Axiom count | 0 | 0 | 0 |
| Imports | 2 | 4 | +2 |

Of the +106 LOC: ~46 are the theorem body, ~54 are the docstring + Why section + Part header, ~6 are comments inside the body. The +1 theorem is `choose_dvd_lcmRange`.

### §7 Docker build status

**BUILD VERIFIED CLEAN** via `LEAN_BUILD_TIMEOUT=20m LEAN_MEMORY_LIMIT=16384 ./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ02` at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
⚠ [3058/3058] Built Proofs.BaselProblemOQ01OQ01OQ02OQ02 (17s)
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean:256:23: This simp argument is unused:
  Finset.sum_range_succ
...
Build completed successfully (3058 jobs).
```

- **3058 jobs** built (vs S11's 3058-job baseline — same job count, since the new theorem is a fresh top-level addition that does not change the dependency graph cardinality at the per-namespace level).
- Final-file compile took **17s** post-import. Total wall-clock from script invocation: ~2 min including the `Mathlib` cache fetch (7727 files from leanprover-community Azure cache) and dependency unpacking (35.2s).
- **0 errors**. **0 new warnings introduced by this ACT.** The single warning at line 256:23 is **pre-existing** in the slug's `harmonicCubed_lcm_clear_nat` proof (Session 4, 2026-05-08) — it is in the `simp [harmonicCubed, Finset.sum_range_succ]` invocation, which predates this S15 by 8 days. Not in scope for S15 ACT; tagged for future hermit / doctor sweep.
- **Build log**: `.loom/logs/researcher-9-basel-s15-build.log` (69 lines, 100% download + unpack + build trace).

### §8 What remains after this S15

Per S14 §6.1 renumber:

- **S16 ACT (A.2)**: prove `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m·C(n,m) ∣ lcmRange n` via Kummer/Legendre, ~80-120 LOC. Bearers `Nat.Prime.emultiplicity_choose` (Multiplicity.lean:209) + `Nat.Prime.emultiplicity_factorial` (Multiplicity.lean:102) pinned by S13 §5. One new bridge bearer needed at S16 ACT time: `factorization` ↔ `emultiplicity` (likely `Nat.Prime.emultiplicity_eq_factorization` or `Nat.factorization_eq_emultiplicity` at `Mathlib/Data/Nat/Factorization/Defs.lean`; pin under then-current lake SHA before consuming).
- **S17+ ACT (vdP §6 application)**: apply S16's `mul_choose_dvd_lcmRange` to the alternating-bilinear summand `∑_{m=1}^{k} (-1)^{m-1} / (2 m^3 C(n,m) C(n+m,m))` inside vdP §6's closed form. Combine with `harmonicCubed_lcm_clear` (S4 ACT, already in slug) and a new `aperyA_explicit_formula` to close `denominator_control` and eliminate the parent axiom at `BaselProblemOQ01OQ01OQ02.lean:385`. ~80-150 LOC of `vdpAlternatingSum_lcm_clear` + ~80 LOC of `aperyA_explicit_formula` + ~80 LOC of assembly.

### §9 Conflict-free assertions

This S15 ACT modifies exactly three files:

1. **MODIFIED**: `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` — adds 2 imports near the top, adds Part 11 (Section header + docstring + `choose_dvd_lcmRange` theorem) before `end BaselProblemOQ01OQ01OQ02OQ02`. Preserves all prior content verbatim.
2. **MODIFIED**: `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/state.md` — appends "Session 15 ACT" section near the top (above Session 14 STATE-SYNC).
3. **MODIFIED**: `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02.json` — refreshes `currentState.iteration` (14 → 15), `currentState.since`, `currentState.focus`, `currentState.nextAction`, `lastUpdate`; adds 2 entries each to `knowledge.insights` and `knowledge.nextSteps`; updates `knowledge.builtItems` with the new theorem; updates the slug's `leanFiles[].lineCount` (799 → 905) and `theoremCount` (35 → 36).
4. **NEW**: this session note `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-16-s15-act-choose-dvd-lcm-range.md`.

#### §9.1 Open-PR conflict surface (this slug)

At ACT-write time: 0 open PRs on this exact slug (the 2 open PRs `#17551`, `#17619` are for the sibling slug `-oq-02-oq-03`, last component `oq-03`, not `oq-02`; they touch a different Lean file).

#### §9.2 Open-PR conflict surface (other slugs touching JSON or Lean)

The JSON and Lean files are owned by this slug only. No other slug's PRs touch them.

### §10 Falsifiability

This S15 ACT is falsifiable along three axes:

1. **Docker build outcome**: the new theorem must build cleanly under the lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If `lake build Proofs.BaselProblemOQ01OQ01OQ02OQ02` fails, S15 must either (a) refactor the proof to use the actually-available API or (b) re-pin to a different bearer set. The build log is captured at `.loom/logs/researcher-9-basel-s15-build.log`.
2. **Bearer surface (§4)**: if any of the 9 pin commands in S14 §3.1 / §4.1 / §4.2 / §5 + this S15 §4.1 returns a different signature or line number than this report claims, the bearer surface is wrong and the proof must be repaired.
3. **Theorem signature**: if a downstream consumer (S16 ACT, S17+ ACT, or the parent file's `denominator_control` discharge) requires a different hypothesis shape (e.g. `0 ≤ k` instead of `k ≤ n`, or `0 < n` weakened to `n ≠ 0`), the theorem must be re-stated. The current signature matches the S12 PREP / S13 PREP / S14 STATE-SYNC consensus.

### §11 Memory pattern alignment

This iteration matches:

- `feedback_researcher_postship_pivot_ships_lean_act_realizing_explicit_mechanic_grade_followon.md` — exactly: prior STATE-SYNC (S14 #19352) named the Lean-modifying mechanic-grade follow-on (S15 ACT = A.1) as TOP priority with caller audit (S13 §3 goal-state walk) + bearer pin (S14 §3-§5, 9 bearers) + ~1 Docker iter estimate (~30-40 LOC, well under budget). This S15 ships the realization (Lean edit, Docker build, gallery meta + research state sync).

### §12 Session metrics

| Metric | Value |
|--------|-------|
| Mode | ACT (Lean-modifying) |
| New files | 1 (this session note) |
| Modified files | 3 (Lean, state.md, JSON) |
| Lean LOC delta | +106 (799 → 905) |
| Theorem delta | +1 (`choose_dvd_lcmRange`) |
| Sorry delta | 0 |
| Axiom delta | 0 |
| New bearer pins | 2 (`Nat.coprime_pow_primes`, `isRelPrime_one_right`) |
| New imports | 2 (`Mathlib.Data.Nat.Choose.Factorization`, `Mathlib.RingTheory.Coprime.Lemmas`) |

**Axiom delta this session**: 0.
