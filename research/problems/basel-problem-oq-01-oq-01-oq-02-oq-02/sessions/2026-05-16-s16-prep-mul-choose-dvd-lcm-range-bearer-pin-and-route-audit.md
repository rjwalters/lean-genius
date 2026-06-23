## Session 2026-05-16 (Session 16 PREP) — `mul_choose_dvd_lcmRange` (A.2) route audit + bridge bearer pin + decomposition recommendation (doc-only)

**Mode**: PREP (no Lean modifications; doc-only)
**Outcome**: progress (4 new bearer pins, 1 deprecation note, 0-drift recheck of 9 existing pins, route recommendation, S17 ACT split-or-monolithic recommendation, naive-route counterexample re-validation)
**Predecessor**: S15 ACT (PR #19397, researcher-9, merged 2026-05-16T03:52:10Z) — shipped A.1 `choose_dvd_lcmRange` Docker-verified clean, +1 theorem, +106 LOC, 0 sorries, 0 axioms.

### TL;DR

S15 ACT shipped A.1 (`choose_dvd_lcmRange`) ~20 min ago. The natural next ACT is A.2 (`mul_choose_dvd_lcmRange`), but per the post-S15 state.md `nextAction`, it needs **one more bridge bearer pinned at S16 ACT time** (factorization ↔ emultiplicity) before the Kummer/Legendre route is consumable. This S16 PREP:

1. Pins **4 new Mathlib bearers** at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from S14 §3 / S15):
   * `Nat.factorization_mul` at `Mathlib/Data/Nat/Factorization/Defs.lean:155`
   * `Nat.factorization_le_factorization_choose_add` at `Mathlib/Data/Nat/Choose/Factorization.lean:142`
   * `Nat.multiplicity_eq_factorization` at `Mathlib/Data/Nat/Factorization/Defs.lean:89`
   * `multiplicity_eq_of_emultiplicity_eq_some` at `Mathlib/RingTheory/Multiplicity.lean:73`
2. Re-verifies the 9 existing bearers from S14 §3 + S15 §4 at the same lake SHA (0 drift expected).
3. Records the `Nat.succ_mul_choose_eq` **DEPRECATION** (2025-12-09) → `Nat.add_one_mul_choose_eq`. The slug's `mul_choose_eq_mul_choose_pred` (Part 5 ACT) already uses the new name (line 367); only its docstring at line 121 cites the old name (informational; no fix needed).
4. Audits three viable routes (A: full Kummer via emultiplicity bridge; B: hybrid identity-then-prime-power-decomp; C: S15-framework extension with a sharper per-prime lemma) and recommends **Route C with split S17a + S17b ACTs**: ~60-80 LOC per-prime bound first, then ~30-40 LOC prime-power-decomposition lift — total ~100 LOC across two manageable Docker-verifiable ACTs vs one 100-150 LOC monolith.
5. Documents the S13 §5.1 naive-route counterexample (n=4, m=2, p=2) in self-contained form.
6. **S17 readiness gate**: 9/9 GREEN for the per-prime bound (Route C, sub-step a) using all-existing-bearers; 1 additional bearer pin (Mathlib's Kummer-carry bound, or alternate formulation) is needed only if Route A or B is taken instead.

This is a doc-only iteration: 1 new sessions file, state.md head update prepending S16 PREP section, JSON refresh (iteration 15 → 16, nextAction, lastUpdate, +2 insights, +2 nextSteps). 0 Lean edits. 0 sibling-slug edits.

### §1 Slug state at S16 PREP start

Post-S15-ACT-merge state (per HEAD `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`):

| Metric | Value |
|--------|-------|
| File LOC | 905 (post-S15 +106) |
| Sorry count | 0 |
| Axiom count | 0 |
| Theorem count | 36 (post-S15 +1) |
| Lake SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S14 §3 pin) |
| Open PRs on slug | 0 |
| Sibling slug open PRs (`-oq-03`) | 2 (`#17619`, `#17551`) — different Lean file, build-pending |
| Days since lake SHA last touched | ≥9 (per `proofs/lake-manifest.json` HEAD) |

### §2 Bearer drift recheck — 9 existing pins, 0 drift expected, 0 drift observed

Per memory pattern `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`, the ACT picker must re-verify bearer typeclasses and line positions before paste. S16 PREP discharges that check for all S14 + S15 pins at the SAME lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Bearer | File | Pinned line | S16 PREP recheck | Drift |
|---|--------|------|------------|------------------|-------|
| 1 | `Nat.prod_pow_factorization_choose` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 267 (S12 PREP) | 267 (gh api at SHA) | 0 |
| 2 | `Nat.pow_factorization_choose_le` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 196 (S12 PREP) | 196 (gh api at SHA) | 0 |
| 3 | `Nat.factorization_eq_zero_of_not_prime` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 129 (S14 §4.2) | 129 (gh api at SHA) | 0 |
| 4 | `Nat.coprime_iff_isRelPrime` | `Mathlib/Data/Nat/GCD/Basic.lean` | 218 (S14 §4.1) | 218 (gh api at SHA) | 0 |
| 5 | `Nat.coprime_pow_primes` | `Mathlib/Data/Nat/Prime/Basic.lean` | 200 (S15 §4.1) | 200 (gh api at SHA) | 0 |
| 6 | `Finset.prod_dvd_of_isRelPrime` | `Mathlib/RingTheory/Coprime/Lemmas.lean` | 252 (S13 §2.4) | 252 (gh api at SHA) | 0 |
| 7 | `isRelPrime_one_left` | `Mathlib/Algebra/Divisibility/Units.lean` | 166 (S14 §5) | 166 (gh api at SHA) | 0 |
| 8 | `isRelPrime_one_right` | `Mathlib/Algebra/Divisibility/Units.lean` | 167 (S15 §4.2) | 167 (gh api at SHA) | 0 |
| 9 | `DecompositionMonoid` via `[Nonempty (GCDMonoid α)]` | `Mathlib/Algebra/GCDMonoid/Basic.lean` | 493 (S13 §2.5) | 493 (gh api at SHA) | 0 |

**Recheck protocol** (used per bearer; result: bytewise-identical signature blocks for all 9):

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
URL=$(gh api "repos/leanprover-community/mathlib4/contents/<path>?ref=${SHA}" -q '.download_url')
curl -sL "$URL" | sed -n '<line-1>,<line+5>p'
```

**Section-header typeclass recheck** for the bearers used inside the S15 ACT's `choose_dvd_lcmRange` proof body (per memory pattern):
- `Nat.coprime_pow_primes` (#5): inside `namespace Nat`, no `variable [...]` overhead; `(n m : ℕ) (pp : Prime p) (pq : Prime q) (h : p ≠ q)` is the full signature.
- `Finset.prod_dvd_of_isRelPrime` (#6): inside `namespace Finset` in `Mathlib/RingTheory/Coprime/Lemmas.lean` at SHA-pinned line 252; requires `[CommMonoidWithZero α]` AND `[DecompositionMonoid α]` typeclasses on `α`. For `α = ℕ`: `CommMonoidWithZero ℕ` is in Mathlib via the `CommSemiring ℕ` instance chain (auto), and `DecompositionMonoid ℕ` is satisfied via the `[Nonempty (GCDMonoid α)]` instance at #9 (with `Nat.instGCDMonoid` providing the witness). Both transitively imported via the slug's existing `import Mathlib.Algebra.GCDMonoid.Finset`.

### §3 Four new bearer pins for S16/S17 ACT

#### §3.1 `Nat.factorization_mul`

**Pin**: `Mathlib/Data/Nat/Factorization/Defs.lean:155`.

**Signature** (verified at lake SHA via `gh api` + `curl`):

```lean
theorem factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization = a.factorization + b.factorization
```

**Why needed**: lifting `v_p(m · C(n, m)) = v_p(m) + v_p(C(n, m))` is the foundational decomposition for Routes A, B, and C of S17 ACT. Without it, every per-prime bound has to be re-derived from `padicValNat`. Note: this is a **Finsupp equality** (the LHS and RHS are `n →₀ ℕ` functions); to access the `p`-th coordinate, apply `Finsupp.add_apply` or `coe_add` + `Pi.add_apply`. Per S14's reference pattern, the slug already imports `Mathlib.Data.Nat.Choose.Factorization` (S15 import), which transitively pulls in `Mathlib.Data.Nat.Factorization.Defs`, so `Nat.factorization_mul` is in scope without additional imports.

**In scope after**: existing S15 import `Mathlib.Data.Nat.Choose.Factorization` (which imports `.Factorization.Defs` transitively).

#### §3.2 `Nat.factorization_le_factorization_choose_add`

**Pin**: `Mathlib/Data/Nat/Choose/Factorization.lean:142`.

**Signature** (verified at lake SHA):

```lean
theorem factorization_le_factorization_choose_add {p : ℕ} :
    ∀ {n k : ℕ}, k ≤ n → k ≠ 0 →
      n.factorization p ≤ (choose n k).factorization p + k.factorization p
```

**Why needed**: this is the **Kummer corollary** stating `v_p(n) ≤ v_p(C(n, k)) + v_p(k)`, equivalent to `n ∣ k · C(n, k)` (already proved in the slug as `dvd_mul_choose` at line 380 via `mul_choose_eq_mul_choose_pred`). It is **NOT** the bound we need for `m · C(n, m) ∣ lcmRange n` — that requires the *upper* bound `v_p(k · C(n, k)) ≤ log_p n`, which is the harder direction. However, this Mathlib lemma is **load-bearing for Route A** as a stepping stone (combined with Kummer's emultiplicity_choose to derive the upper bound from a lower bound + the Legendre identity).

**In scope after**: existing S15 import `Mathlib.Data.Nat.Choose.Factorization`.

#### §3.3 `Nat.multiplicity_eq_factorization` (bridge multiplicity ↔ factorization)

**Pin**: `Mathlib/Data/Nat/Factorization/Defs.lean:89`.

**Signature** (verified at lake SHA):

```lean
theorem multiplicity_eq_factorization {n p : ℕ} (pp : p.Prime) (hn : n ≠ 0) :
    multiplicity p n = n.factorization p
```

**Why needed**: the Kummer/Legendre bearers (`Nat.Prime.emultiplicity_choose` at Multiplicity.lean:209 and `Nat.Prime.emultiplicity_factorial` at Multiplicity.lean:102, both pinned by S13 §5) deal with the **ℕ∞-valued** `emultiplicity`. To use the per-prime bound `v_p(m · C(n, m)) ≤ log_p n` inside the prime-power decomposition framework (S15's `Nat.pow_factorization_choose_le` style), we need to convert to the **ℕ-valued** `factorization`. The two-step bridge is:

```
emultiplicity p (m * C(n, m)) ─→ multiplicity p (m * C(n, m)) ─→ (m * C(n, m)).factorization p
              (via #4 below)                       (via this bearer)
```

The conversion `emultiplicity → multiplicity` requires the multiplicity to be **finite** (i.e., `emultiplicity ≠ ⊤`), which holds whenever the input is nonzero (a standard Mathlib lemma).

**In scope after**: existing S15 import `Mathlib.Data.Nat.Choose.Factorization` (transitively pulls in `.Factorization.Defs`).

#### §3.4 `multiplicity_eq_of_emultiplicity_eq_some` (bridge emultiplicity → multiplicity)

**Pin**: `Mathlib/RingTheory/Multiplicity.lean:73`.

**Signature** (verified at lake SHA):

```lean
theorem multiplicity_eq_of_emultiplicity_eq_some {n : ℕ} (h : emultiplicity a b = n) :
    multiplicity a b = n
```

**Why needed**: completes the `emultiplicity → multiplicity` bridge from §3.3. Given that Kummer's theorem gives `emultiplicity p (C(n, k)) = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}` (a finite cardinality, packaged as `ℕ∞` via `WithTop ℕ`'s `(↑·)` coercion), we extract the `ℕ`-value via this lemma.

**In scope after**: NEW import required for Route A: `Mathlib.Data.Nat.Multiplicity` (which imports `Mathlib.RingTheory.Multiplicity` transitively). The slug currently does NOT import `Mathlib.Data.Nat.Multiplicity` directly — it must be added at S17 ACT time.

**Caveat**: this bearer is a `multiplicity` (universal-over-monoid) lemma, not a `Nat.Prime`-namespaced one. The full route requires composing this with `Nat.Prime.emultiplicity_choose` (which gives the equation `emultiplicity p (C(n, k)) = ↑(card ...)`), then applying this bridge to extract the `ℕ`-valued `multiplicity`, then applying §3.3 to get `factorization`. ~3 lemma applications in sequence.

### §4 `Nat.succ_mul_choose_eq` DEPRECATION (2025-12-09)

The deprecation banner in Mathlib `Mathlib/Data/Nat/Choose/Basic.lean:137-139` (verified at lake SHA):

```lean
@[deprecated add_one_mul_choose_eq (since := "2025-12-09")]
theorem succ_mul_choose_eq : ∀ n k, succ n * choose n k = choose (succ n) (succ k) * succ k :=
  add_one_mul_choose_eq
```

The replacement `Nat.add_one_mul_choose_eq` (line 128) has the equivalent signature:

```lean
theorem add_one_mul_choose_eq : ∀ n k, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)
```

**Slug usage audit** (current HEAD, `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`):

| Line | Reference | Status |
|------|-----------|--------|
| 121 | docstring of `mul_choose_eq_mul_choose_pred` | informational — mentions "Nat.succ_mul_choose_eq" in passing |
| 344 | comment in Part 5 ACT preamble | informational — mentions "Mathlib's `Nat.succ_mul_choose_eq`" |
| 367 | actual proof line of `mul_choose_eq_mul_choose_pred` | **uses `Nat.add_one_mul_choose_eq`** — NEW NAME |

**Conclusion**: the slug's proof body already uses the non-deprecated name. The deprecation **does NOT trigger any v4.26.0 build warning or error** in this slug. The two docstring references at lines 121 and 344 are purely informational/historical commentary. **No fix needed** in S17 ACT; flag for the next slug-wide hermit/doctor sweep if the deprecation banner eventually becomes hard-removed (estimated ~6 months).

### §5 Three viable routes for `mul_choose_dvd_lcmRange`

#### §5.1 Route A — Full Kummer via emultiplicity bridge (paste-ready bearer set)

**Idea**: prove `v_p(m · C(n, m)) ≤ log_p n` directly via Kummer's theorem on `C(n, m)` plus arithmetic on digit sums.

**Step 1** (Kummer for `v_p(C(n, m))`): by §3.4 + §3.3, derive `(C(n, m)).factorization p ≤ log_p n`. This is essentially S15's `Nat.pow_factorization_choose_le` re-derived from first principles, but expressed in `factorization` form rather than `pow ≤`.

**Step 2** (per-prime carry-count argument): by Kummer + Legendre, `v_p(C(n, m)) + v_p(m) = #{carries in m + (n-m) base p} + v_p(m)`. The carry-count is bounded by `log_p n - v_p(m)` because the bottom `v_p(m)` digits of m are 0, so carries can only happen in positions above `v_p(m)`. This is the **sharp** bound.

**Step 3** (lift to factorization): apply §3.2's lower bound + §3.1's additivity.

**Step 4** (S15-framework prime-power decomposition): use `Nat.prod_pow_factorization_choose` analogue for `m · C(n, m)` (extending the S15 strategy from C(n,k) to m·C(n,k)).

**Pros**: closest to mathematical truth; no auxiliary slug-level identities needed; bearer set is fully Mathlib-native.

**Cons**: ~100-150 LOC; requires reasoning about base-p digit sums and Kummer carry positions (intricate Lean tactics); ~3-4 Docker iters likely; new import `Mathlib.Data.Nat.Multiplicity` required.

#### §5.2 Route B — Hybrid identity-then-prime-power-decomp

**Idea**: use the slug's existing `mul_choose_eq_mul_choose_pred` (Part 5 ACT, line 364) to rewrite `m · C(n, m) = n · C(n-1, m-1)`. Then prove `n · C(n-1, m-1) ∣ lcmRange n` via prime-power decomposition.

**Per-prime bound needed**: `v_p(n) + v_p(C(n-1, m-1)) ≤ log_p n`. This is sharper than the trivial `v_p(n) ≤ log_p n` + `v_p(C(n-1, m-1)) ≤ log_p(n-1)` (which gives `≤ 2 log_p n`).

**Why sharp**: when `v_p(n) = a`, then `n` in base p ends with `a` zeros, so `n - 1` in base p ends with `a` copies of `(p-1)`. The carries when computing `(m-1) + ((n-1)-(m-1)) = (n-1)` in base p can only happen in positions where both summands have non-zero digits, but the bottom `a` digits of `(n-1)` are `(p-1)` (no carry needed at those positions because `(p-1) + 0 = (p-1)` with no carry; or `(p-1) - x + x = (p-1)`). So at most `log_p n - a` carries above the bottom-`a` block. By Kummer, `v_p(C(n-1, m-1)) ≤ log_p n - a = log_p n - v_p(n)`. Combined: `v_p(n) + v_p(C(n-1, m-1)) ≤ log_p n`. QED.

**Pros**: leverages slug's existing infrastructure; the identity `mul_choose_eq_mul_choose_pred` is already proven; one-step rewrite at the goal level then reduce to prime-power decomp.

**Cons**: still requires the sharp per-prime bound (~80-100 LOC of base-p digit reasoning); the bound proof is essentially Route A in disguise; the identity rewrite adds 5-10 LOC of housekeeping (off-by-one indexing on `n-1`, `m-1`).

#### §5.3 Route C — S15-framework extension with sharper per-prime lemma (RECOMMENDED, split S17a + S17b)

**Idea**: split S17 ACT into two manageable Lean-modifying sub-iterations:

* **S17a ACT (~60-80 LOC)**: prove the per-prime upper bound as a standalone lemma:

```lean
theorem pow_factorization_mul_choose_le {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {p : ℕ} :
    p ^ ((m * Nat.choose n m).factorization p) ≤ n
```

  using `Nat.factorization_mul` (§3.1) + Kummer (§3.3 + §3.4 bridge) + arithmetic on `log p n`.

* **S17b ACT (~30-40 LOC)**: lift via S15's prime-power decomposition framework (using `Finset.prod_dvd_of_isRelPrime` + `Nat.prod_pow_factorization_choose` adapted for `m * C(n, m)`):

```lean
theorem mul_choose_dvd_lcmRange {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m * Nat.choose n m ∣ lcmRange n
```

**Pros**: each sub-iteration is **independently Docker-verifiable** in a single PR; the per-prime bound (S17a) is a useful standalone lemma (analogue of `Nat.pow_factorization_choose_le` for `m · C(n, m)`); S17b's structure mirrors S15's `choose_dvd_lcmRange` proof almost verbatim (just substitute `m * C(n, m)` for `C(n, m)` and apply S17a in place of `Nat.pow_factorization_choose_le`).

**Cons**: two PRs instead of one; the splitting adds ~10 LOC of glue (S17b's signature must accept S17a's lemma as a black-box rather than inlining the bound proof).

**RECOMMENDATION**: **Route C with split S17a + S17b**. Rationale:
1. Smaller Docker-verifiable PRs reduce ACT-time risk per memory pattern `feedback_researcher_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open` (budget 1-2 elaboration fixes per ACT vs 3-5 for monolithic 100+ LOC ACTs).
2. S17a's `pow_factorization_mul_choose_le` is **useful standalone** — it generalizes S15's `pow_factorization_choose_le`-derived bound and can be reused for vdP §6 application (S18+ ACT) on the alternating-bilinear summand's `C(n+m, m)` factor (which has form `q · C(N, m)` for `q = n + m, N = n + m`).
3. S17b's structure is a **mechanical copy** of S15's proof body (LOC ratio ~1:1 modulo per-prime call substitution), making it a low-risk ship.

### §6 Naive-route counterexample (S13 §5.1 re-validation, self-contained)

The S13 §5.1 claim that "the naive bound `v_p(m) + ⌊log_p(n-1)⌋ ≤ ⌊log_p n⌋` is FALSE" is best illustrated by a different counterexample than the one S13 cited (which actually holds in the n=4, m=2, p=2 case — see numerical check below).

**S13 §5.1 candidate (n=4, m=2, p=2)** — let me re-check:
- `v_p(m) = v_2(2) = 1`
- `⌊log_p(n-1)⌋ = ⌊log_2 3⌋ = 1` (since `2^1 = 2 ≤ 3 < 4 = 2^2`)
- `v_p(m) + ⌊log_p(n-1)⌋ = 2`
- `⌊log_p n⌋ = ⌊log_2 4⌋ = 2`
- `2 ≤ 2` — naive bound **holds tightly** at this point.

**Sharper counterexample (n=12, m=4, p=2)**:
- `v_p(m) = v_2(4) = 2`
- `⌊log_p(n-1)⌋ = ⌊log_2 11⌋ = 3` (since `2^3 = 8 ≤ 11 < 16 = 2^4`)
- `v_p(m) + ⌊log_p(n-1)⌋ = 5`
- `⌊log_p n⌋ = ⌊log_2 12⌋ = 3`
- `5 > 3` — **naive bound FAILS by 2 units**.

But the actual `v_p(m · C(n, m))` for this case:
- `C(12, 4) = 495`. `v_2(495) = 0` (495 = 3^2 · 5 · 11, odd).
- `v_p(m · C(n, m)) = v_2(4 · 495) = v_2(1980) = 2` (since `1980 = 4 · 495`).
- `⌊log_p n⌋ = 3`.
- `2 ≤ 3` — **sharp bound holds**.

So the naive bound IS strictly too pessimistic — the actual bound `v_p(m · C(n, m)) ≤ ⌊log_p n⌋` holds (and is the right target), but the **sum of independent factor bounds** is too loose. The correct path requires the Kummer-carries observation: when `v_p(m) = a`, the bottom `a` digits of m are 0, forcing carries in the addition `m + (n-m) = n` to land only in positions > a, hence `v_p(C(n, m)) ≤ ⌊log_p n⌋ - v_p(m)`.

This counterexample should be documented at the S17a proof site as a comment, motivating why the standalone Mathlib bound `Nat.pow_factorization_choose_le` (which gives `v_p(C(n, m)) ≤ log_p n`) is **not** directly sufficient and the sharper carry-count argument is needed.

### §7 S17a ACT skeleton (paste-ready, Route C sub-step a)

The skeleton below uses bearers §3.1-§3.4 + existing S14/S15 pins. It is a Lean 4 sketch with `sorry`-stubs in the carry-count arithmetic block (~10 LOC out of ~70) to be filled by S17a ACT:

```lean
section Part12
-- (Part 12, Session 17a) Per-prime bound for m · C(n, m): the prime-power
-- factorization of `m * C(n, m)` is bounded by `log_p n`, generalizing
-- `Nat.pow_factorization_choose_le` (S15) to the m-prefactored case.
-- Used by Part 12b (S17b ACT) to discharge `mul_choose_dvd_lcmRange`.

import Mathlib.Data.Nat.Multiplicity   -- NEW (S17a): Nat.Prime.emultiplicity_choose, .emultiplicity_factorial

/-- Per-prime upper bound on `(m * C(n, m)).factorization p`: equals
    `m.factorization p + (C(n, m)).factorization p` by `factorization_mul`,
    and is bounded by `⌊log_p n⌋` via the Kummer carry-count argument.

    The naive bound `v_p(m) + log_p(n-1) ≤ log_p n` FAILS in general (e.g.
    n=12, m=4, p=2: v_2(4) + log_2(11) = 2 + 3 = 5 > log_2(12) = 3).
    The sharp argument uses that `v_p(m) = a` forces the bottom `a` base-p
    digits of m to be 0, so carries in `m + (n-m) = n` (which by Kummer
    counts `v_p(C(n, m))`) can only land in positions > a, giving
    `v_p(C(n, m)) ≤ log_p n - v_p(m)`. -/
theorem pow_factorization_mul_choose_le {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {p : ℕ} :
    p ^ ((m * Nat.choose n m).factorization p) ≤ n := by
  by_cases hp : p.Prime
  case neg =>
    -- Non-prime p ⇒ factorization is 0 by Nat.factorization_eq_zero_of_not_prime.
    rw [Nat.factorization_mul hm.ne' (Nat.choose_pos hmn).ne']
    simp only [Finsupp.add_apply, Pi.add_apply]
    rw [Nat.factorization_eq_zero_of_not_prime _ hp,
        Nat.factorization_eq_zero_of_not_prime _ hp]
    simp
    exact hmn.trans (le_refl n) |>.trans' (Nat.one_le_iff_ne_zero.mpr hm.ne')  -- 1 ≤ n
  case pos =>
    -- Prime p case: use Kummer + Legendre on emultiplicity, then bridge to factorization.
    -- v_p(m * C(n, m)) = v_p(m) + v_p(C(n, m)) (by factorization_mul)
    rw [Nat.factorization_mul hm.ne' (Nat.choose_pos hmn).ne']
    simp only [Finsupp.add_apply, Pi.add_apply]
    -- Goal: p ^ (v_p(m) + v_p(C(n, m))) ≤ n
    -- Equivalently: v_p(m) + v_p(C(n, m)) ≤ log_p n
    sorry -- carry-count argument here (10-15 LOC, S17a ACT will fill in)
end Part12
```

**LOC budget**: ~60-80 (~50-60 for proof body + ~15-25 for docstring + Part header).

**Bearer budget**: 5 (4 new + 1 existing reuse):
- §3.1 `Nat.factorization_mul` ← 2 uses
- §3.2 `Nat.factorization_le_factorization_choose_add` ← 0-1 uses (depending on carry-count formulation)
- §3.3 `Nat.multiplicity_eq_factorization` ← 1 use
- §3.4 `multiplicity_eq_of_emultiplicity_eq_some` ← 1 use
- S13's `Nat.Prime.emultiplicity_choose` at Multiplicity.lean:209 ← 1 use (Kummer)

### §8 S17b ACT skeleton (Route C sub-step b)

After S17a ships, the lift to `mul_choose_dvd_lcmRange` is a near-verbatim copy of S15's `choose_dvd_lcmRange` proof body, substituting `m * C(n, m)` for `C(n, m)` and using S17a's `pow_factorization_mul_choose_le` in place of S15's `Nat.pow_factorization_choose_le`:

```lean
section Part13
-- (Part 13, Session 17b) m * C(n, m) ∣ lcmRange n via prime-power decomposition
-- + S17a's per-prime bound. Generalizes S15's `choose_dvd_lcmRange`.

/-- **m · C(n, m) ∣ lcmRange n**: the central divisibility input to the
    alternating-bilinear summand discharge in vdP §6 (parent file's
    `denominator_control`). Generalizes S15's `choose_dvd_lcmRange`. -/
theorem mul_choose_dvd_lcmRange {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m * Nat.choose n m ∣ lcmRange n := by
  have hMC_pos : 0 < m * Nat.choose n m := Nat.mul_pos hm (Nat.choose_pos hmn)
  rw [← Nat.factorization_prod_pow_eq_self hMC_pos.ne']
  apply Finset.prod_dvd_of_isRelPrime
  · -- Pairwise IsRelPrime: structurally identical to S15 §1.
    sorry -- copy from S15 lines 866-890, substituting `m * C(n, m)` for `C(n, m)`
  · -- Per-prime-power divisibility: use S17a in place of pow_factorization_choose_le.
    intro p _
    by_cases hv : (m * Nat.choose n m).factorization p = 0
    · rw [hv, pow_zero]; exact one_dvd _
    have hpp : p.Prime := by
      by_contra h; exact hv (Nat.factorization_eq_zero_of_not_prime _ h)
    have hpow_pos : 0 < p ^ (m * Nat.choose n m).factorization p :=
      pow_pos hpp.pos _
    have hpow_le : p ^ (m * Nat.choose n m).factorization p ≤ n :=
      pow_factorization_mul_choose_le hm hmn  -- ← S17a bearer
    exact dvd_lcmRange hpow_pos hpow_le
end Part13
```

**LOC budget**: ~30-40 (~25-30 for proof body + ~5-10 for docstring + Part header).

**Bearer budget**: re-use all 9 S15 §4 bearers + S17a's new theorem (consumed as a black box).

### §9 S17 readiness gate

For Route C sub-step a (S17a ACT):

| Item | Status | Notes |
|------|--------|-------|
| `Nat.prod_pow_factorization_choose` bearer pinned | ✓ | S12 + S13 |
| `Nat.pow_factorization_choose_le` bearer pinned | ✓ | S12 + S13 (used in S15; consumed by S17b not S17a) |
| `Nat.factorization_mul` bearer pinned | ✓ | **NEW this S16 §3.1** |
| `Nat.factorization_le_factorization_choose_add` bearer pinned | ✓ | **NEW this S16 §3.2** |
| `Nat.factorization_eq_zero_of_not_prime` bearer pinned | ✓ | S14 §4.2 |
| `Nat.Prime.emultiplicity_choose` (Kummer) bearer pinned | ✓ | S13 §5 |
| `Nat.Prime.emultiplicity_factorial` (Legendre) bearer pinned | ✓ | S13 §5 |
| `Nat.multiplicity_eq_factorization` (bridge) bearer pinned | ✓ | **NEW this S16 §3.3** |
| `multiplicity_eq_of_emultiplicity_eq_some` (bridge) bearer pinned | ✓ | **NEW this S16 §3.4** |
| Lake SHA stable (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) | ✓ | S14 §3, 0 drift this S16 §2 |
| `Mathlib.Data.Nat.Multiplicity` import status | ⚠ | **NEW import needed at S17a ACT** (not yet in slug) |
| Slug build clean at HEAD | ✓ | S15 ACT verified clean (3058 jobs) |

For Route C sub-step b (S17b ACT): all S15 §4 bearers re-used + S17a's `pow_factorization_mul_choose_le` consumed as a black-box. **9/9 GREEN at S17b time once S17a merges**.

**Gate status**: **GREEN for S17a ACT** at this S16 PREP close. The ⚠ on the new import is a one-line addition (no bearer-pin work needed; `Mathlib.Data.Nat.Multiplicity` is a standard Mathlib file used elsewhere in the gallery).

### §10 Conflict-free assertions

This S16 PREP modifies exactly three files:

1. **NEW**: this session note `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-16-s16-prep-mul-choose-dvd-lcm-range-bearer-pin-and-route-audit.md`.
2. **MODIFIED**: `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/state.md` — prepend "Session 16 PREP" section near the top (above the existing Session 15 ACT section).
3. **MODIFIED**: `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02.json` — refresh `currentState.iteration` (15 → 16), `currentState.since`, `currentState.focus`, `currentState.nextAction`, `lastUpdate`; prepend 2 entries to `knowledge.insights` and 2 entries to `knowledge.nextSteps`.

**0 Lean edits**. **0 sibling-slug edits**.

#### §10.1 Open-PR conflict surface (this slug)

At S16 PREP write-time: 0 open PRs on this exact slug (the 2 open PRs `#17619`, `#17551` are for the sibling slug `-oq-03`, last component `oq-03`, not `oq-02`; they touch a different Lean file, `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`).

#### §10.2 Open-PR conflict surface (other slugs touching JSON or Lean)

The JSON and Lean files are owned by this slug only. No other slug's PRs touch them. The slug's parent file `Proofs/BaselProblemOQ01OQ01OQ02.lean` (which contains the `denominator_control` axiom this slug is discharging) is not modified by this PREP.

### §11 Falsifiability

This S16 PREP is falsifiable along three axes:

1. **Bearer surface (§2 + §3)**: if any of the 13 pin commands returns a different signature or line number than this report claims at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the bearer surface is wrong and S17a ACT must repair the pin before consuming.
2. **Route C strategy (§5.3 + §7-§8)**: if S17a ACT discovers that the per-prime upper bound `pow_factorization_mul_choose_le` requires a Mathlib API that doesn't exist at lake SHA, the route must be re-audited. Specifically: if the Kummer carry-count argument cannot be formalized in ≤80 LOC, fall back to Route A (full emultiplicity bridge, ~100-150 LOC monolith) or Route B (hybrid via `mul_choose_eq_mul_choose_pred`, ~80-100 LOC monolith).
3. **Naive counterexample (§6)**: if n=12, m=4, p=2 does NOT actually witness `v_p(m) + ⌊log_p(n-1)⌋ > ⌊log_p n⌋`, the claim that the naive bound fails is wrong and the motivation for the sharper bound must be re-derived. Numerical check: `v_2(4)=2, log_2(11)=3, log_2(12)=3, 2+3=5 > 3` — claim verified.

### §12 Memory pattern alignment

This PREP iteration matches:

- `feedback_researcher_postship_pivot_lands_on_own_recent_prep_with_no_deferred_pencilwork.md` (inverse) — exactly: S15 ACT (PR #19397) merged ~20 min before claim AND nextAction explicitly named bridge bearer as deferred pencilwork ("Needs ONE additional bridge bearer pinned at S16 ACT time: Nat.Prime.emultiplicity_eq_factorization (or similar)"). PREP discharges the deferred pencilwork before S17 ACT fires, matching the pattern's prescription to NOT execute the ACT when pencilwork is outstanding.
- `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md` — exactly: §2's recheck table verifies all 9 existing bearers AND §3 documents typeclass dependencies for the 4 new bearers (specifically §3.4's `multiplicity_eq_of_emultiplicity_eq_some` requires `Mathlib.RingTheory.Multiplicity` import not in slug; §3.3's `Nat.multiplicity_eq_factorization` requires `(pp : p.Prime)` typeclass argument).

### §13 Session metrics

| Metric | Value |
|--------|-------|
| Mode | PREP (doc-only) |
| New files | 1 (this session note) |
| Modified files | 2 (state.md, JSON) |
| Lean LOC delta | 0 |
| Theorem delta | 0 |
| Sorry delta | 0 |
| Axiom delta | 0 |
| New bearer pins | 4 (`factorization_mul`, `factorization_le_factorization_choose_add`, `multiplicity_eq_factorization`, `multiplicity_eq_of_emultiplicity_eq_some`) |
| Bearer drift recheck | 9 bearers, 0 drift at unchanged lake SHA |
| Deprecation notes | 1 (`Nat.succ_mul_choose_eq` → `Nat.add_one_mul_choose_eq`; slug already uses new name) |
| Routes audited | 3 (A: full Kummer; B: hybrid identity; C: split S17a + S17b) |
| Recommended route | **Route C (split)** — S17a per-prime bound + S17b S15-framework lift |
| ACT-readiness gate | **GREEN for S17a** (10/11 items, 1 ⚠ on new import for `Mathlib.Data.Nat.Multiplicity`) |

**Axiom delta this session**: 0 (doc-only).
