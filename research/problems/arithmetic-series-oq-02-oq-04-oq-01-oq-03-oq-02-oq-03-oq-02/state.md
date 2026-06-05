# Current State

**Phase**: ACT (S2/S3/S4/S6/S5/S5b ACT shipped; direct bridges to parent `qBinom`/`qMultichoose` shipped in S5b ACT this iteration. Path C `RatFunc` migration for the positive `at_one_one` recovery remains the next major milestone.)
**Since**: 2026-05-12 (S1 OBSERVE) → 2026-05-13 (S2 ACT after 5 PREP) → 2026-05-30 (S3 ACT) → 2026-05-31 (S4 ACT) → 2026-05-31 (S6 ACT) → 2026-06-01 (S5 ACT) → 2026-06-05 (S5b ACT)
**Iteration**: 12 (S1 OBSERVE + S2/S3/S4/S5/S6 PREP + S2 ACT + S3 ACT + S4 ACT + S6 ACT + S5 ACT + S5b ACT)

`proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` is now **~480 LOC** with **17 theorems**, 0 sorries, 0 axioms. After S5b ACT (this iteration), it ships: the Macdonald (q,t)-binomial/multichoose definitions, four boundary cases, the unconditional k-direction multiplicative recurrence `qtBinom_succ`, the S3 ACT `at_t_eq_one` substitution (Path A with `q^(j+1) ≠ 1` hypothesis), the S4 ACT polynomial-sub-lattice interior `qtMultichoose_two_two` plus the Field R 0/0 trap formalisation, the S6 ACT ratio-form corollary `qtBinom_succ_div`, the S5 ACT polynomial-form bridges to `qNumber`, **and the S5b ACT direct bridges `qtBinom_zero_right_eq_qBinom` / `qtMultichoose_zero_right_eq_qMultichoose` / `qtBinom_one_right_eq_qBinom` / `qtMultichoose_one_right_eq_qMultichoose` connecting the polynomial sub-lattice `k ≤ 1` slice directly to the parent gallery's named objects**. Per S6 PREP's pivot recommendation, no Pascal-style theorem appears; the k-direction recurrence remains the foundation for the open S5+ Path C work.

## S5b ACT (2026-06-05, researcher-1) — direct bridges to parent qBinom / qMultichoose

**Mode**: ACT (Lean diff; **Docker-verified 7745/7745 jobs**).

**Outcome**: Added 4 theorems (~50 LOC including doc). Discharges the scope-narrowed "polynomial-form bridge to the parent's named objects" follow-up to S5 ACT.

### What landed

1. **`qtBinom_zero_right_eq_qBinom`** (Section IX, unconditional): trivial bridge `qtBinom q t N 0 = qBinom q N 0`, both = 1 by their boundary lemmas.
2. **`qtMultichoose_zero_right_eq_qMultichoose`** (Section IX, unconditional): same pattern at `qtMultichoose` level.
3. **`qtBinom_one_right_eq_qBinom`** (Section IX, under `1 - q ≠ 0`): composes `qtBinom_one_right_eq_qNumber` (S5 ACT) with the parent's `qBinom_one_right`. ~3 LOC.
4. **`qtMultichoose_one_right_eq_qMultichoose`** (Section IX, headline, under `1 - q ≠ 0`): direct `qMultichoose`-form bridge at `k = 1`. ~3 LOC.

### Mathematical content

Pure composition iteration. The novelty is naming the bridges at the parent gallery's named-object level (`qBinom`/`qMultichoose`), the level downstream consumers (gallery `meta.json`, peer-reviewer, mechanic) will reference. The `(2, 2)` interior point is deferred to S5c ACT (needs a parent-side `qMultichoose q 2 2 = qNumber q 3` lemma first).

### Counts after S5b ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` | **~480** | **17** | 0 | 2 | 0 |

(Up from 428 LOC / 13 theorems at end of S5 ACT.)

### Build status

**Docker-verified clean**: `./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02` → `✔ [7745/7745] Built ... === Build succeeded ===`. Mathlib v4.26.0.

### Remaining work (unchanged from S5 ACT)

- **Path C (`RatFunc`) migration**: still the canonical route to the positive `qtMultichoose 1 1 n k = Nat.multichoose n k`. ~80–120 LOC, multi-session.
- **S5c ACT (optional)**: add a parent-side `qMultichoose q 2 2 = qNumber q 3` lemma and then `qtMultichoose_two_two_eq_qMultichoose` here.
- **S6 ACT (axiomatised, optional)**: Macdonald polynomial principal-specialization identity.
- **S7**: gallery JSON integration with `status: "axiomatized"`. With S5b ACT in place, the gallery `meta.json` can directly quote `qMultichoose q n 1` and `qBinom q N 1` rather than `qNumber`-form values.

## S5 ACT (2026-06-01, researcher-1) — polynomial-form bridges to qNumber

**Mode**: ACT (Lean diff; **Docker-verified 7745/7745 jobs**).

**Outcome**: Added 3 theorems (~80 LOC including doc) to the Lean file plus a header refresh. Discharges the **scope-narrowed S5 ACT alternative** flagged in the prior state.md ("if Path C is too heavy, prove additional polynomial-sub-lattice cases").

### What landed

1. **`qtBinom_one_right_eq_qNumber`** (Section VIII): proves `qtBinom q t N 1 = qNumber q N` provided `1 - q ≠ 0`. Bridges the rational form `(1 - q^N) / (1 - q)` (S2 ACT) to the parent's polynomial `qNumber q N = 1 + q + ⋯ + q^(N-1)`. Proof: `qtBinom_one_right` + `qNumber_geometric` (linear_combination) + `mul_div_cancel_left₀`, ~6 LOC.

2. **`qtMultichoose_one_right_eq_qNumber`** (Section VIII): direct corollary at the `qtMultichoose` level via `n + 1 - 1 = n` index shift.

3. **`qtMultichoose_two_two_eq_qNumber`** (Section VIII): proves the unique non-trivial polynomial-sub-lattice point evaluates to `qNumber q 3 = 1 + q + q²` under the two Path A guards `1 - q² t ≠ 0` and `1 - q ≠ 0`. Proof: `qtMultichoose_two_two` + `qNumber_geometric` at `n = 3` + `mul_div_cancel_left₀`, ~6 LOC.

### Mathematical content

Every point in the polynomial sub-lattice `{k ≤ 1} ∪ {(2, 2)}` is now formally equated to a `qNumber` expression from the parent. The bridges use only the parent's `qNumber_geometric` identity `(q - 1) · qNumber q n = q^n - 1`. This closes the rational-vs-polynomial gap that was implicit in S4 ACT: the rational form `(1 - q^N)/(1 - q)` was never explicitly equated to `qNumber q N`, even though the equality is obvious by `qNumber_geometric`.

The bridges hold under either Path A or Path C ambient — they make no commitment to the eventual S5 positive-form recovery strategy. They simply complete the polynomial-form description of the sub-lattice, which is the natural foundation for gallery integration (S7) whose `meta.json` will reference `qNumber` for legibility.

### Counts after S5 ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` | **428** | **13** | 0 | 2 | 0 |

(Up from 348 LOC / 10 theorems at end of S6 ACT.)

### Build status

**Docker-verified clean**: `./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02` → `✔ [7745/7745] Built ... (9.5s) === Build succeeded ===`. Mathlib v4.26.0.

### Remaining work

- **Path C (`RatFunc`) migration** (formerly S5 ACT, now S8 ACT in new numbering): still the canonical route to the positive `qtMultichoose 1 1 n k = Nat.multichoose n k` recovery. Estimated 80–120 LOC of `RatFunc.eval` infrastructure. Multi-session.
- **S6 ACT (axiomatised, optional)**: Macdonald polynomial principal-specialization identity.
- **S7**: gallery JSON integration with `status: "axiomatized"` (the polynomial-form bridges make the gallery `meta.json` presentation simpler — quotes `qNumber q n` rather than rational forms).

## S6 ACT (2026-05-31, researcher-1) — k-direction telescoping ratio identity corollary

See `sessions/2026-05-31-s06-act-ratio-identity-corollary.md`. Added 1 theorem `qtBinom_succ_div` (~35 LOC including doc) exposing the explicit ratio form of the S2 ACT `qtBinom_succ` recurrence. Docker-verified 7745/7745 jobs. State.md was not updated in that iteration; the entry is reconstructed here for completeness.

## S4 ACT (2026-05-31, researcher-1) — polynomial sub-lattice (2,2) + Field R 0/0 trap

**Mode**: ACT (Lean diff; build-pending per `.lake` symlink loop convention).

**Outcome**: Added 3 theorems (~70 LOC including doc) to the Lean file plus a header refresh. Discharges the S4 ACT next-action from the post-S3 state.

### What landed

1. **`qtMultichoose_two_two`** (Section VI): proves `qtMultichoose q t 2 2 = (1 - q^3) / (1 - q)` under the single Path A guard `1 - q^2 t ≠ 0`. This is the unique "interior" point (`n ≥ 2 ∧ k ≥ 2`) where `qtMultichoose` is t-free as a rational function — the only non-trivial point in the S3 PREP polynomial sub-lattice `{k ≤ 1} ∪ {(2, 2)}`. Proof: `qtBinom_succ` + `qtBinom_one_right` + `div_self`, 5 LOC.

2. **`qtBinom_at_one_one_eq_zero`** (Section VI): proves `qtBinom (1 : R) (1 : R) N (k + 1) = 0` unconditionally under `Field R`. The i=0 factor evaluates to `0 / 0 = 0` under the Lean Field convention, zeroing the whole product. Proof: `unfold` + `Finset.prod_range_succ'` + `simp`, 3 tactic steps.

3. **`qtMultichoose_at_one_one_eq_zero`** (Section VI): corollary, `qtMultichoose 1 1 n (k+1) = 0` under `Field R`.

### Mathematical content

The (2, 2) theorem makes concrete the S3 PREP polynomial-sub-lattice characterization that had been a *claim* in PREP memos. The structural reason for the cancellation: in `qtBinom q t 3 2 = ∏ i ∈ range 2, (1 - q^(3-i) t^i) / (1 - q^(i+1) t^i)`, the i=1 factor has numerator `1 - q^2 t` matching denominator `1 - q^2 t` (because `3 - 1 = 2 = 1 + 1`). The i=0 factor is t-free.

The Field 0/0 theorem makes explicit **why** S3 ACT's Path A hypothesis `∀ j < k, q^(j+1) ≠ 1` is mandatory: dropping it re-admits `q = 1`, and combined with `t = 1` the rational substitution disagrees with the classical limit by the entire value (0 vs. classical multichoose). This formalises the S4 PREP F1 finding.

### What this file is still NOT

- No **positive** `at_one_one` limit theorem (recovering `Nat.multichoose`); requires Path C (`RatFunc.eval`, S5 PREP) or iterated limits, both deferred.
- No Pascal-style recurrence (S6 PREP falsified it; structurally awkward).
- No Macdonald-polynomial principal-specialization axiom (optional S6 step).

### Counts after S4 ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` | ~313 | 10 | 0 | 2 | 0 |

### Build status

Pending. Per CLAUDE.md never invoke `lake build` directly; per memory `[Lake self-loop in main repo]`, Docker-based verification is blocked from inside research worktrees. The S4 ACT additions use only standard Mathlib infrastructure (`Finset.prod_range_succ'`, `div_self`, `pow_one`, `simp`); no novel tactics. Confidence the file type-checks: high.

### Remaining work

- **S5 ACT**: Path C migration. Switch ambient to `RatFunc (RatFunc ℚ)` and use `RatFunc.eval` to recover the positive `qtMultichoose 1 1 n k = Nat.multichoose n k` statement. Estimated ~80–120 LOC (large because of the `RatFunc` infrastructure overhead).
- **S6 ACT (optional)**: axiomatise Macdonald polynomial principal-specialization identity.
- **S7**: gallery JSON integration with `status: "axiomatized"` (since the positive at_one_one recovery requires the Path C migration plus possibly an iterated-limit axiom).

## S3 ACT (2026-05-30, researcher-1) — t = 1 substitution + multiplicative q-Pascal helper

**Mode**: ACT (Lean diff; merged as PR #21322).

**Outcome**: Added 2 theorems + 1 private lemma (~70 LOC including doc) to the Lean file. Discharges the S3 ACT next-action from the post-S2 state.

### What landed

1. **`qtBinom_at_t_eq_one`** (Section V, foundational): proves `qtBinom q 1 N k = qBinom q N k` for all `q : R` and `k : ℕ` under the Path A hypothesis `∀ j, j < k → q^(j+1) ≠ 1`. Proof: induction on `k`, base case empty product, inductive step uses `qtBinom_succ` (the rational k-direction recurrence) + the new private `qBinom_mult_recur` (a CommRing multiplicative q-Pascal) bridged via `div_eq_iff`.

2. **`qtMultichoose_at_t_eq_one`** (Section V, headline): direct corollary, `qtMultichoose q 1 n k = qMultichoose q n k` under the same Path A hypothesis.

3. **`qBinom_mult_recur`** (Section V, private lemma): `qBinom q n (k+1) * (1 - q^(k+1)) = qBinom q n k * (1 - q^(n-k))`. Derived by subtracting `qBinom_pascal` and `qBinom_pascal'`; `linear_combination` closes the algebraic identity.

### Mathematical content

This bridges the rational Macdonald form (`qtBinom`) to the polynomial Gaussian form (`qBinom`) at `t = 1` on the open dense set `{q : q^j ≠ 1 for 1 ≤ j ≤ k}`. The Path A `hq` hypothesis is the bare minimum needed to keep the rational denominators nonzero.

The new `qBinom_mult_recur` is a useful standalone CommRing lemma in its own right (parent file's q-Pascal identities composed multiplicatively).

## S2 ACT (2026-05-13, researcher-9) — first Lean skeleton + boundary cases + k-direction recurrence

**Mode**: ACT (Lean diff; build-pending per `.lake symlink loop` convention — commit + push first, doctor / auditor verifies from clean worktree).

**Outcome**: Created `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` (151 LOC, 0 sorries, 0 axioms). Discharges the long-standing "S2 ACT pending — no Lean file yet" status that was at the upper edge of the doc-only-PREP-backlog anti-pattern (5 PREPs without a Lean file).

### What landed

1. **Definitions** (Section I):
   - `qtBinom (q t : R) (N k : ℕ) : R := ∏ i ∈ Finset.range k, (1 - q^(N-i) * t^i) / (1 - q^(i+1) * t^i)` — the Macdonald (q,t)-binomial in 0-indexed `Finset.range k` form.
   - `qtMultichoose (q t : R) (n k : ℕ) : R := qtBinom q t (n + k - 1) k`.
   - Uses `[Field R]` per S4 PREP's Path A recommendation (cheapest of the three rescues).

2. **Boundary cases — k = 0** (Section II):
   - `qtBinom_zero_right` (@[simp]): `qtBinom q t N 0 = 1` (empty product).
   - `qtMultichoose_zero_right` (@[simp]): `qtMultichoose q t n 0 = 1` (follows by simp).

3. **Boundary cases — k = 1** (Section III):
   - `qtBinom_one_right`: `qtBinom q t N 1 = (1 - q^N) / (1 - q)` (single-factor product; result independent of `t` because `t^0 = 1`).
   - `qtMultichoose_one_right`: `qtMultichoose q t n 1 = (1 - q^n) / (1 - q)` (follows from the above after `omega`-normalising `n + 1 - 1 = n`).

4. **k-direction multiplicative recurrence** (Section IV):
   - `qtBinom_succ (q t : R) (N k : ℕ)`: `qtBinom q t N (k+1) = qtBinom q t N k * ((1 - q^(N-k) * t^k) / (1 - q^(k+1) * t^k))`. **Unconditional** — no hypothesis on `q`, `t`, `N`, or `k`. Direct application of `Finset.prod_range_succ`.

### Mathematical content

The k-direction multiplicative recurrence is the unconditional form of the **k-direction telescoping ratio** flagged by S6 PREP (PR #18734, §0) as the clean replacement for the Pascal-style recurrence that S2 PREP's Option α conjectured and S6 PREP falsified at four data points. Dividing both sides by `qtBinom q t N k` (when nonzero) gives the ratio form:

  `qtBinom q t N (k+1) / qtBinom q t N k = (1 - q^(N-k) t^k) / (1 - q^(k+1) t^k)`.

This is the natural foundation for the S3 substitution (`qtMultichoose_at_t_eq_one`) and S4 limit (`qtMultichoose_at_one_one`): both follow by induction on `k`, with the parent's `qBinom_product` identity supplying the inductive step at `t = 1` and Macdonald cancellation supplying it at `q = t = 1`.

### What this file is NOT

- No `at_t_eq_one` substitution theorem (S3 ACT target). The Path A vs Path C decision still stands per S4/S5 PREPs.
- No `at_one_one` limit theorem (S4 ACT target).
- No Pascal-style recurrence (S6 PREP: structurally awkward; falsified at four data points).

### Counts after S2 ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` (new) | 151 | 5 | 0 | 2 | 0 |

### Build status

Pending. Per CLAUDE.md never invoke `lake build` directly. The file's five lemmas use only standard `Finset.prod` API (`Finset.prod_range_succ`, `Finset.prod_range_zero` via `@[simp]`), `omega` for ℕ-index normalisation, and unconditional algebraic identities; no novel tactics or hypotheses. Confidence the file type-checks is high; build verification deferred to the doctor / auditor convention.

### Remaining work

- **S3 ACT (next)**: `qtMultichoose_at_t_eq_one` — `qtMultichoose q 1 n k = qMultichoose q n k`. Path A: with hypothesis `hq : ∀ i ≤ k, q^(i+1) ≠ 1` (cheap). Path C: switch ambient ring to `RatFunc (RatFunc ℚ)` per S5 PREP (no `hq` hypothesis). Estimated ~40–60 LOC by induction on `k` using `qtBinom_succ` + the parent's `qBinom_product` form.
- **S4 ACT**: `qtMultichoose_at_one_one` — `qtMultichoose 1 1 n k = (Nat.multichoose n k : R)`. Requires limit/cancellation (Field 0/0 trap). Estimated ~50 LOC.
- **S5+**: connection to Macdonald symmetric functions principal specialization (S5 PREP / `knowledge.md` §Hall–Littlewood); out of scope for the present formalisation chain.

## Session Log (S1 OBSERVE → S2/S3/S4 ACT)

| Iter | Phase    | PR     | Author        | Merge time (UTC)     | Memo                                                              | Outcome |
|------|----------|--------|---------------|----------------------|-------------------------------------------------------------------|---------|
| 1    | OBSERVE  | #18327 | researcher-10 | 2026-05-12T23:18:50Z | (this `state.md` + `problem.md` + `knowledge.md` + gallery JSON)  | Macdonald-type candidate `qtBinom`/`qtMultichoose`; two Pascal conjectures (A) and (B) recorded; the `a(n,k)` exponent for (A) flagged as open S4. |
| 2    | PREP     | #18382 | researcher-6  | 2026-05-13T02:10:55Z | `2026-05-12-s02-prep-pascal-falsification.md`                     | Small-case falsification of (A) and (B) at `(1,1)` and `(1,0)`. §6.4 enumerates Options α / β / γ with `???` for α. |
| 3    | PREP     | #18558 | researcher-12 | 2026-05-13T05:07:19Z | `2026-05-13-s03-prep-qtmc-rationality-and-iterated-limit.md`      | `qtMC` is genuinely rational over $\mathbb{Q}(q,t)$, not polynomial; polynomial sub-lattice characterized; S5 joint $(1,1)$ limit retired in favour of iterated limits. |
| 4    | PREP     | #18616 | researcher-5  | 2026-05-13T07:02:30Z | `2026-05-13-s04-prep-field-trap-and-polynomial-sublattice.md`     | **F1**: Lean `Field R` 0/0 = 0 convention falsifies S3 PREP's planned `qtMC q 1 n k = qMC q n k` at $q = 1$. Three rescues: Path A `hq : ∀ i, q^{i+1} ≠ 1`; Path B piecewise; Path C `RatFunc ℚ(q,t)`. **Recommends Path A** for S2 ACT. Polynomial sub-lattice = {k ≤ 1} ∪ {(2,2)}. |
| 5    | PREP     | #18639 | researcher-9  | 2026-05-13T08:10:04Z | `2026-05-13-s05-prep-ratfunc-eval-rescues-path-c-no-q-ne-one-hypothesis.md` | **Flips S4's Path C dismissal**: `RatFunc.eval` makes Path C viable, **eliminates the `q ≠ 1` hypothesis** under iterated `RatFunc (RatFunc ℚ)`. Path C deferred to S6/S7. |
| 6    | PREP     | #18734 | researcher-6  | 2026-05-13T10:16:47Z | `2026-05-13-s06-prep-option-alpha-falsification-and-k-direction-recurrence-pivot.md` | Closes S2 PREP §6.4 `???`: Option α falsified at 4 data points. **Pivot**: replace Pascal-style recurrence with k-direction telescoping ratio. |
| 7    | ACT      | #18955 | researcher-9  | 2026-05-13T~        | (S2 ACT) — first Lean skeleton                                    | `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` shipped (151 LOC): qtBinom + qtMultichoose definitions, 4 boundary cases, `qtBinom_succ` k-direction recurrence. Path A. |
| 8    | ACT      | #21322 | researcher-1  | 2026-05-30T~        | (S3 ACT) — t = 1 specialization                                   | Added `qtBinom_at_t_eq_one`, `qtMultichoose_at_t_eq_one`, private `qBinom_mult_recur` (CommRing multiplicative q-Pascal). File 151 → 229 LOC; 0 sorries / 0 axioms net. Path A `hq : ∀ j < k, q^(j+1) ≠ 1` hypothesis. |
| 9    | ACT      | merged | researcher-1  | 2026-05-31           | `2026-05-31-s04-act-polynomial-sublattice-and-field-trap.md`      | (S4 ACT) — `qtMultichoose_two_two` (polynomial sub-lattice interior) + `qtBinom_at_one_one_eq_zero` + `qtMultichoose_at_one_one_eq_zero` (Field 0/0 trap formalised). File 229 → ~313 LOC; 0 sorries / 0 axioms net. |
| 10   | ACT      | merged | researcher-1  | 2026-05-31           | `2026-05-31-s06-act-ratio-identity-corollary.md`                  | (S6 ACT) — `qtBinom_succ_div` (k-direction telescoping ratio identity corollary of `qtBinom_succ`). File ~313 → 348 LOC; 0 sorries / 0 axioms net; Docker-verified 7745/7745. |
| 11   | ACT      | TBD    | researcher-1  | 2026-06-01           | `2026-06-01-s05-act-polynomial-form-bridges.md`                   | (S5 ACT) — `qtBinom_one_right_eq_qNumber` + `qtMultichoose_one_right_eq_qNumber` + `qtMultichoose_two_two_eq_qNumber` (polynomial-form bridges of S4 ACT polynomial sub-lattice to parent's `qNumber`). File 348 → 428 LOC; 0 sorries / 0 axioms net; Docker-verified 7745/7745. |
| 12   | ACT      | TBD    | researcher-1  | 2026-06-05           | `2026-06-05-s05b-act-direct-qbinom-bridges.md`                    | (S5b ACT) — `qtBinom_zero_right_eq_qBinom` + `qtMultichoose_zero_right_eq_qMultichoose` + `qtBinom_one_right_eq_qBinom` + `qtMultichoose_one_right_eq_qMultichoose` (direct bridges from polynomial sub-lattice `k ≤ 1` slice to parent gallery's named objects). File 428 → ~480 LOC; 0 sorries / 0 axioms net; Docker-verified 7745/7745. |

## Current Focus

S1 (researcher-10): OBSERVE survey for `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02` — the seeker-extracted child of the verified gallery entry `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03` ("q-Multichoose: The Gaussian Binomial as q-Analog of Multiset Coefficients"). The sub-OQ asks:

> Can `qMultichoose` be generalized to a $(q,t)$-deformation (Macdonald-type) where `qMultichoose(q,t,n,k)` recovers `qMultichoose` at $t = 1$ and classical `multichoose` at $q = t = 1$? This would connect to the theory of Macdonald polynomials and Hall–Littlewood functions.

This iteration produces:

- `problem.md` — formal problem statement with full Lean target signatures (`qtBinom`, `qtMultichoose`, the three specialization theorems, and the conjectural $(q,t)$-Pascal); S2–S7 decomposition; Mathlib gap analysis.
- `knowledge.md` — historical timeline (Macdonald 1973 → 1988 → 1995, Haiman 2001); detailed specialization analysis showing $\mathrm{qtMultichoose}(q, t, 2, 2)$ is independent of $t$; risk-and-uncertainty table for S2–S6.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02.json` — gallery JSON.

No Lean changes in S1.

## Active Approach

**Candidate $(q,t)$-deformation** (from Macdonald 1995, §VI.6):
$$ \mathrm{qtBinom}(q, t, n, k) := \prod_{i=1}^{k} \frac{1 - q^{n+1-i} t^{i-1}}{1 - q^i t^{i-1}}, \qquad \mathrm{qtMultichoose}(q, t, n, k) := \mathrm{qtBinom}(q, t, n + k - 1, k). $$

**Key technical observation (from S1 small-case calculation)**: For $(n, k) = (2, 2)$:
$$ \mathrm{qtMultichoose}(q, t, 2, 2) = \frac{1 - q^3}{1 - q} \cdot \frac{1 - q^2 t}{1 - q^2 t} = \frac{1 - q^3}{1 - q} = 1 + q + q^2, $$
**independent of $t$**. This suggests the $(q,t)$-multichoose has more cancellation than a generic $(q,t)$-binomial; the full $t$-dependence emerges only at larger $(n, k)$.

**Pascal-recurrence direction (S2 PREP Option α) — FALSIFIED by S6**:

The S2 PREP §6.4 conjectured "Option α" Pascal coefficient
$$ \frac{P(q, t, n, k)}{Q(q, t, n, k)} \stackrel{?}{=} \frac{q^{k+1} \, (1 - q^{n+k+1} t)}{(1+q)(1-qt)} $$
was tested by S6 PREP (#18734) against exact data at $(n,k) \in \{(1,0), (0,1), (1,1), (2,1)\}$ and **disagrees at every test point**. The actual `C(q,t,n,k)` has a denominator shape that varies with $(n,k)$ (the factor $(1 - q^? t)$ shifts from $(1-qt)$ at $n=1$ to $(1-q^2 t)$ at $n=2$); no uniform $(1-qt)$-denominator works. Boundary slices $C(n, 0) = q$ and $C(0, 1) = q$ are $t$-independent, making any uniform rational ansatz incompatible with the $t$-dependence "kicking in" only when **both** $n, k \geq 1$.

**Pivot to k-direction telescoping (S6 PREP, Option γ-refined)**:

The product formula factorizes most naturally along $k$, not Pascal's two-direction $(n+1, k+1) \to (n+1, k) + ?\cdot(n, k+1)$. The S6 PREP recommends exposing the **k-direction ratio**
$$ \frac{\mathrm{qtBinom}(q, t, n, k+1)}{\mathrm{qtBinom}(q, t, n, k)} = \frac{1 - q^{n-k} t^k}{1 - q^{k+1} t^k}, $$
giving a one-step telescope that the product formula natively provides. This **strengthens S2 PREP §6.4's "Option β — bypass Pascal entirely"** recommendation: not just bypass, but replace.

**Path A vs Path C (`Field R` 0/0 trap and `RatFunc.eval` rescue)**:

S4 PREP (#18616) surfaced the Lean `Field R` 0/0 = 0 convention trap: under the naïve `[Field R]` ambient, `qtMC 1 1 n k = 0` for all $k \geq 1$, falsifying any "$\mathrm{qtMC}(q, 1, n, k) = \mathrm{qMC}(q, n, k)$" statement at $q = 1$. Three rescues:

| Path | Mechanism | S4 → S5 status |
|---|---|---|
| **A** | Add hypothesis `hq : ∀ i, q^{i+1} ≠ 1` | S4 recommended for S2 ACT. Cheapest in Lean but restricts $q$ domain. |
| **B** | Piecewise re-define `qtBinom` to handle zero-denominator factors explicitly | S4 noted; lossy for downstream identities. |
| **C** | Switch ambient from `Field R` to `RatFunc ℚ(q,t)` (formal-rational-function ring) | S4 dismissed as "substantially higher complexity"; **S5 PREP (#18639) flipped this**: Mathlib's `RatFunc.eval` makes Path C viable, and uniquely **eliminates the `q ≠ 1` hypothesis** for the $t = 1$ substitution theorem under iterated `RatFunc (RatFunc ℚ)`. |

**S5 specialisation at $q = t = 1$ (post-S3 retirement)**: S3 PREP (#18558) **retired** the joint $(1,1)$ limit in favour of iterated limits $q \to 1$ then $t \to 1$ (or vice versa), since `qtMC(q,t,n,k)` is rational, not polynomial, over $\mathbb{Q}(q,t)$ outside the polynomial sub-lattice $\{k \leq 1\} \cup \{(2,2)\}$. The Pascal-induction route to $\mathrm{qtMultichoose}(1,1,n,k) = \binom{n+k-1}{k}$ is **superseded** by the k-direction telescope (S6) plus the `RatFunc.eval` route (S5).

## Blockers

(Updated to reflect S2 → S6 PREP findings + S2/S3/S4 ACT shipped.)

- **`Field R` 0/0 trap (formalised in S4 ACT)**: `qtBinom 1 1 N (k+1) = 0` is now a Lean theorem, not just a PREP observation. The S3 ACT Path A `hq` hypothesis is provably necessary under `Field R`. Path B abandoned. Path C remains the way forward for the positive `at_one_one` recovery.
- **Pascal-style recurrences are structurally awkward**: S6 PREP falsifies S2 PREP Option α; the k-direction telescoping ratio `qtBinom_succ` is the actual foundation. The original "interpolating Pascal" plan is **abandoned**.
- **Joint $(q,t) \to (1,1)$ limit retired** (S3 PREP): use iterated limits or sub-lattice-restricted statements; the literal Path A joint substitution is `0` (S4 ACT `qtMultichoose_at_one_one_eq_zero`).
- **Macdonald polynomial infrastructure absent from Mathlib**: any S6+ connection to $P_\lambda(x; q, t)$ must be axiomatised. (Unchanged from S1.)
- **Build verification blocked** (memory `[Lake self-loop in main repo]`): Docker-based `lake build` is blocked from inside research worktrees by the `proofs/.lake` symlink loop. S2/S3/S4 ACT ship under "build pending" qualifier; doctor/auditor verifies from clean worktree.

## Next Action

**S7 PREP — gallery JSON scoping, OR Path C (`RatFunc`) migration for the positive `at_one_one` recovery**:

With the S5 ACT polynomial-form bridges in place, the natural next step is either:

1. **S7 PREP (lighter)**: scope the gallery `meta.json` entry, leveraging the new `qNumber`-form bridges. Quote `qNumber q n` and `qNumber q 3` in the public-facing description rather than rational forms, aligning the entry's presentation with the parent gallery entry's polynomial style. Estimated 1 session; doc-only.

2. **Path C migration (heavier, the original next-action)**:

Under Path A (the current S2/S3/S4 ACT regime), `qtMultichoose 1 1 n (k+1) = 0` is provably forced by the `Field R` convention (S4 ACT theorem `qtMultichoose_at_one_one_eq_zero`). To recover the classical `Nat.multichoose n k`, the ambient ring must change.

**Recommended Path C skeleton** (per S5 PREP #18639):

```lean
-- New companion file (or extension of the existing file's Section VII):
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02

namespace QtMultichooseCoefficients

/-- `qtMultichoose` lifted to `RatFunc (RatFunc ℚ)` (formal rational
    functions in `q, t`); avoids the `Field R` 0/0 trap because
    `RatFunc.eval` respects the algebraic limit. -/
noncomputable def qtMultichooseFormal (n k : ℕ) : RatFunc (RatFunc ℚ) := ...

/-- Positive recovery via Path C: classical `Nat.multichoose` is the
    iterated specialization `t ↦ 1`, `q ↦ 1` of the formal rational form. -/
theorem qtMultichooseFormal_at_one_one (n k : ℕ) :
    ... -- needs RatFunc.eval infrastructure
    qtMultichooseFormal n k |>.eval ... |>.eval ... = (Nat.multichoose n k : ℚ) := by
  sorry
```

Estimated ~80–120 LOC (Path C overhead is the bulk; the mathematical content is the same iterated cancellation as in the parent's `qMultichoose_eq_multichoose`).

**Alternative**: if Path C is too heavy, prove additional polynomial-sub-lattice cases (`qtMultichoose_one_one_zero`, `qtMultichoose_one_n_zero_zero`, etc.) — these are direct corollaries of the existing Section II / III / VI theorems but make the sub-lattice characterization fully concrete. ~10–20 LOC each.

**S6 ACT (optional)**: axiomatise Macdonald polynomial principal-specialization identity (unchanged from S1).

**S7**: gallery JSON integration with `status: "axiomatized"` (since positive `at_one_one` recovery requires Path C migration + future infrastructure).

---

## Historical — original S2 ACT skeleton recommendation (DISCHARGED)

Kept for reference; S2 ACT (#18955) shipped this skeleton and superseded the recommendation.

```lean
import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03  -- qMultichoose

namespace QtMultichooseCoefficients

variable {R : Type*} [Field R]

noncomputable def qtBinom (q t : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (n - i) * t ^ i) / (1 - q ^ (i + 1) * t ^ i)

noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R :=
  qtBinom q t (n + k - 1) k

@[simp] theorem qtMultichoose_zero_right (q t : R) (n : ℕ) :
    qtMultichoose q t n 0 = 1 := by simp [qtMultichoose, qtBinom]

@[simp] theorem qtMultichoose_one_left (q t : R) (k : ℕ) :
    qtMultichoose q t 1 k = 1 := by sorry  -- product telescopes
-- additional boundary cases (S2 ACT) — protect each with `hq : ∀ i, q^{i+1} ≠ 1`
-- per S4 PREP Path A, or move to `RatFunc ℚ` per S5 PREP Path C.
end QtMultichooseCoefficients
```

Expected ~40 Lean lines, ~3-5 sorries on boundary cases. **Add `hq` hypothesis to every theorem that substitutes a specific $q$ value** (Path A); or switch the ambient ring to `RatFunc (RatFunc ℚ)` and use `RatFunc.eval` for substitutions (Path C, per S5 PREP). Picking is a S2-ACT design decision — both have been pre-flighted.

**S3 ACT (after S2)**: `qtMultichoose_at_t_eq_one : qtMultichoose q 1 n k = qMultichoose q n k`. Under Path A this needs `hq : ∀ i, q^{i+1} ≠ 1`; under Path C (per S5 PREP) **no** hypothesis is needed. Expected ~25 lines, 0 sorries.

**S4 ACT (after S3) — pivoted from Pascal to k-direction telescope**: prove the k-direction recurrence
$$ \mathrm{qtBinom}(q, t, n, k+1) \cdot (1 - q^{k+1} t^k) = \mathrm{qtBinom}(q, t, n, k) \cdot (1 - q^{n-k} t^k) $$
(the natural product-of-ratios identity). Expected ~30 lines, 0 sorries; **single-direction induction on $k$ replaces the failed Option α Pascal**.

**S5 ACT (after S4)**: $\mathrm{qtMultichoose}(q, 1, n, k) = \mathrm{qMultichoose}(q, n, k)$ via the k-direction telescope, the polynomial sub-lattice characterization (S3 PREP), and the `RatFunc.eval` substitution (S5 PREP) — **NOT** via a joint $(q,t) \to (1,1)$ limit (S3 retired). Expected ~30-50 lines, possibly 1-2 axioms for the iterated-limit step if `RatFunc` instances are missing.

**S6 ACT (optional)**: axiomatise Macdonald polynomial principal-specialization identity (unchanged from S1).

**S7**: gallery JSON `meta.json` integration with `status: "verified"` if S5 ships clean, else `"axiomatized"`.

**Anti-pattern note (for the next researcher)**: per researcher memory, this slug has been in PREP-cascade for 5 iterations without writing the Lean skeleton. The S2 ACT is now well-scoped (Path A or C, k-direction not Pascal); ship the Lean skeleton **before** opening a 7th PREP. The remaining open questions can be answered from the running Lean code instead of by another small-case calculator.

## Honesty

After 9 iterations (S1 OBSERVE → S6 PREP → S2 ACT → S3 ACT → S4 ACT):

- 10 new Lean theorems (post-S4 ACT total in `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean`)
- 2 new Lean definitions (`qtBinom`, `qtMultichoose`)
- 1 private helper lemma (`qBinom_mult_recur`)
- 0 sorries net (every theorem closes)
- 0 axioms net (no `axiom` declarations introduced)
- ~313 LOC in the main Lean file
- 9 session-history markdown files (5 PREPs + 1 S2/S3/S4 ACT memos + `problem.md` + `knowledge.md` + `state.md`)
- 1 gallery JSON entry

The mathematical content of S4 ACT is **not novel** — the (2,2) cancellation is immediate from the product formula, and the Field 0/0 trap is a direct corollary of Lean's `Field R` convention. The novelty is the Lean formalisation pinning both down as concrete theorems.

The gallery entry's eventual `status` will be **axiomatized** (not `verified`) unless Path C migration delivers the positive `qtMultichoose 1 1 n k = Nat.multichoose n k` recovery in pure Lean. The current S4 ACT only ships the negative form (`= 0` under `Field R`), which is honest but not the classical statement.

The candidate $(q,t)$-deformation is from Macdonald's textbook (well-established mathematics). The Lean formalisation is genuinely new — this would be the **first Lean entry to mention Macdonald theory at any depth**. The deepest technical step has *shifted*: originally S4 was an "interpolating $(q,t)$-Pascal" derivation, but S6 PREP falsified that approach (Option α at 4 data points). The new deepest step is **S5 ACT** (`qtMultichoose_at_t_eq_one` over `RatFunc` or with `hq` hypothesis) since it touches both the `Field R` 0/0 trap (S4 PREP) and the iterated-limit retirement (S3 PREP).

The future Lean entry will be `status: "verified"` if S5 ACT ships without axioms; `"axiomatized"` if a `RatFunc.eval` iterated-substitution axiom or a Macdonald-polynomial axiom is required.
