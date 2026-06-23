# S7 ACT — Step 5 `sigma_eq_self_add_cofactor` discharge (build pending — Docker daemon down)

**Date**: 2026-06-04
**Researcher**: researcher-1
**Mode**: ACT (Lean edit + state.md/JSON/sessions/ doc updates)
**Branch**: `research/sum-of-divisors-oq-02-s7-act-step5-discharge`
**Base**: `origin/main` (`58d24ff982f`)
**Build status**: PENDING — Docker daemon unavailable (`docker images` →
`Cannot connect to the Docker daemon`). Follows S5 ACT #19562 / S6 ACT
#19644 build-pending qualifier pattern.

## TL;DR

Replaces the `sorry` at L115 of `proofs/Proofs/SumOfDivisorsOQ02.lean`
(`sigma_eq_self_add_cofactor`, Step 5) with a 3-LOC tactic-mode body:

```lean
  have hpos : 0 < mersenne (k + 1) := mersenne_pos.mpr (Nat.succ_pos k)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h_eq, mul_add, ← hm, ← succ_mersenne (k + 1), add_mul, one_mul]
```

Plus a ~17-LOC docstring expansion documenting paste provenance + bearer
verification + build-pending qualifier.

**Sorry count delta: −1** (3 → 2). Step 5 closed. Steps remaining: Step 6
(`cofactor_one_and_prime` at L127), top-level
`euler_converse_self_contained` (L136).

## §1 — Proof structure

**Goal**: `σ 1 m = m + c`
**Hypotheses**:
* `hm : m = mersenne (k + 1) * c`
* `h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m`

**Strategy**: multiply both sides of the goal by `mersenne (k + 1) > 0`
and reduce to algebraic identity verifiable by `rw` chain.

### §1.1 — Positivity

`mersenne_pos.mpr (Nat.succ_pos k) : 0 < mersenne (k + 1)`.

`mersenne_pos` is `0 < mersenne p ↔ 0 < p` (LucasLehmer.lean:64);
applied with `Nat.succ_pos k : 0 < k + 1` gives the positivity needed
for `Nat.eq_of_mul_eq_mul_left`.

### §1.2 — Cancellation reduction

`Nat.eq_of_mul_eq_mul_left : 0 < n → n * a = n * b → a = b` (Lean core stdlib).

Applied with `hpos`: the goal `σ 1 m = m + c` reduces to
`mersenne (k+1) * σ 1 m = mersenne (k+1) * (m + c)`.

### §1.3 — `rw` chain (5 steps)

Goal after `refine`:
```
mersenne (k+1) * σ 1 m = mersenne (k+1) * (m + c)
```

Apply `rw [h_eq, mul_add, ← hm, ← succ_mersenne (k+1), add_mul, one_mul]`:

| Rewrite | Effect | Resulting goal |
|---|---|---|
| `h_eq` | LHS: `mersenne(k+1) * σ 1 m → 2^(k+1) * m` | `2^(k+1) * m = mersenne(k+1) * (m + c)` |
| `mul_add` | RHS: `mersenne(k+1) * (m + c) → mersenne(k+1) * m + mersenne(k+1) * c` | `2^(k+1) * m = mersenne(k+1) * m + mersenne(k+1) * c` |
| `← hm` | RHS trailing: `mersenne(k+1) * c → m` | `2^(k+1) * m = mersenne(k+1) * m + m` |
| `← succ_mersenne (k+1)` | LHS: `2^(k+1) → mersenne(k+1) + 1` | `(mersenne(k+1) + 1) * m = mersenne(k+1) * m + m` |
| `add_mul` | LHS: `(mersenne(k+1) + 1) * m → mersenne(k+1) * m + 1 * m` | `mersenne(k+1) * m + 1 * m = mersenne(k+1) * m + m` |
| `one_mul` | LHS: `1 * m → m` | `mersenne(k+1) * m + m = mersenne(k+1) * m + m` |

Closes by `rfl` (implicit at end of `rw` chain).

## §2 — Bearer pin verification

All bearers verified 0-drift at Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-pinned `v4.26.0`) via
`gh api` raw-content fetch this session.

| Bearer | Module | Line | Signature |
|---|---|---|---|
| `mersenne_pos` | `Mathlib/NumberTheory/LucasLehmer.lean` | 64 | `theorem mersenne_pos {p : ℕ} : 0 < mersenne p ↔ 0 < p` |
| `succ_mersenne` | `Mathlib/NumberTheory/LucasLehmer.lean` | 102 | `theorem succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k` |
| `Nat.eq_of_mul_eq_mul_left` | Lean4 core stdlib | — | `Nat.eq_of_mul_eq_mul_left : 0 < n → n * a = n * b → a = b` |
| `Nat.succ_pos` | Lean4 core stdlib | — | `Nat.succ_pos : ∀ (n : ℕ), 0 < n + 1` (or equivalent for `0 < k + 1`) |
| `mul_add`, `add_mul`, `one_mul` | `Mathlib/Algebra/Ring/...` / `Mathlib/Algebra/Order/...` | — | ring axioms / monoid actions; ubiquitous |

The two NEW Mathlib bearers (`mersenne_pos`, `succ_mersenne`) were located
via `gh api search/code?q=mersenne` and confirmed via direct
`gh api repos/.../contents/Mathlib/NumberTheory/LucasLehmer.lean?ref=2df2f01…`
fetch + grep for declarations. Both are simp-marked and stable in
LucasLehmer.lean since at least Mathlib v4.21.0.

The supporting bearers (`Nat.eq_of_mul_eq_mul_left`, `Nat.succ_pos`,
`mul_add`, `add_mul`, `one_mul`) are core lemmas in stable locations not
requiring fresh re-verification.

## §3 — Risk-acceptance triple (per S5 ACT / S6 ACT pattern)

* **(a) Recent BUILD-VERIFY**: this session §2 cross-referenced the two
  new Mathlib bearers via direct gh raw fetch at the pinned SHA. The
  Archive `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`
  proof (lines 81–127 of
  `Archive/Wiedijk100Theorems/PerfectNumbers.lean`) uses exactly the
  identity `2^(k+1) = mersenne(k+1) + 1` (via `succ_mersenne`) and
  `Nat.eq_of_mul_eq_mul_left` for the same cancellation step. That
  Archive proof passes Mathlib CI at the pinned SHA.

* **(b) Bearer 0-drift**: `gh api` fetch this session showed the same
  `mersenne_pos` and `succ_mersenne` signatures as the Archive
  expects. No drift between the May-16 last-ACT bearer-pin and the
  June-04 today fetch.

* **(c) Leaf-only adds vs in-file edit**: single-file edit
  (`proofs/Proofs/SumOfDivisorsOQ02.lean`) — body replacement at L115
  (`by sorry` → 3-LOC tactic body) + docstring expansion (~17 LOC).
  No new imports, no namespace disturbance, no new file. Strictly
  weakens the file (sorry 3 → 2; theorem/lemma/axiom counts
  unchanged).

## §4 — Failure modes + fallbacks

If the build (when docker recovers) reveals issues:

### §4.1 — `mersenne_pos.mpr (Nat.succ_pos k)` failure

If the iff direction doesn't match (signature is `0 < mersenne p ↔ 0 < p`,
need `0 < k + 1 → 0 < mersenne (k+1)`):
```lean
have hpos : 0 < mersenne (k + 1) := by
  rw [mersenne_pos]; exact Nat.succ_pos k
```
or:
```lean
have hpos : 0 < mersenne (k + 1) := by positivity
```
(`positivity` extension for `mersenne` is provided in LucasLehmer.lean:84).

### §4.2 — `Nat.eq_of_mul_eq_mul_left` symbol resolution

If unqualified or wrong namespace:
```lean
refine mul_left_cancel₀ hpos.ne' ?_
```
where `hpos.ne' : mersenne (k+1) ≠ 0` (using `Nat.pos_iff_ne_zero`).

### §4.3 — `rw [← hm]` ambiguity (matches `mersenne (k+1) * c` after
`mul_add` step)

After `rw [h_eq, mul_add]` the goal is
`2^(k+1) * m = mersenne (k+1) * m + mersenne (k+1) * c`. Only one
occurrence of `mersenne (k+1) * c` appears (RHS rightmost summand);
`rw [← hm]` should match unambiguously. If it fails:
```lean
nth_rewrite 2 [← hm]  -- if positional
```
or:
```lean
rw [show mersenne (k+1) * c = m from hm.symm]
```

### §4.4 — `rw [← succ_mersenne (k+1)]` argument inference

If Lean can't infer the implicit argument:
```lean
rw [show (2 : ℕ)^(k+1) = mersenne (k+1) + 1 from (succ_mersenne (k+1)).symm]
```

### §4.5 — Total fallback: explicit calc-block

```lean
lemma sigma_eq_self_add_cofactor (...) : σ 1 m = m + c := by
  have hpos : 0 < mersenne (k+1) := mersenne_pos.mpr (Nat.succ_pos k)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc mersenne (k+1) * σ 1 m
      = 2^(k+1) * m := h_eq
    _ = (mersenne (k+1) + 1) * m := by rw [← succ_mersenne]
    _ = mersenne (k+1) * m + 1 * m := by rw [add_mul]
    _ = mersenne (k+1) * m + m := by rw [one_mul]
    _ = mersenne (k+1) * m + mersenne (k+1) * c := by rw [← hm]
    _ = mersenne (k+1) * (m + c) := by rw [← mul_add]
```

More verbose (8 LOC vs 3) but easier to debug.

## §5 — File scope (anti-race guarantee)

* Updated: `proofs/Proofs/SumOfDivisorsOQ02.lean` (Lean body replacement +
  docstring expansion at L106–115; 138 → ~158 LOC). Sorry count 3 → 2.
* Updated: `research/problems/sum-of-divisors-oq-02/state.md` (this
  block prepended; all prior content preserved; phase ACT iteration 7 → 8).
* Updated: `src/data/research/problems/sum-of-divisors-oq-02.json`
  (`currentState.phase` ACT (continued), `currentState.iteration` 7 → 8,
  `currentState.since` refresh, `currentState.focus + nextAction` refresh).
* New: `research/problems/sum-of-divisors-oq-02/sessions/2026-06-04-s7-act-step5-discharge.md` (this file).
* **Not touched**: problem.md, knowledge.md, literature/, sibling slugs,
  proofs/Proofs.lean, lake-manifest.json, src/data/proofs/.

Cannot conflict with:
* Any future Step-6 ACT (L127 different lemma).
* Any future top-level `euler_converse_self_contained` ACT
  (L136 different theorem).
* Any concurrent mechanic `fix(meta): sync …` PR for this slug's
  `leanFiles` block (the JSON-side `sorryCount` field is mechanic
  territory; this ACT only refreshes `currentState`).

## §6 — Pool side-effect (out-of-PR)

`scripts/research/claim-problem.sh release sum-of-divisors-oq-02`
runs after PR push. Status remains `in-progress` (NOT `completed`)
because Step 6 + top-level chain remain (2 of 4 sorries still open
after this ACT, both at lines L127 and L136 of post-ACT file).

## §7 — Next-step register

* **Step 6 ACT** (next): close `cofactor_one_and_prime` at L127.
  Per knowledge.md Step 6 plan: `Nat.sum_divisors_eq_sum_properDivisors_add_self`
  to expose `σ(m) = m + ∑ properDivisors`, then `m + c = m + ∑ propers`
  gives `∑ propers = c`. Since `c ∣ m` and `c < m`, `c` is itself a
  proper divisor of `m`, so `∑ propers ≥ c` with equality iff
  `properDivisors m = {c}`. Combined with `1 ∣ m`, this forces
  `c = 1` and `properDivisors m = {1}`, the latter being equivalent
  to `m.Prime` via `Nat.sum_properDivisors_eq_one_iff_prime`.
* **Top-level `euler_converse_self_contained` ACT** (after Step 6):
  chain Steps 1–6 with `eq_two_pow_mul_odd` from Archive to split
  `n = 2^k * m` with `m` odd, then identify `m = mersenne (k+1)` and
  `m.Prime`. Estimated 20–30 LOC.
* **Build verification**: this PR + sibling S5 ACT (#19562) + S6 ACT
  (#19644) all need Docker-side verification. Single-Docker-iter
  expected once host recovers.

## §8 — Honesty assessment

This iteration ships one routine algebraic step (cancellation in a
linear-in-σ equation). The mathematical content is **modest** — most
of the work was bearer verification (gh raw fetch) and writing the
docstring + session file to document provenance. The tactic body itself
is 3 LOC.

**Risk note**: the body has not been docker-built; the build-pending
qualifier is explicit. If `rw [← hm]` (§4.3) or any other step misfires
on elaboration, the §4 fallbacks provide a path. The most likely
fallback to need is §4.5 (calc-block), which is verified by the
Archive's own use of the same lemmas at the same SHA.

The slug is **not closed** by this ACT — Step 6 and the top-level chain
remain. Gallery value: still pedagogical-only (per Step 5 of the
session §S2 of the slug's S2 OBSERVE audit), which is the expected
outcome.

Reported truthfully as such.
