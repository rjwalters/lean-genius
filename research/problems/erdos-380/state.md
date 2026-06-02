# Current State: erdos-380

**Phase**: OBSERVE
**Path**: full
**Since**: 2026-06-02T00:00:00Z (S1 OBSERVE; was placeholder NEW since 2026-01-13)
**Iteration**: 1 (S1 OBSERVE — file inventory + 1-axiom analysis + forward roadmap, doc-only)

## S1 OBSERVE (researcher-1, 2026-06-02, this PR) — file inventory + 1-axiom analysis + roadmap

**Outcome**: progress — the slug's `state.md` was a 28-line placeholder
("Begin problem exploration", NEW since 2026-01-13); the actual Lean file
`proofs/Proofs/Erdos380Problem.lean` is a sophisticated **396-LOC** file
with **17 theorems + 12 definitions + 1 axiom + 0 sorries**, fully
consistent with `meta.json` (`status: axiomatized`, `badge: axiom` —
correct per CLAUDE.md policy for Erdős open conjectures). S1 absorbs
this drift and proposes a forward roadmap.

### §1 Mathematical content

Erdős Problem #380 (https://www.erdosproblems.com/380): an interval
`[u, v]` is **bad** if the greatest prime factor `P` of `∏_{u ≤ m ≤ v} m`
occurs with exponent `> 1` in the product. Let `B(x)` count integers
`n ≤ x` contained in at least one bad interval.

**Conjecture (Erdős)**: `B(x) ~ #{n ≤ x : P(n)² | n}` (where `P(n)` is
the greatest prime factor of `n`).

**Known**: Erdős–Graham (1980) proved `B(x) > x^{1-o(1)}` via the
chain `x^{1-ε} ≤ #{n ≤ x : P(n)² | n} ≤ B(x)`.

### §2 Existing Lean file inventory

396 LOC, **no namespace**, `open Nat Finset`. Imports:
`Mathlib.Data.Nat.Prime.Basic`, `Mathlib.Data.Nat.Basic`,
`Mathlib.Data.Finset.Basic`, `Mathlib.Data.Finset.Card`,
`Mathlib.Data.Nat.Factorization.Basic`,
`Mathlib.NumberTheory.Bertrand`, `Mathlib.Tactic`.

**12 definitions** (lines 35, 69, 76, 82, 86, 94, 307, 313, 318, 322,
326, 392):

| Symbol | Line | Type |
|---|---|---|
| `greatestPrimeFactor` (GPF) | 35 | `ℕ → ℕ` via `Nat.primeFactors.max'` (was 4-axiom; now concrete) |
| `IsBadInterval` | 69 | `ℕ → ℕ → Prop` |
| `InBadInterval` | 76 | `ℕ → Prop` |
| `badCount` (B(x)) | 82 | `ℕ → ℕ` (noncomputable) |
| `gpfSquareCount` (G(x)) | 86 | `ℕ → ℕ` (noncomputable) |
| `ErdosProblem380` | 94 | `Prop` — `B(x) / G(x) → 1` |
| `IsPowerful` | 307 | `ℕ → Prop` (powerful numbers) |
| `IsVeryBadInterval` | 313 | `ℕ → ℕ → Prop` (refined bad-interval) |
| `InVeryBadInterval` | 318 | `ℕ → Prop` |
| `veryBadCount` | 322 | `ℕ → ℕ` (noncomputable) |
| `powerfulCount` | 326 | `ℕ → ℕ` (noncomputable) |
| `VeryBadConjecture` | 392 | `Prop` (refined sub-conjecture) |

**17 theorems** at lines 40, 49, 58, 114, 131, 196, 262, 273, 283, 289,
331, 341, 346, 356, 361, 373, 384.

Highlights:

- **GPF foundation** (3 thm: `gpf_prime`, `gpf_dvd`, `gpf_largest`,
  lines 40-58, ~25 LOC) — proves the GPF properties from the
  concrete definition (was previously 4 axioms; now 0 axioms in this
  section).
- **`erdos_graham_lower`** (line 114, ~10 LOC) — `B(x) > x^{1-ε}` for
  large `x`, derived from `gpfSquare_asymptotic` (the sole axiom) +
  `badCount_ge_gpfSquareCount` (lemma chain). Note: previously
  axiomatized, now a theorem.
- **`bad_interval_no_prime`** (line 131, ~60 LOC) — bad intervals with
  `v < 2u` cannot contain primes. Uses
  `Finset.single_le_prod'`/`Finset.mul_prod_erase`/`gpf_largest` chain.
- **`bad_interval_no_prime_general`** (line 196, ~65 LOC) — strengthens
  to unconditional via Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`).
- **`bad_interval_v_bound`** (line 262, ~10 LOC) — `v ≤ ?` consequence.
- **`singleton_bad_iff`** (line 273, ~10 LOC) — `[n,n]` is bad iff
  `P(n)² | n`.
- **`gpfSquare_in_bad`** (line 283, ~5 LOC) — `P(n)² | n → n ∈ bad`.
- **`badCount_ge_gpfSquareCount`** (line 289, ~20 LOC) — the `G ≤ B`
  inequality underpinning Erdős–Graham.
- **`counting_chain`** (line 384, ~10 LOC) — assembles the chain
  `powerfulCount ≤ veryBadCount ≤ badCount` for the refined system.

**1 axiom** (line 105):

```lean
axiom gpfSquare_asymptotic :
    ∃ c : ℚ, 0 < c ∧
      ∀ (ε : ℚ), 0 < ε →
        ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
          (x : ℚ) ^ (1 - ε) ≤ (gpfSquareCount x : ℚ)
```

The asymptotic count: `#{n ≤ x : P(n)² | n} ≥ x^{1-ε}` for all `ε > 0`
and large `x`. This is the analytic-number-theory input to
Erdős–Graham's lower bound. Tight asymptotic is
`x / exp(c √(log x · log log x))` (per file docstring).

### §3 The 3 ACT lanes (deferred to S2+)

#### Lane A: Discharge `gpfSquare_asymptotic` from Mathlib analytic NT

**Strategy**: requires Mathlib's smooth-number / friable-number theory
or character-sum machinery (Brun/Selberg sieve, Hildebrand–Tenenbaum
estimates). **Probably out-of-reach** at Mathlib v4.26.0 — needs
upstream contribution of smooth-number asymptotics first. Unlikely
single-cycle feasible.

#### Lane B: Tighten `erdos_graham_lower` to a sharper `B(x) ≥ G(x) · constant`

**Strategy**: `badCount_ge_gpfSquareCount` already proven; the
remaining gap to a sharper bound is the `1-o(1)` exponent
improvement. Without Lane A, this is **not actionable** at the
current stage.

#### Lane C: Develop the `VeryBadConjecture` refined system

**Strategy**: the file already has 6 theorems for the very-bad
subsystem (`veryBad_is_bad`, `veryBad_interval_no_prime`,
`singleton_veryBad_iff`, `powerful_in_veryBad`,
`veryBadCount_le_badCount`, `veryBadCount_ge_powerfulCount`,
`counting_chain`). A natural S2 ACT direction is to prove the
**ultra-strong form**: `IsPowerful n ↔ InVeryBadInterval n ∧ n ∈ singleton`
or similar tightening. ~30-50 LOC. **Tractable** — uses only `gpf_*`
+ standard divisibility lemmas already in scope.

#### Lane D: Mathlib v4.26.0 build-verification check

**Strategy**: the file currently shows `1 axiom` in the meta.json, but
the structural soundness depends on the GPF concrete definition
(which depends on `Nat.primeFactors_nonempty`, `Finset.max'`,
`Nat.mem_primeFactors`). Verify the file builds at the current
Mathlib pin via Docker BUILD-VERIFY. **Deferred** to deployer/auditor
per build-pending policy (sibling `lean-build-57602` 5h+ occupying
shared image).

### §4 Recommended S2 picker path

**S2 ACT**: Lane C (`VeryBadConjecture` tightening) is the most
actionable single-cycle iteration — tractable LOC, uses existing
bearer stack, advances toward the slug's mathematical core.

Lane A (the axiom discharge) is the biggest mathematical target but
likely blocked by Mathlib v4.26.0's lack of smooth-number analytic
machinery; could become tractable in a future Mathlib release.

| Iteration | Target | LOC | Risk |
|---|---|---|---|
| S2 ACT | Lane C: VeryBadConjecture tightening (~30-50 LOC) | low-medium | low |
| S3 PREP | Lane A bearer scope: survey Mathlib analytic NT for smooth-number bearers | doc-only | low |
| S4+ | Lane A ACT (if S3 PREP finds tractable bearers) | unknown | high |

### §5 What S1 OBSERVE did **not** do (explicit)

1. **No Lean file edits.** Slug remains at 396 LOC / 17 thm / 12 defs
   / 1 axiom / 0 sorries / `axiomatized`. Lane C tightening deferred
   to S2.
2. **No `meta.json` edits.** Counts already accurate.
3. **No `knowledge.md` creation.** Will be drafted in S2 ACT.
4. **No bearer SHA-pin verification.** Deferred to S2 PREP / ACT
   cycle.
5. **No JSON tracker creation/update.** S2 will create the
   `src/data/research/problems/erdos-380.json` tracker if missing.
6. **No Docker BUILD-VERIFY.** Lane D deferred per build-pending
   policy (sibling `lean-build-57602` 5h+ on shared image).

### §6 References

- File: `proofs/Proofs/Erdos380Problem.lean` (396 LOC, 17 thm + 12
  defs + 1 axiom + 0 sorries).
- meta.json: `src/data/proofs/erdos-380/meta.json` (`status:
  axiomatized`, `badge: axiom`, counts match exactly).
- Source: https://www.erdosproblems.com/380 (per file header).
- Erdős–Graham 1980 — primary citation for the lower bound (paper
  not located in-tree).
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged
  since 2026-05-13, 21 days).
- Bearer `Nat.exists_prime_lt_and_le_two_mul` already used in
  `bad_interval_no_prime_general` — confirms Bertrand's postulate
  available at pin.
