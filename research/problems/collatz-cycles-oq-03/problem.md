# Problem: No All-Odd Collatz Cycles (Parity One-Liner)

**Slug**: `collatz-cycles-oq-03`
**Parent**: `collatz-cycles` — *Collatz Cycles: Non-Existence of Small Cycles*.
Status `verified`, badge `original`, 0 sorries, 0 axioms, 27 theorems, 4
definitions, 256 lines (`proofs/Proofs/CollatzCycles.lean`).
**Sibling proofs**: `collatz-cycles-oq-04` (separate iteration), `collatz-structured`
and its OQ chain (OQ-02 / OQ-02-OQ-01 / OQ-03).

## Plain Statement

The seeker phrases the open question as

> Prove that there are no **odd cycles** (cycles that never reach an even
> number) — equivalent to the cycle constraint.

A natural formalisation is the *cycle-contains-even* form: every
non-degenerate Collatz cycle visits at least one even number.

**Claim (parity lemma).** Let `n ≥ 1` and `k ≥ 1` with `collatzIter k n = n`.
Then at least one of `n, collatz n, collatz² n, …, collatz^{k−1} n` is even.

Equivalently, the contrapositive:

```lean
theorem no_all_odd_cycle
    {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1)
    (hper : collatzIter k n = n)
    (hodd_all : ∀ i, i < k → (collatzIter i n) % 2 = 1) : False
```

## Why this Matters

1. **Closes a clean structural gap.** The parent file `CollatzCycles.lean`
   already proves five structural constraints on hypothetical Collatz
   cycles (no fixed points, no 2-cycles, 3-cycle of 1 unique, 3/4
   contraction, `2^M > 3^j` halving bound). It does **not** explicitly
   state the *parity intersection* property: every cycle hits both
   parities. This OQ fills the gap with a one-line proof.

2. **Trivial-but-foundational.** The proof is a 2-line parity argument
   (`collatz_odd` says `n%2=1 ⟹ collatz n = 3n+1`, which is even). The
   contribution is **honest documentation**, not new mathematics; this
   slug is a classic "fill an obvious lemma the gallery currently skips."

3. **Equivalent to the `2^M > 3^j` bound at `M = 0`.** A pure all-odd
   cycle has `M = 0` (zero halvings) and `j = k` (every step is odd).
   The parent's halving constraint Part VI implicitly forces `M ≥ 1`,
   but the parent never extracts the `M = 0 ⇒ false` corollary
   explicitly. This OQ makes that link.

4. **Decidable cycle-search support.** A future enumerator searching for
   non-trivial Collatz cycles can short-circuit any candidate orbit
   whose computed parity pattern is all-odd; this lemma is the
   correctness witness for that short-circuit.

## Mathematical Specification

### Setup

The parent (`Proofs/CollatzCycles.lean`) defines:

```lean
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1
def collatzIter (k : ℕ) (n : ℕ) : ℕ := collatz^[k] n
def IsPeriodic (n : ℕ) (k : ℕ) : Prop := k ≥ 1 ∧ collatzIter k n = n
```

with these key lemmas:

| Lemma | Statement |
|-------|-----------|
| `collatz_odd` | `n % 2 = 1 → collatz n = 3 * n + 1` |
| `collatz_even` | `n % 2 = 0 → collatz n = n / 2` |
| `collatz_odd_growth` | `n % 2 = 1 ∧ n ≥ 1 → collatz n > n` |
| `collatz_even_decrease` | `n % 2 = 0 ∧ n ≥ 2 → collatz n < n` |

### The Argument

Suppose for contradiction every iterate up to step `k` is odd. Then in
particular `n % 2 = 1`, so

```
collatz n = 3 * n + 1
```

and `3 * n + 1 ≡ 0 (mod 2)` for any odd `n` (since `3 · 1 + 1 = 4 ≡ 0`,
and in general `3n + 1` has the opposite parity of `n`). Hence
`(collatz n) % 2 = 0`, but by hypothesis `(collatzIter 1 n) % 2 = 1`,
contradiction.

That's it. The proof is two lines of `omega` after one unfold.

### Equivalent Phrasings

| Form | Statement | Notes |
|------|-----------|-------|
| **Negative** | No all-odd cycle exists (the OQ statement). | The contrapositive form is easiest in Lean. |
| **Positive** | Every cycle contains at least one even number. | Direct existential — useful for future cycle enumerators. |
| **Quantitative** | If `IsPeriodic n k` and `n ≥ 1`, then `#{i < k : collatzIter i n % 2 = 0} ≥ 1`. | One-liner from the contrapositive. |

The positive existential form is the natural gallery statement.

### Why this is **not** the same as `collatz_odd_growth`

`collatz_odd_growth` says `collatz n > n` for odd `n ≥ 1`. By itself
this rules out an all-odd *fixed point* but not an all-odd *length-≥2
cycle*. For example, an all-odd 2-cycle would require `n_1 < n_2 < n_1`,
which is also impossible by transitivity — but that argument uses
strict-ordering chains rather than parity directly. The OQ-03 statement
gives a *single-step* parity contradiction, which generalises cleanly
to longer cycles and to the *forall-iterate-odd* form needed downstream.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `collatz-cycles` | parent | parity case analysis, `interval_cases`, `native_decide` |
| `collatz-cycles-oq-04` | sibling OQ on the same parent | structural cycle constraints |
| `collatz-structured` | divides-by-3 / halving structure of orbits | `Nat.log2`, `Nat.pow` arithmetic |
| `collatz-structured-oq-02` | recursive structure of orbits | structural induction |

## Initial Thoughts

### Recommended Approach

**S2 ACT** (single session, ~30-50 Lean lines including imports/namespace):

```lean
-- new file: proofs/Proofs/CollatzCyclesOQ03.lean
import Mathlib.Tactic
import Proofs.CollatzCycles

namespace CollatzCycles

/-- Parity flip: 3n+1 is even when n is odd. -/
lemma three_n_plus_one_even {n : ℕ} (h : n % 2 = 1) : (3 * n + 1) % 2 = 0 := by
  omega

/-- For odd n, collatz n is even. -/
theorem collatz_of_odd_is_even {n : ℕ} (h : n % 2 = 1) : (collatz n) % 2 = 0 := by
  rw [collatz_odd h]; exact three_n_plus_one_even h

/-- No all-odd Collatz cycle exists. -/
theorem no_all_odd_cycle {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1)
    (hper : collatzIter k n = n)
    (hodd_all : ∀ i, i < k → (collatzIter i n) % 2 = 1) : False := by
  have h0 : (collatzIter 0 n) % 2 = 1 := by
    simp [collatzIter]; exact hodd_all 0 hk
  have h1 : (collatzIter 1 n) % 2 = 0 := by
    simp [collatzIter, Function.iterate_one]
    exact collatz_of_odd_is_even (by simpa using h0)
  -- if k = 1: collatzIter 1 n = n, n is odd, but collatzIter 1 n is even ⇒ false
  -- if k ≥ 2: hodd_all 1 (Nat.lt_of_lt_of_le ...) says (collatzIter 1 n) % 2 = 1
  rcases Nat.lt_or_ge 1 k with hk2 | hk2
  · -- k ≥ 2: hodd_all gives contradiction at i = 1
    have := hodd_all 1 hk2
    omega
  · -- k = 1: hper gives collatzIter 1 n = n; n odd (from h0); but h1 says even
    interval_cases k
    · -- k = 1
      have heq : collatzIter 1 n = n := hper
      have hn_odd : n % 2 = 1 := by simpa [collatzIter] using h0
      have hn_even : n % 2 = 0 := by rw [← heq]; exact h1
      omega

/-- Positive existential form: every cycle visits at least one even number. -/
theorem cycle_contains_even {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1)
    (hper : collatzIter k n = n) : ∃ i, i < k ∧ (collatzIter i n) % 2 = 0 := by
  by_contra hne
  push_neg at hne
  apply no_all_odd_cycle hn hk hper
  intro i hi
  have := hne i hi
  omega

end CollatzCycles
```

### Risks

- **None substantive.** The proof reduces to `omega` + one rewrite.
- **Possible trap**: confusion with `collatzIter`/`Function.iterate`
  normalisation. Standard idiom: `simp [collatzIter, Function.iterate_succ]`.

## Decomposition

| Session | Deliverable | Estimated effort |
|---------|-------------|------------------|
| **S1 OBSERVE** (this PR) | 4 doc files; no Lean changes | ~30 min |
| **S2 ACT** | `CollatzCyclesOQ03.lean` (~50 lines, 3 theorems, 0 sorries); register in `proofs/Proofs.lean`; Docker build verify | ~45-60 min |
| **S3 GALLERY** | `src/data/proofs/collatz-cycles-oq-03/` (meta.json + index.ts + annotations.json); status `verified`, badge `original`, 0 axioms | ~30 min |

S2 and S3 can be merged into a single session if time permits; the gallery
update is mechanical once the Lean file builds clean.

## References

- Parent file: `Proofs/CollatzCycles.lean` Parts I–VIII (lines 1–256).
- Lagarias (1985), *The 3x+1 problem and its generalizations*: cycle
  constraint `2^M > 3^j`; our OQ is the corollary at `M = 0`.
- Eliahou (1993), cycle length lower bounds.
- Tao (2019), *Almost all orbits of the Collatz map attain almost
  bounded values*: probabilistic upper-density argument; orthogonal to
  our deterministic parity claim.

## Calibration

This is a **TRIVIAL** OQ in the parent sense: the proof is two omega
steps. The contribution is the explicit Lean lemma + a gallery entry
that documents the parity argument. Honesty: this is *infill*, not
new mathematics. Reporting it as anything more would inflate.
