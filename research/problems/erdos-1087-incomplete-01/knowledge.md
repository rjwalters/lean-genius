# Knowledge Base: erdos-1087-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Slug**: `erdos-1087-incomplete-01` (single-sorry completion task for `erdos-1087`).

**The Sorry**: line 314 of `proofs/Proofs/Erdos1087Problem.lean`, in:

```lean
theorem erdos_1087_summary :
    ∃ α β : ℝ, 3 ≤ α ∧ β ≤ 3.5 ∧
    (∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≥ n^α) ∧
    (∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≤ n^β) := by
  sorry -- follows from the bounds with appropriate constants
```

The intent: sandwich `f n` (count of degenerate quadruples) between `n^α`
and `n^β` for some `3 ≤ α` and `β ≤ 3.5`, using the existing axioms.

## Session 2026-05-08 (Session 1) — Assessment: Sorry is Unfillable As Stated (researcher-8)

**Mode**: FRESH
**Outcome**: BLOCKED — sorry is not derivable from the existing axioms; the
theorem statement needs reformulation (or strengthening of the axiom
constants), not a proof attempt.

### What I Did

Read the file (316 lines, 6 theorems, 2 axioms, 1 sorry, status `axiomatized`),
analyzed the axioms supplying the bounds, and assessed buildability.

### Why The Sorry Is Unfillable

The two supporting axioms are:

```lean
axiom erdos_purdy_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≥ c * (n : ℝ)^3 * Real.log n

axiom erdos_purdy_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≤ C * (n : ℝ)^(7/2)
```

Both have **existentially-quantified positive constants** `c` and `C` — the
axiom guarantees only that *some* positive constant works, not that the
constants are 1.

The summary's two requirements:

1. **Lower** (with `α = 3`): need `f n ≥ n^3` for all `n ≥ 4`, i.e.
   `c · log n ≥ 1`. For `n = 4`: requires `c ≥ 1/log 4 ≈ 0.722`. The axiom
   only gives `c > 0`, which can be arbitrarily small.
2. **Upper** (with `β = 3.5`): need `f n ≤ n^{3.5}` for all `n ≥ 4`, i.e.
   `C ≤ 1`. The axiom only gives `C > 0`, which can be arbitrarily large.

For *general* α ≥ 3 (existentially in the summary), the lower bound is
unaffected: any α ≥ 3 with `c · n^3 · log n ≥ n^α` gives
`α ≤ 3 + log_n(c · log n)`. The RHS varies with `n`, with infimum approaching
3 (as `n → ∞` if c is fixed) but the *finite-n* worst case is at `n = 4`
giving `α ≤ 3 + log_4(c · log 4)`. For small `c`, this is `< 3`, contradicting
`α ≥ 3`.

So `∃ α ≥ 3, ∀ n ≥ 4, f n ≥ n^α` is NOT a logical consequence of
`∃ c > 0, ∀ n ≥ 4, f n ≥ c · n^3 · log n`.

By symmetric argument, `∃ β ≤ 3.5, ∀ n ≥ 4, f n ≤ n^β` is NOT a logical
consequence of `∃ C > 0, ∀ n ≥ 4, f n ≤ C · n^{7/2}`.

### Reformulations That Would Be Provable

- **With explicit constants**: `∃ α β c' C', 3 ≤ α ∧ β ≤ 3.5 ∧ c' > 0 ∧ C' > 0 ∧
  ∀ n ≥ 4, c' · n^α ≤ f n ≤ C' · n^β`. Pick α = 3, β = 7/2, then
  `c' = c · log 4` (the infimum of `c · log n` for `n ≥ 4`) and `C' = C`.
- **With limits/asymptotics**: `f n = Θ(n^α)` for some α with `3 ≤ α ≤ 7/2`
  (in big-Θ notation) — provable from the axioms but heavier machinery.
- **Just bounds_gap**: the existing `bounds_gap` (`∃ α β, 3 ≤ α ∧ β ≤ 3.5 ∧ α < β`)
  is the trivial 2-line existence statement that *is* provable; it's already
  proved in the file. The summary tries to combine `bounds_gap` with the
  bound axioms but loses information about the constants.

### Recommendation

The sorry should be replaced by one of:

1. **Reformulate** the summary to include explicit constants (`c'`, `C'`),
   then derive from the axioms with α = 3, β = 7/2.
2. **Delete** the summary and rely on `erdos_1087` (which packages the
   lower/upper bounds directly). The summary adds no information beyond
   `erdos_1087` once you put in concrete constants.

Both are "fix the statement" operations, not "fill the sorry". This slug
should likely be re-classified from `incomplete-01` to a docs/restructuring
task, or split into a sibling slug for the reformulation.

### Status

- **Axiom count**: 2 (unchanged — `erdos_purdy_lower_bound`, `erdos_purdy_upper_bound`).
- **Sorry count**: 1 (unchanged — `erdos_1087_summary`).
- **Phase**: BLOCKED (sorry is unfillable as stated).

### Why Not Done This Session

The sorry's resolution requires editing the theorem statement (not just
filling a placeholder). Per the researcher role's "What Counts as Progress"
guidelines, fabricating an axiom or pretending the existential gives us
explicit constants would be dishonest. Documenting the structural issue
exposes the gap for the next researcher (or curator) to address with a
reformulated statement.

---

## Insights

- **Existentially-quantified constants in axioms cannot be forgotten** when
  using them downstream. The summary statement `∃ α, ∀ n, f n ≥ n^α` is
  weaker than `∃ α c, ∀ n, f n ≥ c · n^α`, and the existing axiom only
  yields the latter form.
- **Buildability assessment is part of the role**: per `feedback_researcher_session_time_merge.md`
  patterns and the "BLOCKED — needs > 1000 lines foundational work" criterion,
  this slug is structurally blocked by the *theorem statement*, not by
  missing infrastructure. The right output is documentation of the issue,
  not a forced proof.

## Dead Ends

- **Naively `refine ⟨3, 3.5, _, _, _, _⟩`**: would leave 4 goals, 2 of which
  (the bounds applied to all n ≥ 4) require constants the axioms do not
  give. Cannot be closed without an explicit-constant reformulation.
