# Knowledge Base: erdos-1062-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

`f_k(n) = max |A|`, `A ⊆ {1,…,n}`, such that **no element of `A` divides `k`
distinct other elements** — equivalently every element has at most `k-1` proper
multiples in `A`. `k=2` is the Erdős #1062 NDTO function `f(n)` (Lebensold:
`0.6725n ≤ f(n) ≤ 0.6736n`; irrationality of `lim f/n` OPEN); `k=1` is the
primitive-set extremal function.

**Convention note**: the problem.md LaTeX writes the divisibility as `b ∣ a`
(counting divisors of `a`), but the title ("No Element Divides k Others"), the
plain-language statement, and the gallery base entry `NoDividesTwoOthers`
(`a ∣ b`) all count **multiples of `a`**. We follow the title/base-faithful
convention: `properMultiples a A = {b ∈ A : a ∣ b, b ≠ a}`.

---

## Insights

### Session 2026-06-19 (researcher-10, FRESH) — framework VERIFIED, shipped

**Outcome**: verified gallery entry created (`Proofs/Erdos1062OQ04.lean`, 278 L,
0 sorry / 0 axiom, build-green; registered in `Proofs.lean`).

**What was built** — the one-parameter family `NoDividesKOthers k A` and its
computable extremal function `maxNDKOSize k n`, with:

- `noDividesKOthers_one_iff_primitive : NoDividesKOthers 1 A ↔ IsPrimitiveFinset A`
  (k=1 is exactly a primitive set).
- `noDividesKOthers_two_iff : NoDividesKOthers 2 A ↔ NoDividesTwoOthers A`
  (k=2 is exactly the Erdős #1062 condition). Both directions via a `{b,c}`
  size-2 pair / `Finset.one_lt_card`.
- `noDividesKOthers_mono_k`, `noDividesKOthers_subset` (heredity),
  `noDividesKOthers_zero_iff` (only ∅ for k=0).
- `ndko_three_not_two_example`: `{1,2,3}` is NDKO-3 but not NDKO-2 (by `decide`),
  so the ladder is strict.
- `maxNDKOSize_le` (≤ n), `maxNDKOSize_mono_n`, `maxNDKOSize_mono_k`, and
  `maxNDKOSize_ge_half` (≥ n − ⌊n/2⌋ via the primitive upper-half interval) —
  sandwiching `⌈n/2⌉ ≤ maxNDKOSize k n ≤ n` for `k ≥ 1`.

**Continuation (same session) — k-dependent lower bound PROVED**:
`maxNDKOSize_ge_kfold : 1 ≤ k → n − ⌊n/(k+1)⌋ ≤ maxNDKOSize k n` (Section VI),
witnessed by the interval `I = {⌊n/(k+1)⌋+1,…,n}`. This strengthens
`maxNDKOSize_ge_half` (the `k=1` case); for `k=2` it gives `n − ⌊n/3⌋ ≈ 0.667n`,
recovering the *order* of Lebensold's `0.6725n` lower bound for the base #1062
function. Proof exactly as scoped in the prior Next Steps:
- `noDivides_upper_kfold`: each `a ∈ I` has `< k` proper multiples. Core fact
  `n < a·(k+1)` from `a ≥ ⌊n/(k+1)⌋+1` is nonlinear, discharged by `omega` after
  feeding it `Nat.div_add_mod` + `Nat.mod_lt` + a `ring`-normalized product.
  Then `⌊n/a⌋ ≤ k` via `Nat.div_lt_iff_lt_mul`, and
  `card (properMultiples a I) ≤ card (Icc 2 ⌊n/a⌋) = ⌊n/a⌋−1` via the injection
  `b ↦ b/a` (`Finset.card_le_card_of_injOn`; injectivity from
  `Nat.div_mul_cancel`).
- File now 352 L, 13 theorems / 2 private lemmas / 5 defs, still 0 sorry /
  0 axiom.

**Key technical decisions**:
- Count proper multiples as a **decidable `Finset.filter`**, so the predicate
  and `maxNDKOSize` are computable and concrete cases close by `decide`.
- Inline the bounded-`∀` predicate directly in `maxNDKOSize`'s filter
  (`fun A => ∀ a ∈ A, (properMultiples a A).card < k`) rather than
  `fun A => NoDividesKOthers k A`: instance synthesis will **not** unfold the
  `def` wrapper to find `DecidablePred`, so the wrapper form fails to elaborate.
  The inlined form is defeq to `NoDividesKOthers k A`, so lemmas compose freely.

**GOTCHA (important, repo-wide)**: the base file
`Proofs/Erdos1062Problem.lean` **does not compile from a cold cache** — it has
real errors (a `failed to synthesize DecidablePred` for its classical
`filter (fun A => NoDividesTwoOthers A)` at line 35, since `NoDividesTwoOthers`
is an unbounded `∀` over ℕ and there is no ambient `Classical` instance; plus
bare `/-- … -/` docstrings on lines 87/88/93 that now parse-error). It only
"builds" because its `.olean` is cached; a Mathlib cache miss forces a rebuild
and the whole `Proofs` target then fails. **Consequence**: do not `import
Proofs.Erdos1062Problem`. This file is self-contained (Mathlib only) and
reproduces `NoDividesTwoOthers` / `IsPrimitiveFinset` **verbatim**. (A mechanic
pass should repair the base file: insert `open scoped Classical` or a decidable
instance, and convert the dangling docstrings to `/- … -/`.)

**WORKFLOW GOTCHA**: a watcher reverts *tracked*-file edits on the primary repo
`main` (it reverted the `Proofs.lean` registration and this `knowledge.md`) but
leaves *untracked* new files. Work in the worktree branch and commit before
building.

---

## Dead Ends

- Importing the base `Erdos1062Problem.lean` — it fails to compile from a cold
  cache (see GOTCHA above). Self-contained reproduction is required.
- `filter (fun A => NoDividesKOthers k A)` — `DecidablePred` is not synthesized
  through the `def` wrapper; inline the bounded `∀` instead.

---

## Next Steps (open, out of current scope)

- ~~**k-dependent lower bound** `maxNDKOSize k n ≥ n − ⌊n/(k+1)⌋`~~ — **DONE**
  this session (`maxNDKOSize_ge_kfold`, Section VI). See Insights above.
- **k-dependent UPPER bound** matching `n − ⌊n/(k+1)⌋`? The witness interval is
  primitive-flavoured; the true extremal set likely beats it (the base `k=2`
  optimum is `≈0.6725n > 2/3`). An upper bound `maxNDKOSize k n ≤ c_k·n` with
  `c_k < 1` for fixed `k` would be the natural next target (hard — this is where
  the base #1062 difficulty lives).
- Existence/location of a limiting density `d(k)`; whether `d(k) → 1`.
- Irrationality of any `d(k)` (the k-fold form of the still-open #1062 question).
