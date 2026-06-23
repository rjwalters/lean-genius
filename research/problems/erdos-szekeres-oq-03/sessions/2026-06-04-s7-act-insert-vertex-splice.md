# S7 ACT — Splice lemma `IsMonochromatic.insert_vertex`

**Researcher**: researcher-1
**Date**: 2026-06-04
**Phase**: ACT (S7 splice infrastructure; the `s > k ∧ t > k` sorry in
`ramsey_existence` is unchanged at this iteration)
**PR**: (this PR)

## Summary

Closes the **splice gap** in the S6 ACT-D plan: given a
`k`-monochromatic sub-clique `S'` on the non-vertex side **plus** the
S6 `link_lifts`-derived vertex-side hypothesis `hLink`, we now have a
single composition lemma producing the `k`-monochromatic clique
`insert v S'` of size `|S'| + 1`.

One new lemma lands in `proofs/Proofs/RamseyHypergraph.lean`, just
after `IsMonochromatic.link_lifts` (the S6 ACT-D output):

```lean
lemma IsMonochromatic.insert_vertex {n k : ℕ} {χ : kColoring n} {c : Bool}
    {v : Fin n} {S' : Finset (Fin n)} (hvS' : v ∉ S')
    (hS' : IsMonochromatic χ k S' c)
    (hLink : ∀ T ∈ (insert v S').powersetCard k, v ∈ T → χ T = c) :
    IsMonochromatic χ k (insert v S') c
```

Proof is a direct `by_cases hvT : v ∈ T` on each `k`-subset
`T ⊆ insert v S'`:

* **Case `v ∈ T`** — `hLink` discharges directly (re-pack `hTsub` /
  `hTcard` into a `powersetCard` membership).
* **Case `v ∉ T`** — every `x ∈ T` lies in `insert v S'` but is not
  `v`, so `x ∈ S'`. Hence `T ⊆ S'` and `hS'` discharges.

The proof is ~12 lines of tactic body (15 with the docstring framing
the lemma's role in the S7+ Ramsey 1930 induction).

## Net file deltas

| Metric | Before (S6 ACT-D, `origin/main`) | After (this S7 ACT) | Δ |
|--------|----------------------------------|---------------------|---|
| LOC | 654 | 688 | +34 |
| lemmas+theorems | 18 | 19 | +1 |
| defs+structures | 5 | 5 | 0 |
| sorries | 1 | 1 | 0 |
| axioms | 0 | 0 | 0 |

The lone surviving sorry in `ramsey_existence` (the `s > k ∧ t > k`
genuine inductive case) is unchanged. The splice lemma is the
**precondition** for closing that sorry in a future S8 session — see
the next-action menu below for the induction body sketch.

## Why this is the right S7 work

The S6 ACT-D memo's S7 candidate plan named **`insert_vertex` as the
single missing ingredient** between the existing toolkit and the
Ramsey 1930 induction body:

> Then the Ramsey 1930 inductive step assembles: ... 3. Restrict
> `χ.link v` to `Fin n \ {v}` ⇒ obtain a `(k-1)`-mono clique `S` of
> appropriate size. 4. WLOG false case: apply the IH on `s + t` to
> `χ` restricted to `S` ⇒ either a `k`-mono-false sub-clique
> `S' ⊆ S` (use `insert_vertex` to extend by `v` to a `k`-mono-false
> `s`-clique) or a `k`-mono-true `t`-clique on `S` (done).

This PR lands `insert_vertex` as a stand-alone lemma. The remaining
induction body (an estimated 80–120 LOC of `Nat.strongRecOn`
machinery plus the `IH(k-1)` ⇒ `IH(k)` neighborhood-collapse
plumbing) is deferred to S8 because:

* The induction needs to be on the lexicographic pair `(k, s + t)`,
  which requires an explicit termination argument (`WellFoundedRecursion`
  or `decreasing_by`-style) — non-trivial enough to deserve its own
  session.
* It is much easier to inspect `insert_vertex` in isolation than to
  bundle it with the harder induction; if the splice lemma has a
  subtle bug, catching it in a small PR is preferable.
* The S6 link infrastructure + this splice lemma together form the
  complete set of *non-recursive* facts the proof needs; the only
  remaining work after this PR is the recursion itself.

## Implementation walkthrough

### The splice lemma's signature

```lean
lemma IsMonochromatic.insert_vertex {n k : ℕ} {χ : kColoring n} {c : Bool}
    {v : Fin n} {S' : Finset (Fin n)} (hvS' : v ∉ S')
    (hS' : IsMonochromatic χ k S' c)
    (hLink : ∀ T ∈ (insert v S').powersetCard k, v ∈ T → χ T = c) :
    IsMonochromatic χ k (insert v S') c
```

The hypothesis names mirror the S6 `link_lifts` output:

* `hvS' : v ∉ S'` — the non-vertex side `S'` excludes `v`. This is
  *not strictly needed* for the proof (the case-split on `v ∈ T`
  handles both possibilities cleanly), but documenting `hvS'` keeps
  the lemma's intended use clear and matches the shape of the S6
  `link_lifts` hypothesis (which takes `hvS : v ∉ S`).
* `hS' : IsMonochromatic χ k S' c` — the **non-vertex side** facts:
  every `k`-subset of `S'` already evaluates to `c`. Comes from the
  outer induction's `IH(s+t)` application on `χ` restricted to
  `Fin n \ {v}`.
* `hLink` — the **vertex side** facts: every `k`-subset of
  `insert v S'` *containing* `v` evaluates to `c`. Comes from
  `IsMonochromatic.link_lifts` (the S6 vertex-side
  `(k-1) → k` transfer) applied to a `(k-1)`-mono clique of
  `χ.link v`.

### Case `v ∈ T` (vertex-side)

```lean
exact hLink T (Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩) hvT
```

Direct application of `hLink`. The only mild gymnastic is re-packing
`hTsub` and `hTcard` (extracted via `Finset.mem_powersetCard.mp` at
the top of the proof) into a fresh `powersetCard` membership term,
since `hLink` takes a `powersetCard` argument rather than the split
`subset + card` pair. (Lean's `mp ∘ mpr` is not a definitional
identity in this elaboration context.)

### Case `v ∉ T` (non-vertex-side)

```lean
have hT_sub_S' : T ⊆ S' := by
  intro x hxT
  have hxInsert : x ∈ insert v S' := hTsub hxT
  rcases Finset.mem_insert.mp hxInsert with hxv | hxS'
  · exact absurd (hxv ▸ hxT) hvT
  · exact hxS'
exact hS' T (Finset.mem_powersetCard.mpr ⟨hT_sub_S', hTcard⟩)
```

The crux is the subset proof `T ⊆ S'`:

* Each `x ∈ T` is in `insert v S'` (since `T ⊆ insert v S'`).
* `Finset.mem_insert` gives the disjunction `x = v ∨ x ∈ S'`.
* In the `x = v` branch, rewriting `x = v` in `hxT : x ∈ T` gives
  `v ∈ T`, contradicting `hvT : v ∉ T` — discharged via `absurd`.
* In the `x ∈ S'` branch, return `hxS'` directly.

Then `hS'` discharges using `T`'s membership in `S'.powersetCard k`
(re-packing `hT_sub_S'` and `hTcard`).

## Build status — NOT verified locally

The worktree shares the broken `proofs/.lake` symlink (per memory
`feedback_researcher_lake_symlink_broken.md`), and Docker is unavailable
on this host. Build verification deferred to CI / next-auditor pass.
Confidence grounded in:

* **Pattern equivalence**: the proof's tactic vocabulary
  (`Finset.mem_powersetCard`, `Finset.mem_insert`, `by_cases`,
  `absurd`, `rcases`) is identical to S4's `is_ramsey_self_right` and
  S6's `link_lifts`, both of which have built clean in their merged
  PRs (#19454, #18122-followup CI).
* **No new imports**: every symbol used is already imported by the
  S6 ACT-D additions (`Finset.mem_insert`, `Finset.mem_powersetCard`
  come from `Mathlib.Data.Finset.Basic`, already pulled in).
* **Local type-check**: the proof's term shape matches the goal
  structure 1-to-1 — each case discharges by `exact` against a fact
  whose type signature has been written out in the docstring.

## Iteration outcome

Splice lemma landed. The Ramsey 1930 induction now has all
non-recursive ingredients (`anti_s`, `anti_t`, `mono_n`, `mono`,
`swap`, `self_right`, `self_left`, `link_lifts`, `link_apply`,
`insert_vertex`). The lone surviving sorry remains the `s > k ∧ t > k`
case of `ramsey_existence`, but its proof is now a pure recursion-body
question with no missing sub-lemmas.

## Next Action (S8 candidate menu)

* **(S8 ACT-F: Ramsey 1930 induction body)** — assemble the
  pieces. The `Nat.strongRecOn` machinery on `(k, s + t)` is the only
  remaining ingredient. ~80–120 LOC, but each block is now a direct
  application of a named lemma. Closes the file's last sorry.
  * Sub-step F1: state `∀ k ≥ 2, ∀ s t ≥ k, ∃ n, IsRamsey n k s t` as
    a `Nat.strongRecOn` on `k + (s + t)` (or lexicographic
    `(k, s + t)`); discharge `k = 2` as a separate base case (use
    `isRamsey_one_iff` + a custom `k = 2` argument, since
    `is_ramsey_self_*` only cover `s = k` and `t = k`).
  * Sub-step F2: the inductive step at `k ≥ 3` follows the textbook
    Ramsey 1930 proof line by line — pick `v = ⟨0, _⟩`, restrict
    `χ.link v` to `Fin (n-1)` (need a `castLE`-style embedding),
    apply `IH(k-1)` to extract a `(k-1)`-mono clique `S`, then apply
    `IH(k, s' + t)` or `IH(k, s + t')` to `χ` on `S` to extract a
    `k`-mono `(s-1)`- or `(t-1)`-clique `S'`, then splice via
    `insert_vertex`.
* **(meta sync)** — `lineCount`/`theoremCount` for
  `RamseyHypergraph.lean` are not currently tracked in the
  `erdos-szekeres` meta.json (the file is under `additionalFiles`).
  A separate hermit / curator PR could add per-additional-file
  metrics for the gallery to show.
* **(skip)** — park this slug as splice-ready and return to other
  slugs.

Recommended for S8: **(F1 + F2)** as a single PR closing the file's
last sorry. This is the natural finish line of the OQ-03 work — once
done, the file becomes 0-sorry / 0-axiom and the gallery badge can
flip from `wip` to `verified`.
