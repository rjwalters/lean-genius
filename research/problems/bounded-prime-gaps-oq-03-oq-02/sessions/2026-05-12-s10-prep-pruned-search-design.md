# S10 Prep — `engelsmaSearchPruned` design survey

**Phase**: ACT (preparation, doc-only)
**Date**: 2026-05-12
**Researcher**: researcher-8
**Builds on**: PR #18218 (S9 — naive `engelsmaSearch` surface API) and PR #18090
(S8 — bridge lemma `engelsma_lower_bound_of_finitary`).

This note designs the **pruned** variant of `engelsmaSearch` that S10–S12 of the
research thread will implement. It fleshes out `knowledge.md` §4.2/§4.3 into a
concrete Lean encoding plan — choice of runtime representation, branch order,
correctness-lemma decomposition, and the boundary between S10/S11/S12.

This is a **planning-only** document. No Lean code is committed; no state.md /
knowledge.md / json fields are mutated. All identifiers below are proposals to
be ratified or modified once S10 starts implementation.

---

## §1. What S9 left behind

PR #18218 (researcher-5, in flight) lands the naive interface:

```lean
def engelsmaSearch (w k : ℕ) : Bool :=
  decide (∃ H ∈ (Finset.range w).powersetCard k, 0 ∈ H ∧ IsAdmissible H)

theorem engelsmaSearch_eq_false_iff (w k : ℕ) :
    engelsmaSearch w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H
```

plus the bridge

```lean
theorem engelsma_lower_bound_of_engelsmaSearch_false
    (h : engelsmaSearch 246 50 = false) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne
```

Composing this with S8's `engelsma_lower_bound_of_finitary` gives the chain

> `engelsmaSearch 246 50 = false`  ⟹  `engelsma_lower_bound`.

But the LHS is computationally infeasible at `(50, 246)` because `decide`
enumerates `Finset.powersetCard 50 (Finset.range 246) ≈ 1.7 × 10^54` subsets.
The S9 PR is *infrastructure*: it fixes the surface API so that future pruned
variants can be substituted at the implementation layer without touching the
downstream `engelsma_lower_bound_of_engelsmaSearch_false` consumer.

S10's job is the substitution. Concretely: produce

```lean
def engelsmaSearchPruned (w k : ℕ) : Bool := ...
theorem engelsmaSearchPruned_correct (w k : ℕ) :
    engelsmaSearchPruned w k = engelsmaSearch w k
```

so that `engelsmaSearchPruned 246 50 = false` (by `native_decide` on the pruned
implementation) discharges `engelsmaSearch 246 50 = false` (by rewriting along
the correctness equation), which then flows through the S9 bridge into the
axiom replacement.

---

## §2. The algorithmic skeleton (concrete form of `knowledge.md` §4.2)

Engelsma's algorithm, restated with the variable names that S10's Lean code
will use:

```
function search(w, k, primes, candidates, chosen):
    if chosen.size == k:
        return true                      -- found admissible k-tuple
    if candidates.size < k - chosen.size:
        return false                     -- not enough candidates remaining
    if primes is empty:
        # Enumerate (k - chosen.size)-subsets of candidates;
        # for each, check admissibility against primes > primeCutoff
        # (using IsAdmissibleBdd's restriction to p ≤ H.card).
        return any(isAdmissible(chosen ∪ S) for S in subsetsOfSize(...))
    let p = primes.head
    for r in 0..p-1:
        let candidates' = filter (λ n. n % p ≠ r) candidates
        let chosen' = filter (λ n. n % p ≠ r) chosen
        # If chosen already has residue r mod p, this branch is dead
        if chosen'.size < chosen.size: continue
        if search(w, k, primes.tail, candidates', chosen):
            return true
    return false
```

Three things make this fast in practice:

1. **Residue pruning**: at each prime `p`, we commit to a "forbidden" residue
   class `r`. All `n % p = r` candidates die. Over `primes = [2, 3, 5, 7]`
   alone, this prunes by a factor of `2 · 3 · 5 · 7 = 210` (best case).
2. **Cardinality short-circuit**: once `candidates.size < k - chosen.size`, no
   subtree can succeed. This dominates the tree shape near leaves.
3. **Prime cutoff**: once `primes` is empty, the residual admissibility check
   is bounded by `IsAdmissibleBdd` (knowledge.md §3.1), which only quantifies
   over `p ≤ H.card`. So after exhausting `primes = [2, 3, 5, ..., 47]` (the
   primes up to 50 = k), the rest is just bounded `Decidable`.

The empirical claim (Polymath 8b §6, Engelsma 2013) is that the resulting tree
at `(50, 246)` has ~10^6 leaves, runnable in ~1 second of C and ~10–60 seconds
of compiled Lean.

---

## §3. Lean representation choices

S10 must pick a concrete in-Lean encoding for `candidates`, `chosen`, and
`primes`. Three options, in increasing order of complexity:

### §3.1 Option F (Finset-native)

```lean
def engelsmaSearchPruned (w k : ℕ)
    (primes : List ℕ := primesUpTo k)
    (candidates : Finset ℕ := Finset.range w)
    (chosen : Finset ℕ := ∅) : Bool := ...
```

**Pros**: Matches the existing S9 `engelsmaSearch` signature exactly; the
correctness lemma `engelsmaSearchPruned_correct` reduces to functional
extensionality on `Finset`. No runtime/proof bridge needed.

**Cons**: `Finset` is backed by `Multiset` backed by `Quotient List`. Every
`Finset.filter` invocation allocates a new `Quotient`-wrapped list, and the
extracted compiled code carries the quotient machinery. Polymath gallery
experience (and `Mathlib.Data.Nat.Sieve`) shows this is **10×–100× slower**
than a plain `List` or `Array` representation. At `(50, 246)`, that turns a
10–60 s search into a 100–6000 s search — probably still feasible but risky.

### §3.2 Option A (Array-runtime with Finset bridge)

```lean
def engelsmaSearchPrunedArr (w k : ℕ)
    (primes : List ℕ)
    (candidates : Array ℕ)
    (chosen : Array ℕ) : Bool := ...

def engelsmaSearchPruned (w k : ℕ) : Bool :=
  engelsmaSearchPrunedArr w k (primesUpTo k).toArray
    (Array.range w) #[]

theorem engelsmaSearchPruned_correct (w k : ℕ) :
    engelsmaSearchPruned w k = engelsmaSearch w k := ...
```

**Pros**: `Array.filter` compiles to a tight C-level loop (no quotient
overhead). Expected `(50, 246)` runtime: 10–60 s, matching the C reference.
This is the same trick `Mathlib.Data.Nat.Sieve` and the gallery's
`engelsma50Tuple_admissible` use.

**Cons**: The correctness proof requires an `Array`/`Finset` bridge lemma
that itself is non-trivial. Roughly:

```lean
theorem search_array_eq_search_finset
    (w k : ℕ) (primes : List ℕ) (candidates : Array ℕ) (chosen : Array ℕ) :
    engelsmaSearchPrunedArr w k primes candidates chosen =
    engelsmaSearchPrunedFinset w k primes candidates.toFinset chosen.toFinset
```

This is mechanical (induction on `primes`, push `Array.filter`/`Finset.filter`
through), but it's ~50–150 lines of unfun pushing-down lemmas.

### §3.3 Option L (List-runtime, no Finset bridge)

```lean
def engelsmaSearchPrunedList (w k : ℕ)
    (primes : List ℕ)
    (candidates : List ℕ)
    (chosen : List ℕ) : Bool := ...
```

**Pros**: `List` has clean structural induction (no quotient); proofs are
easier than Array; runtime is ~1.5–3× slower than Array but still **far**
faster than Finset. Common choice for medium-complexity certified
computations.

**Cons**: We still need a bridge to `Finset` for the S9-compatible interface.
That bridge is essentially the same shape as Option A's (push `List.filter`
through `List.toFinset`).

### §3.4 Recommendation

**Option L**, for these reasons:

* The Finset/List bridge is simpler than the Finset/Array bridge (`List.toFinset`
  is well-developed in Mathlib; `Array.toFinset` is thinner and requires
  `Multiset.coe_toList`-style detours).
* Runtime is acceptable: 30–180 s estimated for `(50, 246)` after compilation.
  Within CI tolerance for `native_decide`.
* If profiling shows L is too slow at the actual `(50, 246)` call, S11 can
  upgrade to Option A; the bridge lemma in S10 makes the substitution
  transparent.

**Compromise fallback**: implement Option F first (smallest surface area), run
on the small unit tests (k=6 w=16 etc.), and only upgrade to Option L if the
small cases reveal the Finset overhead is a problem. This stages the risk.

---

## §4. Correctness-lemma decomposition

The full correctness statement is

```lean
theorem engelsmaSearchPruned_correct (w k : ℕ) :
    engelsmaSearchPruned w k = true ↔
      ∃ H ∈ (Finset.range w).powersetCard k, 0 ∈ H ∧ IsAdmissible H
```

(or the symmetric `engelsmaSearchPruned w k = engelsmaSearch w k` if we accept
the S9 surface API as the spec). Either way, proving this directly is
~200–500 lines. Decompose into:

### §4.1 `searchAux_sound` (recursive soundness)

```lean
theorem searchAux_sound (w k : ℕ) (primes : List ℕ)
    (candidates : List ℕ) (chosen : List ℕ)
    (h : searchAux w k primes candidates chosen = true) :
    ∃ S ⊆ candidates.toFinset, S.card = k - chosen.toFinset.card ∧
      0 ∈ (chosen.toFinset ∪ S) ∧ IsAdmissible (chosen.toFinset ∪ S)
```

By strong induction on `(primes.length, candidates.length)` ordered
lexicographically. ~50–100 lines.

### §4.2 `searchAux_complete` (recursive completeness)

```lean
theorem searchAux_complete (w k : ℕ) (primes : List ℕ)
    (candidates : List ℕ) (chosen : List ℕ)
    (S : Finset ℕ) (hS : S ⊆ candidates.toFinset)
    (hcard : S.card = k - chosen.toFinset.card)
    (h0 : 0 ∈ chosen.toFinset ∪ S)
    (hadm : IsAdmissible (chosen.toFinset ∪ S))
    (hpr : ∀ p ∈ primes, ...) :  -- "primes already accounted for in chosen"
    searchAux w k primes candidates chosen = true
```

By induction on `primes`: at each prime `p`, pick the residue class `r ∈ Fin p`
that's absent from `(chosen.toFinset ∪ S).image (· % p)` (such an `r` exists
because the union is admissible). Recurse on the `r`-branch. ~100–150 lines.

### §4.3 Headline `engelsmaSearchPruned_correct`

```lean
theorem engelsmaSearchPruned_correct (w k : ℕ) :
    engelsmaSearchPruned w k = true ↔
      ∃ H ∈ (Finset.range w).powersetCard k, 0 ∈ H ∧ IsAdmissible H
```

Iff. Forward via `searchAux_sound`. Reverse via `searchAux_complete` applied
to `(primes := primesUpTo k, candidates := List.range w, chosen := [0])`.
~30–50 lines once §4.1/§4.2 are in place.

### §4.4 Optional `engelsmaSearchPruned_eq_engelsmaSearch`

If we want the rewrite to flow through S9's bridge directly:

```lean
theorem engelsmaSearchPruned_eq_engelsmaSearch (w k : ℕ) :
    engelsmaSearchPruned w k = engelsmaSearch w k :=
  Bool.eq_iff_iff.mpr ⟨..., ...⟩  -- via engelsmaSearchPruned_correct
                                  -- and engelsmaSearch_eq_true_iff (S9 PR)
```

`engelsmaSearch_eq_true_iff` is the obvious sibling of `engelsmaSearch_eq_false_iff`
already in S9; the S9 PR or a follow-up will need to add it. ~5 lines.

### §4.5 Total budget

- §4.1: 50–100 lines
- §4.2: 100–150 lines
- §4.3: 30–50 lines
- §4.4: 5–10 lines
- Auxiliary `searchAux` `def`: 30–50 lines
- Helper lemmas (`primesUpTo`, branch-soundness mini-lemmas): 50–100 lines

**Total: 265–460 lines** for S10–S11 combined. S10 lands `searchAux` +
small-case `native_decide` unit tests; S11 lands the correctness chain.

---

## §5. Branch order: small primes first

The recursion in §2 is parameterized by the prime list. Performance is
**asymmetric** in branch order:

* **Small primes first** (recommended): at `p = 2`, half the candidates die
  per branch (2 branches × 50% pruning). At `p = 3`, two-thirds (3 × 67%).
  The cumulative pruning is the product `1/2 · 2/3 · 4/5 · ...`, which by
  Mertens-style estimates is ~`1/log(p_last)`. For primes up to 47 (the cutoff
  at k=50), the candidate set shrinks by a factor of ~100 per leaf.
* **Large primes first**: each branch at `p = 47` only prunes by ~2% (one
  residue class out of 47). The tree explodes near the root because we don't
  short-circuit on cardinality early.

Engelsma's original C implementation uses small-primes-first. Lean should
follow suit.

Concretely, S10's `primesUpTo k` should return primes in **ascending** order:

```lean
def primesUpTo (k : ℕ) : List ℕ :=
  (List.range (k + 1)).filter Nat.Prime
```

(Mathlib also has `Nat.factorial`-style prime enumerators; for the small
ranges we care about, `List.filter` is fine.)

---

## §6. Prime cutoff: why `primes = primesUpTo k`?

The cutoff comes from §3.1 of `knowledge.md` (which becomes the file's
`IsAdmissibleBdd`): for primes `p > k`, admissibility is automatic because
`(H.image (· % p)).card ≤ H.card = k < p`. So once the branching prime list
runs out, the *remaining* admissibility content is fully captured by
`IsAdmissibleBdd` and can be discharged by `decide`/`native_decide` on the
small bounded-`Finset.range (k+1).filter Nat.Prime` quantifier.

For k=50, the relevant primes are `[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
41, 43, 47]` — 15 primes. The branching factor product is
`2 · 3 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 31 · 37 · 41 · 43 · 47 ≈ 1.2 × 10^17`,
but the effective tree (after pruning) is empirically ~10^6 leaves
(Polymath 8b §6.3).

S10 unit tests should run on shorter prime lists:

* `(k, w) = (6, 16)`: primes `[2, 3, 5]`. Search space ~`2 · 3 · 5 = 30`
  branches × `C(16, 6) = 8008` leaf-subsets. Matches S4's existing
  `native_decide`-verified bound; the pruned version should agree.
* `(k, w) = (10, 30)`: primes `[2, 3, 5, 7]`. The vacuous-but-real
  S7-deferred test. Pruned version should run in <1s; original `decide`
  estimate was 30–120 s.

The unit test `(6, 16)` is *the* feasibility checkpoint: if Option L's
pruned variant at `(6, 16)` doesn't match S4's value, the implementation is
wrong and we don't proceed to `(10, 30)` or `(50, 246)`.

---

## §7. The candidate-set invariant

A subtle but important invariant for §4 correctness:

> At every recursive call, `candidates ⊆ Finset.range w` and `chosen ⊆ Finset.range w`,
> and `∀ n ∈ chosen, ∀ p ∈ primesDone, n % p ∉ forbidden(p)`,

where `primesDone` is `primesUpTo k \ primes`. This ensures the partial
admissibility check (only against the primes we've already branched on) is
maintained throughout the recursion.

In Lean, the cleanest encoding is to carry `forbidden : ℕ → Option ℕ` (the
residue class we've committed to forbid at each prime) as an additional
parameter to `searchAux`. Then `candidates` is always
`(List.range w).filter (λ n. ∀ p, forbidden p = some r → n % p ≠ r)`. But
explicitly storing `candidates` is faster than recomputing the filter at every
recursive call — hence the `candidates`-as-an-argument idiom.

For the proof of §4.2, the invariant `candidates = (List.range w).filter (...)`
should be a separate `searchAux_candidates_correct` lemma carried implicitly.

---

## §8. S10 deliverable scope (proposal)

**Goal**: Land `engelsmaSearchPruned` + small-case unit tests in
`BoundedPrimeGapsOQ03OQ02.lean`. Defer the full correctness chain to S11.

**File changes**:
* `BoundedPrimeGapsOQ03OQ02.lean`: +120–180 lines.
  - `def primesUpTo (k : ℕ) : List ℕ`
  - `def searchAux (w k : ℕ) (primes : List ℕ) (candidates : List ℕ) (chosen : List ℕ) : Bool`
  - `def engelsmaSearchPruned (w k : ℕ) : Bool`
  - `theorem engelsmaSearchPruned_6_16_eq_engelsmaSearch_6_16 :
       engelsmaSearchPruned 16 6 = engelsmaSearch 16 6 := by native_decide`
  - Optional: `engelsmaSearchPruned_10_30_*` if runtime cooperates.
* No state.md / knowledge.md edits in S10 (those land in S11/S12 once the
  correctness chain is in place).

**No new axioms**: the `native_decide` calls reuse the `Lean.ofReduceBool`
axiom already present from S4. `axiomCount` stays at 1.

**Build risk**: moderate. The `searchAux` recursion needs a termination
metric — likely `(primes.length, candidates.length)` lexicographic — which
Lean's auto-termination usually handles for ascending-prime-list recursion.
If it doesn't, an explicit `termination_by` clause is needed (~5 lines).

---

## §9. S11 deliverable scope

**Goal**: Land `engelsmaSearchPruned_correct` (the iff against the existential
form).

**File changes**:
* `BoundedPrimeGapsOQ03OQ02.lean`: +200–300 lines.
  - `searchAux_sound` (§4.1)
  - `searchAux_complete` (§4.2)
  - `engelsmaSearchPruned_correct` (§4.3)
* The S9 file already has `engelsmaSearch_eq_false_iff`; S11 may add the
  symmetric `_eq_true_iff` as a 5-line preamble if needed for §4.4.

**Build risk**: higher. The `searchAux_complete` proof is the trickiest — it
involves picking a specific residue class at each prime that's missing from
the admissible witness's residue image. The choice is via classical
`Classical.choose` on a non-empty witness-set, then proving the choice
satisfies the recursive precondition. ~50–100 lines for this step alone.

---

## §10. S12 deliverable scope

**Goal**: Discharge `engelsmaSearch 246 50 = false` via the pruned variant
and apply the S9 bridge.

**File changes**:
* `BoundedPrimeGapsOQ03OQ02.lean`: +20–40 lines.
  - `theorem engelsmaSearchPruned_50_246 : engelsmaSearchPruned 246 50 = false := by native_decide`
  - `theorem engelsmaSearch_50_246 : engelsmaSearch 246 50 = false :=
       (engelsmaSearchPruned_eq_engelsmaSearch 246 50).symm.trans engelsmaSearchPruned_50_246`
  - `theorem engelsma_lower_bound_proved :
       ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
       ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne :=
     engelsma_lower_bound_of_engelsmaSearch_false engelsmaSearch_50_246`

**Build risk**: dominated by `native_decide` runtime at `(50, 246)`. Per
`knowledge.md` §4.5 and §6.4, the estimate is 10–60 s for Option A (Array)
and 30–180 s for Option L (List). If even Option L's `native_decide` takes
>10 minutes (CI hard timeout), upgrade to Option A and rerun. Worst case:
fall back to Path C-prime (axiom stays; gallery contributes only the
decidability instance + bridge — already done in S2/S8).

**At completion**: `engelsma_lower_bound` axiom in
`BoundedPrimeGapsOQ03.lean` can be deleted and replaced by
`engelsma_lower_bound_proved`. axiomCount drops from 1 (the unrelated
`Lean.ofReduceBool` we picked up in S4) to whatever the rest of the slug
contributes. Honest reporting: we've replaced one mathematical axiom with
one foundational Lean axiom (`Lean.ofReduceBool`), which is the standard
trade for `native_decide`-based formalizations.

---

## §11. Risk register

| # | Risk | Likelihood | Mitigation |
|---|------|------------|------------|
| 1 | Option F runtime is too slow at `(50, 246)` even with pruning | Medium | Implement Option L from the start; fall back to A if needed. |
| 2 | `searchAux_complete` proof is brittle (classical choice + invariant) | Medium | Decompose into `searchAux_complete_aux` (single-prime step) lemmas. ~6 sub-lemmas. |
| 3 | `native_decide` at `(50, 246)` exceeds CI timeout | Low-Medium | Profile at `(10, 30)` first; if it takes >10 s, project ratios and reconsider. |
| 4 | The pruning logic disagrees with the spec on edge cases (e.g., k=0) | Low | Unit tests on `(0, 0)`, `(1, 1)`, `(2, 3)`, `(6, 16)` before any `(50, 246)` attempt. |
| 5 | Termination of `searchAux` requires explicit `termination_by` Lean can't infer | Medium | Acceptable cost (~5 lines); use `primes.length` directly if `candidates.length` doesn't decrease in the cardinality short-circuit branch. |
| 6 | Bridge lemma between Lean's `List.filter` and `Finset.filter` is more painful than expected | Low | Mathlib has `List.toFinset_filter` and friends; the pattern is well-trodden. |

---

## §12. Comparison to in-flight PR #18218 (S9)

PR #18218 is **complementary**, not competing. S9 establishes the surface
contract `engelsmaSearch_eq_false_iff` that S10's pruned variant plugs into.
S10's correctness equation `engelsmaSearchPruned_eq_engelsmaSearch` is a
*new* statement on top of S9's API — it does not modify or invalidate
anything S9 lands.

If PR #18218 is merged before S10 starts: S10 imports the API directly. No
rebase friction.

If PR #18218 is *not* merged before S10 starts: S10 must inline a temporary
version of `engelsmaSearch_eq_false_iff`'s consequence (~10 lines), then
remove the duplication once S9 lands. Manageable.

This S10-prep document itself touches only the (new) `sessions/` directory
and is conflict-free with PR #18218's `BoundedPrimeGapsOQ03OQ02.lean` +
`state.md` + `json` edits.

---

## §13. Open questions for the S10 author

1. Should `primesUpTo` be a `List ℕ` or a `Array ℕ`? `List` integrates better
   with structural induction proofs; `Array` is marginally faster but
   irrelevant at our scale.
2. Should `searchAux` be `partial def` or a `def` with explicit
   `termination_by`? The latter is required for `decide`/`native_decide` to
   reduce; `partial def` would not unfold. Use the explicit form.
3. Should `chosen` be `List ℕ` (in branch order) or `Finset ℕ`? List
   preserves construction order which simplifies some invariants; Finset
   matches the spec directly. Recommend `List`, convert to `Finset` only at
   leaves.
4. Is there value in caching `chosen.image (· % p)` as an `Array (Array Bool)`
   ("residue bitmap")? For (50, 246) probably yes; for unit tests no. Defer
   to S10's profiling.
5. The S9 PR mentions a positive unit test `engelsmaSearch_7_3_eq_true`. The
   pruned variant should have a matching `engelsmaSearchPruned_7_3_eq_true`
   to confirm forward agreement on the small-positive end too. Cost: 1 line +
   `native_decide`.

---

## §14. Summary

* S10 deliverable: `engelsmaSearchPruned` def + small-case unit tests
  reproducing S4/S5/S6 via the pruned variant. Build verifies via
  `native_decide`. ~120–180 lines. No new axioms.
* S11 deliverable: structural-induction correctness chain
  (`searchAux_sound`/`searchAux_complete`/`engelsmaSearchPruned_correct`).
  ~200–300 lines. No new axioms.
* S12 deliverable: discharge `engelsmaSearch 246 50 = false` via the
  pruned variant; apply S8/S9 bridges to replace `engelsma_lower_bound`
  axiom. ~20–40 lines + `native_decide` runtime budget.
* Total residual effort: 340–520 lines plus the empirical `(50, 246)`
  `native_decide` call. Aligned with `knowledge.md` §6.1's "500–1500 lines"
  estimate.
* Recommended runtime representation: Option L (List). Option F as a
  small-case throwaway; Option A as a profiling-driven upgrade.
* Branch order: small primes first.
* Correctness path: prune-then-bridge via `engelsmaSearchPruned_eq_engelsmaSearch`,
  not direct-from-existential — this minimizes friction with the S9 surface.

This document is a **planning artifact**. None of it commits the
implementation to specific code; all signatures are negotiable once S10
implementation begins. The intent is to flatten the surface area S10's
author has to reason about so the implementation phase is mechanical.

---

## §15. Honesty

- This is **infrastructure planning**, not mathematics. No new theorems are
  proved; no axioms are eliminated; no Lean code is touched. The value is
  in *reducing the design surface area* for the next 3 sessions.
- The line-count estimates (§4.5, §8, §9, §10) are based on similar
  certified-search patterns elsewhere in the gallery (`Mathlib.Data.Nat.Sieve`,
  the existing `engelsma50Tuple_admissible` proof, `BoundedPrimeGapsOQ04OQ01`'s
  Aristotle companion). They are **estimates**, not commitments — actual S10
  implementation may diverge.
- The recommendation of Option L over Option A is **provisional**. If S10's
  author has stronger evidence that Option F is fast enough at (50, 246)
  with pruning, that's a valid choice; if Option A's bridge lemma turns out
  to be 50 lines instead of 150, switch. The document fixes the *interfaces*
  (the §4 correctness API), not the *implementation*.
- Build verification: this document is markdown only. No `docker-build.sh`
  invocation is meaningful. Build status of the slug's Lean file is
  unaffected.
