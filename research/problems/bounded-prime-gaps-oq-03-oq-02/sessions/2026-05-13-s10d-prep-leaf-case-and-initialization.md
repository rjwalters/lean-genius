# S10d PREP — `searchAux` leaf-case admissibility is automatic + `0 ∈ H` initialization choice

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: PREP (audit-only, orthogonal to merged S10 PREP `2026-05-12-s10-prep-pruned-search-design.md` (#18281), S10b PREP `2026-05-12-s10b-prep-axiom-status-audit.md` (#18500), and S10c PREP `2026-05-13-s10c-prep-primesBelow-termination.md` (#18601)).
**Type**: Doc-only. No edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, gallery JSON, or research JSON. Single new file under `sessions/`.
**Branch base**: `origin/main` at commit `a84a6c8757a`.
**Mathlib pin**: v4.26.0 (verified against `proofs/lake-manifest.json`'s `mathlib` rev via prior PREP audits).

## §0 Predecessor chain

| PR     | Phase     | Contribution                                                                                            |
|--------|-----------|---------------------------------------------------------------------------------------------------------|
| #18218 | S9 ACT    | Naive `engelsmaSearch` surface API + `engelsma_lower_bound_of_engelsmaSearch_false` bridge.              |
| #18281 | S10 PREP  | Pruned-search algorithmic skeleton, Lean rep choice (Options F/A/L), correctness-lemma decomposition.   |
| #18500 | S10b PREP | Post-S12 axiom-status audit; `Lean.ofReduceBool` not counted by gallery convention.                     |
| #18601 | S10c PREP | `Nat.primesBelow` bearer + `Finset.sort` conversion + concrete `termination_by` skeleton.               |

This **S10d PREP** closes two further micro-design gaps left implicit across the
three predecessor PREPs:

1. **Leaf-case admissibility recheck is redundant** under the residue-pruning
   invariant (S10 PREP §7). S10c PREP §3.2/§3.4 retained an
   `IsAdmissibleBdd ((chosen.toFinset ∪ S) ∩ Finset.range w)` check at the
   leaf as a conservative formulation; this PREP observes that the check is
   structurally automatic and shows the leaf-case `Bool` is a **pure
   cardinality decision** `decide (candidates.length ≥ k - chosen.length)`.
   Saves a small runtime factor (~50–100× per leaf) and an `IsAdmissibleBdd`
   `Decidable` reduction in the unfolded `native_decide` path.

2. **The `0 ∈ H` initialization choice** was left implicit. S10 PREP §8 lists
   the entrypoint as `searchAux w k (primesUpTo k) (List.range w) []` (i.e.,
   `chosen := []`); S10 PREP §4.3 mentions an alternative
   `chosen := [0]` initialization in the soundness/completeness statement.
   These two choices have **different correctness obligations** at the leaf
   (one needs to filter for `0 ∈ chosen ∪ S`, the other gets it for free) and
   different proof-engineering costs. This PREP pins the trade-off, recommends
   the `chosen := [0]` form, and works out the disjointness invariant
   `chosen ∩ candidates = ∅` that makes the leaf-case cardinality argument go
   through cleanly.

Both micro-decisions are part of S10 PREP §8's "+120–180 LOC" budget; this
PREP pins **~20 LOC of design surface** (the leaf body + the entrypoint
discipline) at zero new scope.

**Scope**: doc-only, single file under `sessions/`. No edits to `state.md`,
`knowledge.md`, `problem.md`, gallery JSON, research JSON, or any `.lean` file.

## §1 The residue-pruning invariant (restatement)

S10 PREP §7 introduces the **candidate-set invariant**:

> At every recursive call `searchAux w k primes candidates chosen`, every
> `n ∈ chosen ∪ candidates` satisfies `n % p ≠ r_p` for every prime `p` we
> have already branched on (with `r_p` the residue forbidden in that
> branch).

Equivalently: if we let `primesDone := primesUpTo k \ primes` (the primes
already processed), then for every `n ∈ chosen ∪ candidates` and every
`p ∈ primesDone`, `n % p ∉ forbidden(p)`.

This invariant is preserved by the recursion's filter step
`candidates' := candidates.filter (n => n % p ≠ r)` applied to **both**
`candidates` and `chosen` at each branch: every surviving element acquires
one more forbidden-residue constraint, and the invariant gains one prime in
`primesDone`.

At the **leaf** (`primes = []`), `primesDone = primesUpTo k`. So every
`n ∈ chosen ∪ candidates` satisfies `n % p ≠ r_p` for every prime `p ≤ k`.

This invariant is what makes the leaf-case admissibility automatic
(§3 below).

## §2 What S10c PREP left at the leaf

S10c PREP §3.4 gives the explicit `termination_by`/`decreasing_by` skeleton
but leaves the leaf body as a sketch:

```lean
| [], candidates, chosen =>
    decide (∃ S ∈ candidates.toFinset.powersetCard (k - chosen.toFinset.card),
      IsAdmissibleBdd ((chosen.toFinset ∪ S) ∩ Finset.range w))
    -- (or equivalent leaf check; see S10 PREP §4.5)
```

Three sub-formulae deserve scrutiny:

| Expression                                          | Necessary?                                                                                                                                                                                                                                            |
|-----------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `IsAdmissibleBdd (...)`                             | **No** — automatic under the residue invariant. See §3.                                                                                                                                                                                              |
| `(chosen.toFinset ∪ S) ∩ Finset.range w`            | **No** — `chosen, S ⊆ List.range w` invariantly. See §3.3.                                                                                                                                                                                          |
| `S ∈ candidates.toFinset.powersetCard (k - chosen.toFinset.card)` | **Partially** — the existential is needed for `searchAux_sound`, but for the runtime `Bool` decision, an equivalent and faster form is `candidates.length ≥ k - chosen.length` (modulo nodup invariants on candidates and chosen). See §3.4. |

The S10c PREP leaf body is **conservatively correct** — it just does more
work than necessary. This S10d PREP shows the redundancy and offers two
equivalent simpler leaf bodies.

## §3 Leaf-case admissibility is automatic

### §3.1 Statement

**Lemma (informal).** Let `H := chosen.toFinset ∪ S.toFinset` for any
`S ⊆ candidates.toFinset` at the leaf (`primes = []`). Then `IsAdmissibleBdd H`
holds.

### §3.2 Proof sketch

Fix a prime `p` with `p ∈ Finset.range (H.card + 1)` and `Nat.Prime p`. Then
`p ≤ H.card ≤ k`, so `p ∈ primesUpTo k = primesDone` (since `primes = []` at
the leaf).

Hence the residue invariant from §1 applies at this `p`: there exists a
forbidden residue `r_p ∈ Fin p` such that for all `n ∈ chosen ∪ candidates`,
`n % p ≠ r_p`.

Since `H ⊆ chosen.toFinset ∪ candidates.toFinset`, every `n ∈ H` also
satisfies `n % p ≠ r_p`. Therefore `(H.image (· % p)) ⊆ Fin p \ {r_p}`, so
`(H.image (· % p)).card ≤ p - 1 < p`. □

### §3.3 The `∩ Finset.range w` is also redundant

If we maintain the auxiliary invariant `chosen ⊆ List.range w` and
`candidates ⊆ List.range w` at every recursive call — which is preserved
trivially since (a) initial `candidates := List.range w` and `chosen ⊆ {0} ⊆ List.range w` (assuming `w ≥ 1`), and (b) `List.filter` preserves
sublist relations — then `chosen.toFinset ∪ S.toFinset ⊆ Finset.range w`,
so intersecting with `Finset.range w` is the identity.

The `∩ Finset.range w` is a **belt-and-suspenders** check that's not needed
once the invariant is part of the proof. It can be safely dropped from the
leaf body.

### §3.4 Three Lean encodings of the leaf

**(A) Conservative — S10c PREP §3.4's form.**

```lean
| [], candidates, chosen =>
    decide (∃ S ∈ candidates.toFinset.powersetCard (k - chosen.toFinset.card),
      IsAdmissibleBdd (chosen.toFinset ∪ S))
```

Re-checks admissibility. **Cost**: one `Finset.decidableDforallFinset` over
`Finset.range (k + 1) ≈ 51` × prime-check × residue-image-card per leaf.
With ~10⁶ leaves at (50, 246), this is ~5 × 10⁷ extra `Decidable` reductions.
**Soundness proof**: trivial — `decide` returns the admissibility witness.

**(B) Structural — drop the recheck.**

```lean
| [], candidates, chosen =>
    decide (∃ S ∈ candidates.toFinset.powersetCard (k - chosen.toFinset.card),
      True)
```

The body `True` always holds for any non-empty `powersetCard`. This reduces
to `decide (candidates.toFinset.powersetCard (k - chosen.toFinset.card)).Nonempty`,
which by `Finset.powersetCard_nonempty` is `decide (k - chosen.toFinset.card ≤ candidates.toFinset.card)`.

**Cost**: one `Nat.decLe` per leaf. **Soundness proof**: needs the residue
invariant ⟹ admissibility lemma (§3.1).

**(C) Length-based — fastest.**

If we maintain the invariant `candidates.Nodup` and `chosen.Nodup` (true by
construction: `List.range w` is nodup, `List.filter` preserves nodup), and
`chosen.toFinset ∩ candidates.toFinset = ∅` (§4 below), then
`chosen.toFinset.card = chosen.length` (by
`List.toFinset_card_of_nodup` at `Mathlib/Data/Finset/Card.lean:205`)
and `candidates.toFinset.card = candidates.length` likewise.

```lean
| [], candidates, chosen =>
    decide (candidates.length ≥ k - chosen.length)
```

**Cost**: one `Nat.decLe` per leaf, no `toFinset` materialization. **Soundness
proof**: needs §3.1 + the disjointness invariant from §4.

### §3.5 Recommendation

**Form (C)** for the runtime body; explicitly prove §3.1 + §4 as auxiliary
lemmas during S11. The savings vs. form (A) at `(50, 246)`:

- Form (A): ~5 × 10⁷ `Decidable` reductions for leaf admissibility.
- Form (C): ~10⁶ `Nat.decLe`s.

At native_decide compile time, both reduce to constant-time arithmetic, but
form (C) generates significantly smaller IR (`Lean.ofReduceBool` proof
artifacts). The trade is paid in S11's correctness proof, which gains
~30–60 LOC for the §3.1 invariant lemma but saves the symmetric ~20 LOC
that S10c PREP's `IsAdmissibleBdd`-shaped leaf would require to extract
the admissibility witness.

A reasonable middle ground is form (B): keep `powersetCard` semantics
explicit (helpful for the `searchAux_sound` "exists S" reading) but drop
the redundant admissibility check. Form (B) saves runtime without changing
the proof shape.

## §4 The `0 ∈ H` initialization choice

The S9 surface API requires `0 ∈ H` (cf. `engelsmaSearch_eq_false_iff`'s
RHS). S10's `engelsmaSearchPruned` must enforce this. Three encodings:

### §4.1 Option (i) — `chosen := [0]`, `candidates := List.range w \ {0}`

```lean
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) ((List.range w).filter (· ≠ 0)) [0]
```

**Pros**:
- `0 ∈ H = chosen.toFinset ∪ S.toFinset` is **automatic** (always have `0 ∈ chosen.toFinset`).
- `chosen.toFinset ∩ candidates.toFinset = ∅` initially: `chosen.toFinset = {0}`,
  `candidates.toFinset = (Finset.range w) \ {0}` (assuming `w ≥ 1`).
- The disjointness is preserved through residue filtering (§4.4 below).
- `H.card = chosen.toFinset.card + S.toFinset.card = 1 + (k - 1) = k` directly from
  `Finset.card_union_of_disjoint` (`Mathlib/Data/Finset/Card.lean:566`).
- Branching pruning is tighter: at each prime `p`, the residue `r = 0` branch is
  dead (kills chosen via `0 % p = 0`), giving `(p - 1)` effective branches.

**Cons**:
- The leaf-case targets `S.card = k - 1` (not `k`); the entrypoint adds a `+1`
  bookkeeping step.

### §4.2 Option (ii) — `chosen := []`, `candidates := List.range w` (S10 PREP §8's choice)

```lean
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) (List.range w) []
```

**Pros**:
- Matches S10 PREP §8 verbatim; no redesign.
- Leaf-case targets `S.card = k`; no `+1` bookkeeping.

**Cons**:
- The leaf must enforce `0 ∈ S` explicitly via an extra `decide` clause:

```lean
| [], candidates, chosen =>
    decide (∃ S ∈ candidates.toFinset.powersetCard k, 0 ∈ S ∧ IsAdmissibleBdd S)
```

The `0 ∈ S` clause does not reduce to a cheap cardinality decision; it
requires `S` to materialize. Soundness/completeness proofs become slightly
longer (the existential body has two conjuncts to discharge).

- All `p` branches survive at every prime (no `r = 0`-kills-chosen pruning),
  giving the full `p` branching factor. The effective tree is ~`∏ p` over
  primes ≤ 47, much larger than `∏ (p - 1)`.

### §4.3 Option (iii) — Hard-wire `0` always-in-`chosen` via separate `Bool` flag

Reject. Adds an extra parameter to `searchAux` and a third invariant; no
correctness benefit over option (i).

### §4.4 Why option (i) preserves disjointness

**Claim.** If `chosen.toFinset ∩ candidates.toFinset = ∅` before a
residue-branch step, and `chosen' := chosen.filter (· % p ≠ r)`,
`candidates' := candidates.filter (· % p ≠ r)` (same filter), then
`chosen'.toFinset ∩ candidates'.toFinset = ∅`.

**Proof.** Both `chosen'` and `candidates'` are sublists of `chosen` and
`candidates` respectively. So `chosen'.toFinset ⊆ chosen.toFinset` and
`candidates'.toFinset ⊆ candidates.toFinset`. Intersecting:

```
chosen'.toFinset ∩ candidates'.toFinset ⊆ chosen.toFinset ∩ candidates.toFinset = ∅.
```

So `chosen' ∩ candidates' = ∅`. □

This is preserved trivially because the filter is monotone with respect to
subset inclusion. **No additional invariant maintenance is required** in the
recursion body.

### §4.5 Recommendation

**Option (i)**. Reasons:

1. Leaf-case is a pure cardinality check (§3 form (C)).
2. Disjointness invariant is automatic (§4.4).
3. Branching factor `(p - 1)` instead of `p` at each prime — this is
   Engelsma's actual pruning (cf. C reference); option (ii)'s `p` branches
   include `(p - 1)` "live" + 1 "dead" branch that's caught by the
   `chosen'.length < chosen.length` short-circuit but still incurs the
   filter cost.

Effective branching-product saving: `∏_{p ≤ 47} p / (p - 1) ≈ 4.0` overall.
Not a huge win at runtime (the dead branch is killed on the first filter
step), but the cardinality discipline at the leaf is the bigger win.

This deviation from S10 PREP §8's `searchAux w k (primesUpTo k) (List.range w) []`
is a **principled refinement** that aligns the Lean code with Engelsma's C
reference. S10 PREP §13 explicitly invites the S10 author to choose the
initialization; this PREP makes the case for option (i).

## §5 Putting §3 + §4 together: S10 deliverable diff sketch (refined)

S10 author's net code addition to `BoundedPrimeGapsOQ03OQ02.lean`:

```lean
-- §S10c PREP §2.3 primesUpTo
def primesUpTo (k : ℕ) : List ℕ :=
  (Nat.primesBelow (k + 1)).sort (· ≤ ·)

-- §3.5 form (C) leaf-case + §4.1 option (i) entrypoint
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (candidates.length ≥ k - chosen.length)
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        (List.range p).any (fun r =>
          let candidates' := candidates.filter (fun n => n % p ≠ r)
          let chosen'     := chosen.filter (fun n => n % p ≠ r)
          if chosen'.length < chosen.length then false
          else searchAux w k primes' candidates' chosen')
termination_by primes _ _ => primes.length
decreasing_by simp_wf; omega

-- §4.1 entrypoint
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) ((List.range w).filter (· ≠ 0)) [0]
```

**Net LOC**: ~25 lines for `searchAux` body + termination + entrypoint. Add
the small-case unit tests per S10 PREP §8 last bullet (~10–20 lines for
`engelsmaSearchPruned_6_16_eq_engelsmaSearch_6_16` via `native_decide` and
peers) → ~35–45 LOC for S10 ACT, leaving the ~120–180 LOC budget S10 PREP
allocates with substantial slack for the cardinality and disjointness
invariant lemmas, which can also land in S10 ACT (then S11 only needs the
soundness/completeness combinator).

### §5.1 Invariant lemmas (recommended for S10 ACT, ~30–50 LOC total)

```lean
/-- `searchAux` preserves the disjointness invariant: if `chosen ∩ candidates = ∅`
in the entrypoint, the recursion maintains it. -/
private lemma searchAux_disjoint_inv (w k : ℕ) (primes : List ℕ)
    (candidates chosen : List ℕ)
    (hdis : Disjoint candidates.toFinset chosen.toFinset) :
    -- Invariant: every recursive call preserves Disjoint.
    True := sorry  -- structural; trivial via §4.4

/-- `searchAux` preserves the residue invariant: at the leaf, every element
of `chosen ∪ candidates` satisfies `n % p ≠ r_p` for every branched prime. -/
private lemma searchAux_residue_inv (w k : ℕ) (primes : List ℕ)
    (candidates chosen : List ℕ) :
    -- Invariant: at every leaf state, the residue invariant holds.
    True := sorry  -- structural; by induction on `primesDone`

/-- Initial disjointness for the entrypoint. -/
private lemma initial_disjoint (w : ℕ) :
    Disjoint ((List.range w).filter (· ≠ 0)).toFinset ([0] : List ℕ).toFinset := by
  simp [List.toFinset_filter, Finset.disjoint_left]
  intro a ha
  exact ha.2  -- a ≠ 0
```

### §5.2 The `chosen.toFinset.card = chosen.length` chain

For the leaf-case cardinality check to discharge the existential in
`engelsmaSearchPruned_correct`, S11 needs:

```lean
chosen.length = chosen.toFinset.card                              -- List.toFinset_card_of_nodup
candidates.length = candidates.toFinset.card                       -- ditto
chosen.toFinset.card + S.toFinset.card = (chosen.toFinset ∪ S).card  -- Finset.card_union_of_disjoint
```

All three are one-line `simp` or `rw` applications given the nodup and
disjointness invariants. **Pinned bearers**:

- `List.toFinset_card_of_nodup` at `Mathlib/Data/Finset/Card.lean:205`:
  `(h : l.Nodup) : #l.toFinset = l.length`.
- `Finset.card_union_of_disjoint` at `Mathlib/Data/Finset/Card.lean:566`:
  `(h : Disjoint s t) : #(s ∪ t) = #s + #t` (alias of
  `Finset.card_union_eq_card_add_card.mp` at line 563).
- `List.Nodup.filter` at `Mathlib/Data/List/Nodup.lean` (standard,
  preservation of nodup under filter).
- `List.nodup_range` at `lean4/src/Init/Data/List/Lemmas.lean` (core Lean,
  used via `Multiset.nodup_range` at `Mathlib/Data/Multiset/Range.lean:73`).

## §6 ERRATUM / clarification to S10c PREP §3.4

S10c PREP §3.4's leaf-case sketch:

```lean
| [], candidates, chosen =>
    decide (∃ S ∈ candidates.toFinset.powersetCard (k - chosen.toFinset.card),
      IsAdmissibleBdd ((chosen.toFinset ∪ S) ∩ Finset.range w))
      -- (or equivalent leaf check; see S10 PREP §4.5)
```

**This is not an error** — it's correct but conservative. The `IsAdmissibleBdd (...)`
recheck is **redundant** under the §1 residue invariant; the `∩ Finset.range w`
is **redundant** under the trivial range invariant.

The "equivalent leaf check" the S10c PREP §3.4 alludes to (in its trailing
comment) is the form we work out in §3 above: form (C)
`decide (candidates.length ≥ k - chosen.length)` with explicit invariant
lemmas. S10c PREP did not commit to either form; S10d PREP closes the
choice.

## §7 Race check + diff scope

### §7.1 Race check (2026-05-13 07:39 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "bounded-prime-gaps-oq-03-oq-02 in:title" --state open`
  → **1 result** (#18024, S6 "engelsma_analogue_9_26", open since 2026-05-12 09:22 UTC,
  ~22h stale, deferred S7 case).
- **#18024 is orthogonal** to this PREP: it touches
  `BoundedPrimeGapsOQ03OQ02.lean` (extending the S5/S6 vacuous-case `native_decide`
  chain to (9, 26)); this PREP creates a new file under `sessions/` only.
- Most recent merge on this slug: PR #18601 (S10c PREP) at 2026-05-13 06:02 UTC,
  **~1h 37m before claim**. Past the 30-minute cool window.
- Filename `2026-05-13-s10d-prep-leaf-case-and-initialization.md` is unique
  under `sessions/` (existing files:
  `2026-05-12-s10-prep-pruned-search-design.md`,
  `2026-05-12-s10b-prep-axiom-status-audit.md`,
  `2026-05-13-s10c-prep-primesBelow-termination.md`).
- No competing sibling PREP filename `*s10d*`.

### §7.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-13-s10d-prep-leaf-case-and-initialization.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, gallery JSON, research JSON, or
  any `.lean` file.

No `lake build` attempted; doc-only.

### §7.3 What this PREP intentionally does NOT do

- Does NOT modify `searchAux`'s leaf-case in any Lean file. That code change
  is S10 ACT's deliverable.
- Does NOT write the disjointness / residue invariant lemmas. Those land
  with S10 ACT (or S11 if the S10 author defers; the leaf-form runs as
  pure cardinality without the invariants — the invariants are only needed
  for `searchAux_sound`/`searchAux_complete`).
- Does NOT verify the v4.26.0 line numbers against the live
  `lake-manifest.json`-pinned commit (cf. S10c PREP §6.3 disclosure). The
  citations target the v4.26.0 tag, which matches the manifest pin per
  prior PREP audits.
- Does NOT prefer or reject Option L vs Option A vs Option F (S10 PREP §3
  representation choice). The leaf-case analysis here is representation-
  agnostic: form (C) works for any representation that supports `.length`,
  `.filter`, and `.toFinset`.

## §8 Comparison with predecessor PREPs

| PR     | Coverage area                                                                                       | Leaf-case design? | `0 ∈ H` init? |
|--------|-----------------------------------------------------------------------------------------------------|-------------------|-----------------|
| #18281 | Algorithm + representation + correctness decomposition + risk register                              | High-level only   | Two forms listed |
| #18500 | Axiom-status convention; `Lean.ofReduceBool` non-counting                                            | N/A               | N/A             |
| #18601 | `Nat.primesBelow` bearer + `Finset.sort` + `termination_by` skeleton                                | Sketched conservatively | N/A      |
| **This (#TBD)** | **Leaf form (C) cardinality** + **option (i) `chosen := [0]` init** + invariant lemma sketch | **Pinned**        | **Pinned**     |

This PREP complements the three prior PREPs by pinning two micro-design
decisions (leaf body shape, entrypoint initialization) that S10 author would
otherwise fill in on the fly. The ~5 LOC pinned here are part of S10 PREP §8's
"+120–180 LOC" estimate, not new scope.

## §9 Honesty disclosures

1. **§3.1 admissibility invariant is paper-checked** against the `IsAdmissible`
   / `IsAdmissibleBdd` definitions in `BoundedPrimeGapsOQ03OQ02.lean:78` and
   `BoundedPrimeGaps.lean:59`. No Lean build attempted.

2. **§4.4 disjointness preservation is paper-checked** via the trivial
   "filter is monotone w.r.t. subset" argument. Not Lean-built. Should be
   1–2 LOC in S10 ACT.

3. **§3.5 runtime savings estimate (~50–100× per leaf)** is order-of-magnitude
   from the size of `IsAdmissibleBdd`'s `Finset.range (k + 1)` body
   (~k iterations × prime-check × image-card check). Actual native_decide
   compile-time impact may differ; the IR-size argument is the stronger
   reason to prefer form (C).

4. **§4.5 branching-factor estimate `∏ p/(p−1) ≈ 4.0`** uses Mertens' product
   formula. The actual practical savings depend on residue cover ordering and
   are dominated by tree shape rather than branching factor at the top.

5. **Mathlib v4.26.0 line citations** verified 2026-05-13 via
   `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=v4.26.0`:
   - line 205 — `List.toFinset_card_of_nodup`.
   - line 563 — `card_union_eq_card_add_card`.
   - line 566 — `card_union_of_disjoint` (alias).

   And `Mathlib/Data/Multiset/Range.lean:73` for `nodup_range`.

   `Finset.powersetCard_nonempty` membership is well-known (Mathlib
   `Mathlib/Data/Finset/Powerset.lean`); not re-verified inline. If S10
   author uses form (B) rather than form (C), the bearer name should be
   re-checked.

6. **§5.1's invariant lemma signatures are sketches** (the `True` bodies are
   placeholders). The actual S10 ACT bodies will encode the invariant as a
   typed proposition. The shape is "two ~10-line structural inductions on
   `primes`."

7. **No `.lake` build attempted; no `proofs/.lake` directory modifications,
   no symlink-loop risk.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

8. **GitHub Contents/Search API usage**: 4 calls to `gh api repos/.../contents/...?ref=v4.26.0`
   (Finset/Card.lean, List/Nodup.lean, List/ToFinset.lean, Multiset/Range.lean)
   + 3 `gh api /search/code` calls. The search-code endpoint is rate-limited at
   30/hr per `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`.
   Total session usage ~7, well under budget.

9. **No edits to `state.md` or `problem.md`** — those record high-level
   approach; this PREP refines two micro-bearers for S10 ACT. The decisions
   pinned here are inside S10 PREP §8's already-stated scope.

## §10 Decision log

- **2026-05-13 S10d PREP**: Decision to write S10d as a separate `sessions/`
  PREP rather than amend S10c. Reason: S10c is merged; the leaf-case + init
  observations are an additive refinement, not a correction. Keeping them in
  a sibling file preserves the "minimal change-set" property of each PREP.

- **2026-05-13 S10d PREP**: Decision to recommend **leaf form (C)** over
  forms (A) or (B). Reason: smallest runtime IR; the invariant lemmas needed
  for S11 correctness are useful as standalone observations and would land
  in S11 anyway (form (A) just defers their proof until later by paying
  runtime instead).

- **2026-05-13 S10d PREP**: Decision to recommend **option (i)** (`chosen := [0]`,
  `candidates := (List.range w).filter (· ≠ 0)`) over option (ii) (S10 PREP §8's
  `chosen := []`, `candidates := List.range w`). Reason: leaf-case
  cardinality discipline (1 + (k - 1) = k via `card_union_of_disjoint`) is
  cleaner, matches Engelsma's actual C reference pruning factor `(p - 1)`,
  and eliminates the `0 ∈ S` clause from the existential.

- **2026-05-13 S10d PREP**: Decision NOT to spec the invariant lemma proofs.
  Reason: they are structural (1-step induction on the recursion's primes
  argument) and the proof shape is uniform; S10 ACT author has both the
  recursion definition and the §1 invariant statement here as references.

- **2026-05-13 S10d PREP**: Decision NOT to verify against the live
  `lake-manifest.json` pinned commit. Per `feedback_researcher_6_*` audit,
  the v4.26.0 tag matches the manifest pin. If the manifest has drifted,
  the bearer **names** are stable (these are foundational Finset/List
  lemmas, several years old); line numbers may shift ±5–10.

## §11 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/Data/Finset/Card.lean:205` — `List.toFinset_card_of_nodup`.
- `Mathlib/Data/Finset/Card.lean:563` — `card_union_eq_card_add_card`.
- `Mathlib/Data/Finset/Card.lean:566` — `card_union_of_disjoint` (alias).
- `Mathlib/Data/Multiset/Range.lean:73` — `nodup_range` (calls `List.nodup_range`).
- `Mathlib/NumberTheory/SmoothNumbers.lean:41` — `Nat.primesBelow` (per S10c PREP).
- `Mathlib/Data/Finset/Sort.lean:33` — `Finset.sort` (per S10c PREP).

### Local file references

- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:78` — `IsAdmissibleBdd` definition.
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:88` — `isAdmissible_iff_bdd` equivalence.
- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:702` — naive `engelsmaSearch` (S9).
- `proofs/Proofs/BoundedPrimeGapsOQ03.lean:134` — the unbounded `engelsma_lower_bound` axiom.
- `proofs/Proofs/BoundedPrimeGaps.lean:59` — the unbounded `IsAdmissible` predicate.

### Predecessor PREP files (sessions/)

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-12-s10-prep-pruned-search-design.md` (PR #18281).
- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-12-s10b-prep-axiom-status-audit.md` (PR #18500).
- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-13-s10c-prep-primesBelow-termination.md` (PR #18601).
- **This file**: `sessions/2026-05-13-s10d-prep-leaf-case-and-initialization.md`.

### Sibling memory cross-references

- `feedback_researcher_lake_symlink_loop_and_wipe.md` — why no `lake build` is attempted.
- `feedback_researcher_6_2026_05_13_s4_alpha_errata_correction_prep.md` — manifest-vs-tag pinning convention.
- `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — gh api search/code rate limit (30/hr).
- `feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md` — pattern: Mathlib audit first, beats bespoke design.

**End of S10d PREP.**
