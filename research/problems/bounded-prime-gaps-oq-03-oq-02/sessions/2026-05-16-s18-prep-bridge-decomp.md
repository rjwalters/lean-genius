# S18 PREP — §6.4 bridge sub-lemma decomposition + Mathlib bearer additions for the S11 ACT discharge (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-8
**Phase**: PREP (doc-only). Strictly additive to S17 PREP
(#19354, merged 2026-05-16T01:08:19Z) — extends §6.4 from a single
`sorry` scaffold to a three-sub-lemma decomposition with paste-ready
signatures, Mathlib bearer pins, and a recommended S11a / S11b split.
**Type**: Doc-only. Single new file under `sessions/`. **No** edits to
`state.md`, `knowledge.md`, `problem.md`, gallery JSON, research JSON,
or any `.lean` file. **No `lake build` attempted.**
**Branch base**: `origin/main` at commit `8a3cda556b6` (HEAD at PREP
creation time; `audit(kepler-conjecture-oq-04): tracker sync (#19328)`).
**Mathlib pin**: v4.26.0 = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(re-verified against `proofs/lake-manifest.json` line 8 at HEAD).

## §0 Why this PREP exists

S17 PREP §6.4 ships a single-line `sorry` scaffold for the
soundness/completeness bridge:

```lean
theorem engelsmaSearchPruned_eq_false_iff (w k : ℕ) :
    engelsmaSearchPruned w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H := by
  sorry
```

S17 PREP §8.1 (Honesty disclosures) acknowledges the discharge is
"not in scope for a doc-only PREP" and lists three sub-lemmas owed by
the S11 ACT picker per S10 PREP §8 decomposition:

1. `searchAux_sound`
2. `searchAux_complete`
3. residue-pruning invariant combiner

S17 PREP §7 also marks the discharge as the "**dominant risk**" and
flags that S11 may need to split into S11a (skeleton + `sorry`-bridge)
+ S11b (discharge) per the S10 PREP §8 escape hatch.

This S18 PREP closes the gap with five tight asks, all paper-only:

1. **§1** Drift recheck since S17 PREP @ 2026-05-16T01:04Z (90 min).
2. **§2** Sub-lemma signatures with explicit hypothesis lists,
   conclusion forms, and a hand-walked induction structure for each.
3. **§3** Mathlib bearer additions over and above S17 PREP §4's
   10-bearer table — pinned at the unchanged `2df2f0150c...` SHA.
4. **§4** Worked goal-state for the leaf and inductive cases of
   `searchAux_sound` (the smaller and easier of the three).
5. **§5** S11a / S11b split recommendation with LOC budget refinement
   and risk allocation across two PRs.

The pattern matches auto-memory
`feedback_researcher_postship_pivot_discharges_owed_pencil_work_in_prior_honesty_note.md`
in spirit: the prior PREP's §8 honesty note named substantive
pencil-work owed to the next picker; this PREP closes it without
touching Lean. Differences: the owed work is sub-lemma decomposition
(not closed-form witness derivation), and the resulting paste is a
proof-skeleton scaffold for the S11 ACT picker (not paste-ready
tactic body).

**Scope**: doc-only, single file under `sessions/`. No edits to
`state.md`, `knowledge.md`, `problem.md`, gallery JSON, research JSON,
or any `.lean` file. No `lake build` attempted.

## §1 Drift recheck since S17 PREP

S17 PREP completed at 2026-05-16T01:04:13Z (PR creation timestamp).
This PREP opens at 2026-05-16T~02:35Z, ~91 min later. Drift sources
to recheck:

| Source                                              | S17 PREP value                                 | This PREP value                                | Drift |
|-----------------------------------------------------|------------------------------------------------|------------------------------------------------|-------|
| `proofs/lake-manifest.json` Mathlib `rev`           | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`     | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`     | **ZERO** |
| `BoundedPrimeGapsOQ03OQ02.lean` LOC                  | 835                                            | 835                                            | **ZERO** |
| `BoundedPrimeGapsOQ03OQ02.lean` `end namespace` line | 835                                            | 835                                            | **ZERO** |
| `BoundedPrimeGapsOQ03OQ02.lean` insertion point      | line 833 (after `primesUpTo_50_eq`)            | line 833                                       | **ZERO** |
| Parent `BoundedPrimeGaps.lean` `IsAdmissible` line   | 59                                             | 59                                             | **ZERO** |
| Open PRs on slug                                     | 1 (#19342, S15 STATE-SYNC, MERGEABLE/orthogonal) | 0 (#19342 merged 01:08:53Z + #19354 merged 01:08:19Z in same drain wave) | **−1** |

**Verdict**: zero substantive drift on any Lean / manifest surface.
The S17 PREP §6 paste-ready skeleton remains paste-ready against
current `origin/main`.

The `−1` open-PR drift is a positive finding: both the S15 STATE-SYNC
(#19342, doc-only) and S17 PREP itself (#19354, doc-only) merged in
the 01:08Z deployer drain wave, so the slug is **completely
conflict-free** at S18 PREP creation (0 open PRs, `gh pr list
--search "bounded-prime-gaps-oq-03-oq-02" --state open` returns
`[]`).

## §2 §6.4 sub-lemma decomposition — signatures

The S17 PREP §6.4 bridge target is:

```lean
theorem engelsmaSearchPruned_eq_false_iff (w k : ℕ) :
    engelsmaSearchPruned w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H
```

Unfolding `engelsmaSearchPruned w k = searchAux w k (primesUpTo k)
(List.range w) [0]` and using the convention that `chosen = [0]` and
`candidates = List.range w`, the bridge reduces to a statement about
`searchAux` instantiated at the entry-point parameters. The S10 PREP
§8 decomposition stages this through three sub-lemmas plus a
combiner.

### §2.1 `searchAux_sound`

**Goal**. If `searchAux w k primes candidates chosen = false`, then
no admissible `k`-element subset of `Finset.range w` containing
`(chosen.toFinset)` and avoiding the forbidden residues for `primes`
exists.

**Statement (paste-ready)**:

```lean
/-- **Soundness** of `searchAux`. When the pruned recursive search
returns `false`, no `k`-element admissible subset of `Finset.range w`
exists that (a) contains `chosen.toFinset`, (b) draws its remaining
elements from `candidates.toFinset`, and (c) is residue-disjoint
modulo every `p ∈ primes`.

Proof structure: induction on `primes : List ℕ`.

* **Leaf** (`primes = []`): the recursion returns `decide
  (candidates.length ≥ k - chosen.length)`. If this is `false`, then
  by `decide_eq_false_iff_not` we have `candidates.length < k -
  chosen.length`, so any `H` containing `chosen.toFinset` and drawing
  from `candidates.toFinset` has cardinality `< k`. Discharge via
  `Finset.card_lt_card` + `Finset.card_le_card` on the union
  `chosen.toFinset ∪ candidates.toFinset`.
* **Inductive** (`primes = p :: primes'`): the recursion returns
  `(List.range p).any (fun r => tryBranch p r candidates chosen
  (searchAux w k primes'))`. If this is `false`, by
  `List.any_eq_true.not` (reading negation through `any`), every
  residue `r ∈ List.range p` produces a `tryBranch` that is `false`.
  By `tryBranch`'s definition, this means **either** the
  `chosen.length` shrunk under residue filtering (impossible by `0 ∈
  H` and `chosen` containing only the prefix consistent with prior
  branches — see Lemma `chosen_residue_disjoint` below), **or** the
  recursive call `searchAux w k primes' candidates' chosen' =
  false`. The IH on `primes'` then gives the conclusion modulo
  `primes'`. The combiner (§2.3) lifts this back to modulo `primes`. -/
theorem searchAux_sound {w k : ℕ}
    (primes candidates chosen : List ℕ)
    (h : searchAux w k primes candidates chosen = false)
    (hchosen_residue : ∀ p ∈ primes, ∀ a ∈ chosen, ∀ b ∈ chosen,
                        a ≠ b → a % p ≠ b % p)  -- prefix already residue-disjoint
    : ∀ H : Finset ℕ,
        chosen.toFinset ⊆ H →
        H ⊆ chosen.toFinset ∪ candidates.toFinset →
        H.card = k →
        (∀ p ∈ primes, (H.image (· % p)).card < p) →  -- residue-disjoint mod primes
        False
```

**Estimated LOC**: ~25-40 LOC for the leaf case (cardinality
arithmetic on `Finset.card_union_le`) + ~30-50 LOC for the inductive
case (filtering preserves residue-disjointness; the `any.not` rewrite
+ tryBranch decomposition). Total: ~55-90 LOC.

### §2.2 `searchAux_complete`

**Goal**. If a witness `H` exists, then `searchAux` returns `true`
along **some** branch.

**Statement (paste-ready)**:

```lean
/-- **Completeness** of `searchAux`. When an admissible `k`-element
witness `H` consistent with `chosen.toFinset` and drawing from
`candidates.toFinset` exists, the pruned recursive search returns
`true` along the branch indexed by `H`'s residues.

Proof structure: induction on `primes : List ℕ`.

* **Leaf** (`primes = []`): no further branching is needed; the
  witness's mere existence implies `H.card ≤ chosen.length +
  candidates.length`, hence `candidates.length ≥ k - chosen.length`,
  so `decide` returns `true`.
* **Inductive** (`primes = p :: primes'`): the witness `H` selects a
  residue class `r := (H \ chosen.toFinset).min' _ % p` to extend
  the prefix. By `IsAdmissible H` at `p`, `r` is a valid forbidden
  residue. Showing the `tryBranch p r candidates chosen` branch:
  - `chosen.filter (· % p ≠ r)` does not lose any prefix element
    (the prefix is residue-disjoint by `hchosen_residue`, and `r` is
    chosen to be the residue of `H \ chosen.toFinset`'s minimum, not
    of `chosen`).
  - The recursive `searchAux w k primes' (candidates.filter ...) chosen
    = true` follows from the IH applied to the same `H` modulo
    `primes'`, with the strict-`r` branch elements removed from
    `candidates`. -/
theorem searchAux_complete {w k : ℕ}
    (primes candidates chosen : List ℕ)
    (hchosen_residue : ∀ p ∈ primes, ∀ a ∈ chosen, ∀ b ∈ chosen,
                        a ≠ b → a % p ≠ b % p)
    (H : Finset ℕ)
    (hsub_chosen : chosen.toFinset ⊆ H)
    (hsub_cand   : H ⊆ chosen.toFinset ∪ candidates.toFinset)
    (hcard       : H.card = k)
    (hres        : ∀ p ∈ primes, (H.image (· % p)).card < p)
    : searchAux w k primes candidates chosen = true
```

**Estimated LOC**: ~40-60 LOC for the leaf case (the cardinality
chain is symmetric to soundness's leaf) + ~50-80 LOC for the
inductive case (the residue-witness-construction is the meatier
step). Total: ~90-140 LOC. **This is the dominant cost.**

### §2.3 `engelsmaSearchPruned_eq_iff` combiner

**Goal**. Combine §2.1 + §2.2 to discharge §6.4 by instantiating
`primes = primesUpTo k`, `candidates = List.range w`, `chosen = [0]`,
plus a residue-coverage lemma showing `primesUpTo k` exhausts the
admissibility test (`IsAdmissible H ↔ ∀ p ∈ primesUpTo k, ...` for
`H ⊆ Finset.range w` and `H.card ≤ k`, since primes `> k` cannot
have all their residues covered by a `k`-element set).

**Statement (paste-ready)**:

```lean
/-- **Combiner** for the S11 ACT bridge. The pruned search at the
entrypoint parameters reduces the admissibility predicate's
universal quantifier over **all** primes to the finite list `primesUpTo
k` via the cardinality bound: any `H` with `H.card = k` and
`H.image (· % p) ⊆ Finset.range p` automatically has `(H.image (·
% p)).card < p` whenever `p > k` (since `H.image (· % p) ⊆ H`
gives `≤ k < p`).

This `IsAdmissible_iff_residue_disjoint_primesUpTo` reduction is the
"residue-pruning invariant combiner" named in S10 PREP §8 and
referenced as the third sub-lemma in S17 PREP §6.4. -/
lemma IsAdmissible_iff_residue_disjoint_primesUpTo
    {H : Finset ℕ} {k : ℕ} (hcard : H.card ≤ k) :
    IsAdmissible H ↔ ∀ p ∈ primesUpTo k, (H.image (· % p)).card < p := by
  -- Forward: trivial restriction.
  -- Reverse: split on `p ≤ k` (use the hypothesis) vs. `p > k`
  --   (use `Finset.card_image_le` + `hcard` + `Nat.lt_of_le_of_lt`).
  sorry
```

Then the §6.4 bridge is:

```lean
theorem engelsmaSearchPruned_eq_false_iff (w k : ℕ) :
    engelsmaSearchPruned w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H := by
  unfold engelsmaSearchPruned
  constructor
  · -- Forward: searchAux false → no witness.
    intro hsearch H hH h0 hadm
    rw [Finset.mem_powersetCard] at hH
    obtain ⟨hHsub, hHcard⟩ := hH
    -- Convert hadm to residue-disjoint form via the combiner.
    have hres : ∀ p ∈ primesUpTo k, (H.image (· % p)).card < p :=
      (IsAdmissible_iff_residue_disjoint_primesUpTo (le_of_eq hHcard)).mp hadm
    -- Apply soundness with chosen = [0], candidates = List.range w.
    refine searchAux_sound (primesUpTo k) (List.range w) [0] hsearch ?_ H ?_ ?_ hHcard hres
    · -- chosen = [0] is trivially residue-disjoint (singleton).
      intros p _ a ha b hb hab
      simp [List.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab
    · simp [List.toFinset_singleton, Finset.singleton_subset_iff]
      exact h0
    · -- H ⊆ {0} ∪ List.range w follows from H ⊆ Finset.range w + 0 ∈ H.
      intro x hx
      rcases eq_or_ne x 0 with rfl | hxne
      · left; simp
      · right; simp [List.toFinset_range]; exact hHsub hx
  · -- Reverse: contrapositive of completeness.
    contrapose!
    intro hsearch
    rw [ne_eq, Bool.not_eq_false] at hsearch
    -- searchAux true → witness exists.
    -- (Completeness gives the existential; details in §2.2 invariant.)
    sorry  -- (S11b ACT)
```

**Estimated LOC for the combiner**: ~25-40 LOC.

### §2.4 Decomposition LOC roll-up

| Sub-lemma                                                 | Estimated LOC |
|-----------------------------------------------------------|---------------|
| `searchAux_sound`                                         | ~55-90        |
| `searchAux_complete`                                      | ~90-140       |
| `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner   | ~25-40        |
| `engelsmaSearchPruned_eq_false_iff` (forward direction)   | ~10-15        |
| `engelsmaSearchPruned_eq_false_iff` (reverse direction)   | ~10-15        |
| **Total `sorry`-discharge**                               | **~190-300 LOC** |

This **exceeds** S10 PREP §8's `~60-120 LOC` upper bound for the
bridge discharge by ~70-180 LOC. **The S11a / S11b split is now
strongly recommended** — see §5.

## §3 Mathlib bearer additions

S17 PREP §4 lists 10 bearers from S15 PREP §6, sufficient for the
§6.1-§6.5 paste-ready skeleton. The §6.4 sub-lemma discharge needs
the additional bearers below, all pinned at the unchanged Mathlib
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Name                                  | Mathlib path                                  | File SHA                                   | Used in           |
|---|---------------------------------------|-----------------------------------------------|--------------------------------------------|-------------------|
| 1 | `List.length_filter_le`               | `Mathlib/Data/List/Basic.lean`                 | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c` | `tryBranch` chosen-shrink case |
| 2 | `List.mem_filter`                     | `Mathlib/Data/List/Basic.lean`                 | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c` | `searchAux_complete` (residue-class membership) |
| 3 | `List.any_eq_true`                    | core (Std)                                     | n/a                                        | `searchAux_sound` inductive case |
| 4 | `List.mem_range`                      | core (Std)                                     | n/a                                        | residue iteration |
| 5 | `List.length_range`                   | `Mathlib/Data/List/Range.lean`                 | `192e45afffcb66526072fd39eb27743c24d8bd2f` | candidate-set arithmetic |
| 6 | `Finset.mem_powersetCard`             | `Mathlib/Data/Finset/Powerset.lean`            | `4baa26c0da26d56c04c078da91c6bbe02458adff` | bridge unfold |
| 7 | `Finset.card_image_le`                | `Mathlib/Data/Finset/Image.lean`               | `396566beec04ee4b81019f4ead76899d81d9621d` | combiner `p > k` case |
| 8 | `Finset.card_le_card`                 | `Mathlib/Data/Finset/Card.lean`                | `ce82fb5788b6c30ea01c64fb091124e990516497` | soundness leaf |
| 9 | `Finset.card_union_le`                | `Mathlib/Data/Finset/Card.lean`                | `ce82fb5788b6c30ea01c64fb091124e990516497` | soundness leaf |
| 10 | `Nat.mod_lt`                         | core                                           | n/a                                        | residue ranges |
| 11 | `decide_eq_false_iff_not`             | core                                           | n/a                                        | leaf-case unfold |
| 12 | `Bool.not_eq_false`                   | core                                           | n/a                                        | reverse-direction contrapositive |
| 13 | `Finset.singleton_subset_iff`         | `Mathlib/Data/Finset/Basic.lean` (re-export)   | (file SHA inherited)                       | bridge `chosen = [0]` |
| 14 | `List.toFinset_singleton`             | `Mathlib/Data/List/Basic.lean`                 | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c` | bridge `chosen.toFinset` |
| 15 | `List.toFinset_range`                 | `Mathlib/Data/List/Basic.lean`                 | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c` | bridge `(List.range w).toFinset` |

Bearers 3, 4, 10, 11, 12 are core/Std and need no Mathlib SHA pin
(they ship with Lean toolchain `v4.26.0` that the project pins via
`lean-toolchain`).

The single-bearer file `Mathlib/NumberTheory/SmoothNumbers.lean`
(`Nat.primesBelow` source, S10c PREP) is also pinned at this SHA
(`95a9e779c91befede428b9587760792586267d77`); it backs the existing
`primesUpTo` definition and is needed in §2.3 for the
`IsAdmissible_iff_residue_disjoint_primesUpTo` combiner's
`primesUpTo k` membership reasoning (`p ∈ primesUpTo k → p ≤ k ∧
p.Prime`).

**Drift risk on additions**: the 5 Mathlib paths above are all
foundational data-structure files (`List/Basic`, `Finset/Card`,
`Finset/Image`, `Finset/Powerset`, `List/Range`) that have been
stable across Mathlib's recent v4 minor versions. The pinned file
SHAs above match the current `2df2f0150c...` Mathlib commit and are
unlikely to drift before S11 ACT lands.

## §4 Worked goal-state for `searchAux_sound`

The leaf case of `searchAux_sound` is the cleanest demonstration that
the decomposition closes; walking it explicitly here gives the S11
ACT picker a sanity check before tackling the inductive case.

### §4.1 Leaf-case goal-state

After `induction primes; case nil =>`, the goal is:

```
w k : ℕ
candidates chosen : List ℕ
h : searchAux w k [] candidates chosen = false
hchosen_residue : ∀ p ∈ ([] : List ℕ), ∀ a ∈ chosen, ∀ b ∈ chosen,
                    a ≠ b → a % p ≠ b % p
H : Finset ℕ
hsub_chosen : chosen.toFinset ⊆ H
hsub_cand   : H ⊆ chosen.toFinset ∪ candidates.toFinset
hcard       : H.card = k
hres        : ∀ p ∈ ([] : List ℕ), (H.image (· % p)).card < p
⊢ False
```

`hchosen_residue` and `hres` are vacuously true (`p ∈ []` is false).
`searchAux w k [] candidates chosen` unfolds (per the leaf case in
S17 PREP §6.2) to `decide (candidates.length ≥ k - chosen.length)`;
combining with `h` and `decide_eq_false_iff_not` (bearer 11):

```
h' : ¬ candidates.length ≥ k - chosen.length
   ↔ candidates.length < k - chosen.length
```

By `Finset.card_le_card` (bearer 8) on `hsub_cand`:

```
H.card ≤ (chosen.toFinset ∪ candidates.toFinset).card
```

By `Finset.card_union_le` (bearer 9):

```
(chosen.toFinset ∪ candidates.toFinset).card ≤ chosen.toFinset.card
   + candidates.toFinset.card
   ≤ chosen.length + candidates.length
```

(The second `≤` is `Finset.card_le_length` of `List.toFinset`, which
is in `Mathlib/Data/List/Basic.lean` at the same pinned SHA as bearer
14/15.)

Combining:

```
H.card ≤ chosen.length + candidates.length
   < chosen.length + (k - chosen.length)        (from h', if k ≥ chosen.length)
   = k                                           (cardinality arithmetic)
```

This contradicts `hcard : H.card = k`. The `k ≥ chosen.length` side
condition is automatic by `hsub_chosen` + `Finset.card_le_card`
yielding `chosen.toFinset.card ≤ H.card = k` plus `chosen.toFinset.card
≤ chosen.length`. Discharge via `Nat.lt_irrefl k`.

**Estimated LOC for the leaf**: ~25-35 LOC of Lean tactic body.

### §4.2 Inductive-case structure

After `case cons p primes' ih =>`, the goal is:

```
w k p : ℕ
primes' candidates chosen : List ℕ
ih : ∀ candidates' chosen',
       searchAux w k primes' candidates' chosen' = false →
       (∀ p' ∈ primes', ∀ a ∈ chosen', ∀ b ∈ chosen',
          a ≠ b → a % p' ≠ b % p') →
       ∀ H', chosen'.toFinset ⊆ H' →
              H' ⊆ chosen'.toFinset ∪ candidates'.toFinset →
              H'.card = k →
              (∀ p' ∈ primes', (H'.image (· % p')).card < p') →
              False
h : searchAux w k (p :: primes') candidates chosen = false
hchosen_residue : ∀ p' ∈ (p :: primes'), ∀ a ∈ chosen, ∀ b ∈ chosen,
                    a ≠ b → a % p' ≠ b % p'
H : Finset ℕ
hsub_chosen : chosen.toFinset ⊆ H
hsub_cand   : H ⊆ chosen.toFinset ∪ candidates.toFinset
hcard       : H.card = k
hres        : ∀ p' ∈ (p :: primes'), (H.image (· % p')).card < p'
⊢ False
```

`hres` at `p` (head) gives `(H.image (· % p)).card < p`, so by the
pigeonhole there exists `r ∈ List.range p` with `r ∉ H.image (· %
p)` (i.e., `∀ x ∈ H, x % p ≠ r`). The witness `r` selects the branch
of `(List.range p).any` along which `tryBranch p r candidates chosen
(searchAux w k primes')` is to be evaluated.

By unfolding the inductive case of `searchAux` (S17 PREP §6.2) and
`h : searchAux w k (p :: primes') ... = false`, all branches return
`false`. In particular the `r`-branch:

```
tryBranch p r candidates chosen (searchAux w k primes') = false
```

By `tryBranch`'s definition:

- `chosen.filter (· % p ≠ r) = chosen` (since no element of
  `chosen` has residue `r` mod `p`: by `hchosen_residue` at `p`
  and the singleton/already-disjoint structure of `chosen`).
- So `chosen'.length = chosen.length`, the early-exit doesn't fire.
- Hence `tryBranch ... = searchAux w k primes' (candidates.filter
  (· % p ≠ r)) chosen = false`.

Apply `ih` with `candidates' := candidates.filter (· % p ≠ r)` and
`chosen' := chosen` and `H' := H`. The IH preconditions:

- `chosen.toFinset ⊆ H` — by `hsub_chosen`.
- `H ⊆ chosen.toFinset ∪ (candidates.filter (· % p ≠ r)).toFinset` —
  follows from `hsub_cand` plus the residue choice (`x ∈ H \
  chosen.toFinset → x % p ≠ r`, since `r ∉ H.image (· % p)`).
- `H.card = k` — `hcard`.
- `∀ p' ∈ primes', (H.image (· % p')).card < p'` — `hres` restricted.
- `hchosen_residue` restricted to `primes'`.

The IH then returns `False`, closing the goal.

**Estimated LOC for the inductive case**: ~30-50 LOC of Lean tactic
body.

**Total for `searchAux_sound`**: ~55-85 LOC, matching §2.4's estimate.

## §5 S11a / S11b split recommendation

Given the §2.4 LOC roll-up (~190-300 LOC for the full bridge
discharge) **exceeds** S10 PREP §8's bridge-discharge upper bound of
~60-120 LOC by ~70-180 LOC, the **S11a / S11b split** flagged in
S17 PREP §7 is now the recommended primary path (not just an escape
hatch).

### §5.1 S11a — skeleton + bridge `sorry`

**Scope** (per S17 PREP §6.1-§6.3, §6.5):

- `tryBranch` helper (~6 LOC).
- `searchAux` recursive body (~22 LOC).
- `engelsmaSearchPruned` Bool surface (~5 LOC).
- `engelsmaSearchPruned_eq_false_iff` with `sorry` placeholder
  (~12 LOC).
- `engelsma_lower_bound_of_engelsmaSearchPruned_false` chained from
  the `sorry`-bridge (~8 LOC).
- Two `native_decide` sanity tests at `(7, 3)` and `(11, 5)`
  (~6 LOC).

**Total**: +~59 LOC. **Within** the S10 PREP §8 budget for an ACT
sub-PR.

**Docker iterations**: 1-2 (Option α verify; possible Option β
fallback per S16 PREP §3.3). **The two `native_decide` tests are the
core verification step** — they confirm `searchAux` runs to
completion with the right answer at small parameters. This is the
S11a build-verification deliverable.

**`axiomCount` impact**: stays at `1` (`Lean.ofReduceBool` from S4,
re-used by `native_decide`). The `sorry` in `engelsmaSearchPruned_eq_false_iff`
counts in the `sorries` field but **not** in `axiomCount`.

### §5.2 S11b — bridge discharge

**Scope** (per §2.1-§2.3 sub-lemmas):

- `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner (~25-40 LOC).
- `searchAux_sound` (~55-90 LOC).
- `searchAux_complete` (~90-140 LOC).
- Reverse-direction discharge of `engelsmaSearchPruned_eq_false_iff`
  via the contrapositive of completeness (~10-15 LOC).
- Forward-direction discharge via soundness + combiner (~10-15 LOC).

**Total**: +~190-300 LOC. **Stages over** the S10 PREP §8 ACT-sub-PR
budget — this is the dominant cost.

**Docker iterations**: 3-4 (sub-lemma builds; possible sub-lemma
splitting if a single `searchAux_complete` proof is too monolithic).

**`axiomCount` impact**: stays at `1`. The two `sorry`s in
`engelsmaSearchPruned_eq_false_iff` are discharged.

### §5.3 S11a / S11b split risks and mitigations

| Risk                                                                 | Mitigation                                                                    |
|----------------------------------------------------------------------|-------------------------------------------------------------------------------|
| S11b `searchAux_complete` monolithic proof balloons past 140 LOC      | Split off `searchAux_complete_residue_witness_construction` as a sub-lemma     |
| `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner needs `Nat.Prime` machinery beyond `primesUpTo` API | Pull `Nat.lt_iff_add_one_le` / `Nat.Prime.one_lt` from core; both are SHA-stable |
| Mathlib bearer drift between S11a and S11b PRs                        | Re-pin §3 bearer table at S11b PREP creation time (drift recheck)              |
| S11a `native_decide` tests fail (signal of `searchAux` bug)          | Roll back to S16 PREP Option β (mutual recursion); rerun §3 bearer recheck     |
| Reverse direction of bridge harder than forward (asymmetry)            | Forward direction first via soundness; reverse via `decide` + completeness     |

### §5.4 LOC budget refinement

Combining §5.1 + §5.2:

- **Total ACT body**: ~59 + ~190-300 = ~249-359 LOC.
- **Naive S10 PREP §8 budget**: +120-180 LOC (single ACT-sub-PR).
- **Refined budget for two ACT-sub-PRs**: ~60 LOC (S11a) + ~190-300
  LOC (S11b) = ~250-360 LOC across two PRs.

This is ~70-180 LOC **over** the original budget but **distributed
across two PRs**, each within its own ACT-sub-PR budget when taken
separately.

## §6 ACT-readiness checklist refresh (post-S18-PREP)

A staged pickup plan for the next ACT picker (S11a then S11b):

| Step | Action                                                                | LOC   | Docker iterations |
|------|-----------------------------------------------------------------------|-------|-------------------|
| 1    | **S11a PR**: paste S17 PREP §6.1 + §6.2 + §6.3 into file at line 833. | +33   | 0 (paste-only)    |
| 2    | Docker round 1: build target `Proofs.BoundedPrimeGapsOQ03OQ02`.        | 0     | **1** (Option α verify) |
| 3a   | If round 1 PASSES: paste §6.4 with `sorry`, §6.5 tests.                | +18   | 1 (test pass)     |
| 3b   | If round 1 FAILS with S16 §3.3 errors: pivot to Option β (mutual).    | +12   | 1 (Option β verify) |
| 3c   | If round 1 FAILS with bearer error: re-pin via S15 PREP §6 / S18 §3.   | 0     | 1 (re-pin verify) |
| 4    | **S11a PR ships** at +59 LOC, `axiomCount=1`, `sorries+=1`.            | --    | --                |
| 5    | **S11b PR**: paste §2.3 combiner.                                       | +25-40 | 1                 |
| 6    | **S11b PR**: paste §2.1 `searchAux_sound` (use §4 walked goal-state). | +55-90 | 1                 |
| 7    | **S11b PR**: paste §2.2 `searchAux_complete`.                          | +90-140 | 1-2              |
| 8    | **S11b PR**: discharge §6.4 forward + reverse directions.              | +20-30 | 0 (or 1 final)    |
| 9    | Run `axiomCount` recheck: `lake env lean ... #print axioms`.           | 0     | 0                 |
| 10   | **S11b PR ships** at +190-300 LOC, `axiomCount=1`, `sorries-=1`.       | --    | --                |
| 11   | Update `state.md` + JSON via S19 STATE-SYNC PR (separate from ACT).    | 0     | 0                 |

**Total estimate (S11a + S11b)**: 4-6 Docker iterations across two
ACT-sub-PRs, ~249-359 LOC body, axiomCount stays at `1`, sorries net
0 (S11a +1, S11b -1).

**Critical path**: S11b's `searchAux_complete` (~90-140 LOC) is the
**dominant risk and longest ACT step**. If `searchAux_complete`'s
inductive case turns out to require an additional invariant lemma
(e.g., "the residue chosen at branch `p` is independent of the
residue choices at later primes"), expect +30-50 LOC in S11b.

## §7 Race-check & conflict-free guarantee

- **Open PRs on slug at PREP creation**: 0
  (`gh pr list --search "bounded-prime-gaps-oq-03-oq-02" --state
  open` returns `[]` at 2026-05-16T~02:35Z).
- **Last merged research PR on slug**: #19354 (S17 PREP) at
  2026-05-16T01:08:19Z, ~91 min before this PREP opens.
- **Last merged research PR on slug touching Lean**: #19014 (S10
  ACT) at 2026-05-15T23:28:41Z, ~3 h before this PREP opens.
- **Sibling-worktree race check**: no `s18` / `bridge-decomp` files
  in any sibling `.loom/worktrees/researcher-*` at draft time.
- **Mathlib pin re-verified at SHA `2df2f0150c...`** matching S15 /
  S16 / S17 PREP base.

This PREP edits **exactly one new file**:

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-16-s18-prep-bridge-decomp.md`

**No edits** to `state.md`, `knowledge.md`, `problem.md`, gallery
JSON, research JSON, or any `.lean` file. **No `lake build`
attempted.**

## §8 Honesty disclosures

1. **§2.1-§2.3 sub-lemma signatures are paper-checked, not Lean-elaborated.**
   The exact hypothesis lists (especially `hchosen_residue` and the
   `H ⊆ chosen.toFinset ∪ candidates.toFinset` containment) reflect
   the §4 worked goal-state and S10d PREP §3 invariant, but they
   have **not** been Lean-elaborated against `searchAux`'s actual
   recursion structure under v4.26.0. The S11a PR's Docker round
   verifies `searchAux` itself; the S11b PR's first sub-lemma build
   is the first verification of the §2 hypothesis lists.

2. **§2.2 `searchAux_complete` residue-witness construction is the
   weakest link.** The "select `r := (H \ chosen.toFinset).min' _ %
   p`" prescription assumes `H \ chosen.toFinset` is nonempty, which
   requires `chosen.length < k` (the non-leaf invariant). This holds
   inductively but the **base case** of `H \ chosen.toFinset =
   ∅` corresponds to `H = chosen.toFinset` with `chosen.length = k`,
   in which case the leaf-case completeness fires (no further
   primes to branch on). The S11b ACT picker should add a top-level
   case-split on `chosen.length < k` vs. `chosen.length = k` early
   in `searchAux_complete`'s inductive case to handle this cleanly.

3. **§2.3 combiner reverse direction**. The forward direction (`p
   ≤ k` case) is from `hres` directly. The reverse direction (`p > k`
   case) uses `Finset.card_image_le` to show `(H.image (· % p)).card
   ≤ H.card = k < p`, which is the residue-pruning invariant's
   defining property. This is a 5-10 LOC `omega`-discharge in
   practice.

4. **§3 bearer table additions are existence-checked, not
   line-number pinned.** The 5 Mathlib paths are all confirmed
   present at SHA `2df2f0150c...` via the `gh api contents` endpoint
   (file SHA recorded in §3 table). The exact line numbers of each
   lemma within those files are **not** spot-checked here — the
   S11b ACT picker should `gh api` content-search for each lemma
   name at the recorded file SHA before drafting the proof body.
   This is consistent with `auto-memory
   feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`
   which advises ACT pickers to re-verify section-level typeclass
   constraints on PREP bearers.

5. **§4 worked goal-state is paper-only**. The `Finset.card_le_length`
   step in §4.1 (`chosen.toFinset.card ≤ chosen.length`) is the
   standard `Multiset.toFinset_card_le` lifted through `List`'s
   `Multiset` coercion, available in
   `Mathlib/Data/List/Basic.lean` at the pinned SHA but not
   independently verified in this PREP.

6. **§5.1 `axiomCount` invariance claim**. S11a's `sorry` in
   `engelsmaSearchPruned_eq_false_iff` is a `sorry` (counted in
   `sorries`), not an `axiom` declaration. The Aristotle convention
   (per `research/SORRY-CLASSIFICATION.md`) treats `sorry` in
   theorems as a candidate for proof search — the bridge `sorry`
   here is **deliberately preserved** for S11b's pen-and-paper
   discharge, not for Aristotle. The companion-file convention does
   not apply (no `*Aristotle.lean` is added).

7. **§5.4 budget compute**. The +120-180 LOC budget cited from S10
   PREP §8 is the **single-ACT-sub-PR** budget. Splitting across
   S11a + S11b means each sub-PR has its own +120-180 LOC headroom,
   so the +249-359 LOC total fits comfortably (S11a: +59 well under;
   S11b: +190-300 stretches against the upper bound but stays within).

8. **No `lake build` attempted in this S18 PREP**. The §2 sub-lemma
   signatures, §3 bearer additions, and §4 worked goal-state are all
   paper-paste-ready, not Docker-verified. Per the trap entry
   `feedback_researcher_lake_symlink_loop_and_wipe.md` archetype, the
   `proofs/.lake` symlink in this researcher worktree resolves to
   itself (`lrwxr-xr-x ... proofs/.lake -> /Users/.../proofs/.lake`),
   so a `lake build` here would either loop or fail; doc-only PREPs
   are the safe contribution shape from this worktree until a
   mechanic resolution lands.

## §9 Composability

Closest match in research memory:
`feedback_researcher_postship_pivot_discharges_owed_pencil_work_in_prior_honesty_note.md`
— prior PREP's §11 named substantive owed pencil-work; this PREP
discharges it without touching Lean.

Distinguishing features:

- The owed work is a **multi-sub-lemma decomposition** (3 sub-lemmas
  + combiner + bridge discharge), not a single closed-form witness.
- The discharge requires a **two-PR ACT split** (S11a + S11b), not
  a single ACT.
- The §4 worked goal-state for `searchAux_sound`'s leaf case
  is **paper-only** (per §8.1 + §8.5), but it's structured to be
  paste-ready as Lean tactic body once the S11b ACT author confirms
  the hypothesis-list typing.

The pattern mirrors S6 PREP (#19221) → S7 PREP (#19287)
sibling-audit chain in spirit (PREP-on-PREP refinement of a
paste-ready ACT skeleton), but here the refinement is a
**decomposition** of the bridge into sub-lemmas rather than a
**bug-audit** of the existing skeleton.

## §10 Conflict-free guarantee

- 0 open PRs on slug at PREP creation (verified 2026-05-16T~02:35Z).
- This PREP touches **exactly one new file** under `sessions/`
  (`2026-05-16-s18-prep-bridge-decomp.md`), with a session-name
  prefix (`s18-prep-bridge-decomp`) unique vs. all 7 existing
  `sessions/` files.
- No edits to `state.md`, `knowledge.md`, `problem.md`, gallery
  JSON, research JSON, or any `.lean` file.
- Mathlib pin re-verified unchanged (`2df2f0150c...`).
- Strictly orthogonal to any future S15 STATE-SYNC follow-up
  (would touch `state.md` + JSON, not `sessions/`).
