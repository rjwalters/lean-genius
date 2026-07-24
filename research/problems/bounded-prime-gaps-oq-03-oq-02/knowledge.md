# Knowledge — bounded-prime-gaps-oq-03-oq-02

## S23 STATE-SYNC + BLOCKED flag (2026-06-13, researcher-1)

Build-free audit of `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` at current
`origin/main` (HEAD `fb829e819f7`). Docker is down fleet-wide (verification
blackout), so no build this session.

**Actual file state (corrects stale tracker numbers):**
- **997 LOC** (tracker said 953; S11a PR #19519 is merged into origin/main).
- **Exactly 1 real `sorry`** — `engelsmaSearchPruned_eq_false_iff` at **line
  969** (tracker said line 925; the other "sorry" greps at 852/964 are
  docstring text). All other theorems are sorry-free.
- **0 literal `axiom` declarations** in this file (the `engelsma_lower_bound`
  axiom lives in the parent `BoundedPrimeGapsOQ03.lean`; this file aims to
  *discharge* it). The `native_decide` calls introduce the implicit
  `Lean.ofReduceBool` dependency, which is the "axiomCount = 1" the docstrings
  refer to. No structure-encoded assumptions.
- No gallery `meta.json` exists for this slug — it is research-only, so there
  is no published-counts audit to reconcile.

**Why BLOCKED.** The single remaining sorry is the crux bridge and needs the
full S11b decomposition (`searchAux_sound` + `searchAux_complete` + combiner,
estimated **+225–360 LOC** per S20 PREP §5). That work is gated on TWO
independent blockers right now:
1. **Infra:** Docker is down fleet-wide. Pasting +225–360 LOC of well-founded
   recursion soundness/completeness proofs that cannot be build-verified would
   be blind-shipping build-dependent ACT — explicitly disallowed.
2. **Churn:** sessions S17–S22 (~10 sessions) produced only doc-only PREP /
   STATE-SYNC memos circling this same sorry. Per the researcher role's
   "3+ sessions stuck on same sorry → flag BLOCKED, move on", this slug should
   stop being re-claimed for further PREP padding.

**Unblock path (unchanged, well-specified):** once Docker recovers, execute the
S11b α→β→γ→δ chain then S12 `native_decide`, exactly as `currentState.nextSteps`
documents (note: the §3.1-corrected residue witness
`(List.range p).filter (· ∉ H.image (· % p)) |>.head!` must be used, NOT the
S18 sketch which picks an existing rather than missing residue). No new PREP
memo is needed — the paste-ready skeletons already exist.

---

# (Below: original S1 survey — line/LOC references predate S11a and are stale.)

S1 OBSERVE pass. No Lean code written; this document is the survey + path menu.
Build status not changed.

## §1. Precise statement of the target

The axiom under attack is (`BoundedPrimeGapsOQ03.lean` line 134):

```lean
axiom engelsma_lower_bound :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, H.max' hne - H.min' hne ≥ 246
```

where (`BoundedPrimeGaps.lean` line 59):

```lean
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p
```

This is the Hardy-Littlewood admissibility condition: no small prime covers every residue
class of `H`. Equivalently, for every prime `p` there exists `r ∈ Fin p` with
`r ∉ H.image (· % p)`. The mathematical claim is then:

> The narrowest admissible 50-tuple has diameter ≥ 246, with witness `engelsma50Tuple`.

The achievability side is already proven in the file:

```lean
theorem admissible_50_tuple_diam_achieved :
    ∃ H : Finset ℕ, ∃ hne : H.Nonempty,
    IsAdmissible H ∧ H.card = 50 ∧ H.max' hne - H.min' hne = 246
```

So the missing half is the *lower bound* (no diameter < 246 is possible).

## §2. Reduction to a finite decidable problem

### §2.1 Translation invariance

If `H` is admissible and has minimum `m`, then `H' := H.image (· - m)` is admissible (the
shift map is a bijection on residues mod `p` for each `p`, so `H'.image (· % p) =
(H.image (· % p)).image (·.sub_mod p)` is a translate of the same set and has the same
cardinality). So we may assume `min H = 0`.

### §2.2 Cardinality and diameter constraint

If `max H - min H < 246` and `min H = 0`, then `H ⊆ {0, 1, …, 245} = Finset.range 246`.
Combined with `H.card ≥ 50`, the only configurations are subsets of `Fin 246` of
cardinality exactly 50 (anything larger requires diameter ≥ 246 by the same logic).

### §2.3 The decidable reformulation

The axiom is logically equivalent to:

$$
\forall H \in \binom{\{0,1,\ldots,245\}}{50},\ 0 \in H \implies \neg \mathrm{IsAdmissible}(H).
$$

In Lean syntax this is:

```lean
theorem engelsma_lower_bound_finitary :
    ∀ H ∈ (Finset.range 246).powersetCard 50,
      0 ∈ H → ¬ IsAdmissible H
```

This is a `∀ H : Finset (Fin 246)`-quantified statement over a *finite* set with
`Decidable` body (modulo a `Decidable (IsAdmissible H)` instance which we will need to
build — see §3.1).

### §2.4 The bridge lemma we will need

To finalize the axiom replacement after proving the finitary form, we need:

```lean
theorem engelsma_lower_bound_of_finitary
    (hfin : ∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H → ¬ IsAdmissible H) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, H.max' hne - H.min' hne ≥ 246
```

Proof sketch (S2/S3 work):

1. Argue by contradiction; suppose `H` admissible, `H.card ≥ 50`, `max - min < 246`.
2. Let `m := H.min' hne`. Define `H' := H.image (· - m)`. (Subtraction is truncated in `ℕ`,
   but since `m ≤ a` for all `a ∈ H`, the image is faithful: `Finset.image_sub_of_le`.)
3. `IsAdmissible H'` from `IsAdmissible H` by §2.1 (translation lemma — needs to be
   verified for `Finset.image (· - m)` — the residue-class translate is `((· - m) % p) =
   ((· % p) - (m % p)) % p` and `Finset.image_image` together with bijection of the
   residue translate finishes).
4. `H'.max' ≤ 245` since `H.max' - m = (max - min) ≤ 245`.
5. `H'.card = H.card ≥ 50` (image of injection has same cardinality; subtraction by a
   constant ≤ min is injective on `H` by `Finset.image_sub_inj_of_le`).
6. Take any 50-subset `H₀ ⊆ H'` containing 0 (which is `H'.min' = 0`): by §3.2 it is also
   admissible. Then `H₀ ∈ (Finset.range 246).powersetCard 50` and `0 ∈ H₀`.
7. Apply `hfin H₀` to conclude `¬ IsAdmissible H₀`, contradiction.

Approximately 50–100 lines of Lean once §3.1 lands. None of this is the hard part.

## §3. Decidability of admissibility

### §3.1 `Decidable (IsAdmissible H)` instance — required infrastructure

Currently no such instance exists in either this repo or Mathlib. The definition is:

```
IsAdmissible H := ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p
```

This is an unbounded `∀ p`, but in practice the only primes that can matter are
`p ≤ H.card`: if `p > H.card`, then `(H.image (· % p)).card ≤ H.card < p` is automatic.

**Reformulation**: define `IsAdmissibleBdd H := ∀ p ≤ H.card, Nat.Prime p →
(H.image (· % p)).card < p`. Then `IsAdmissible H ↔ IsAdmissibleBdd H` is a one-line lemma
splitting `p ≤ H.card` from `p > H.card` (the latter trivial by `card_image_le`).

`IsAdmissibleBdd H` is a `∀ p ∈ Finset.range (H.card + 1)`, which is decidable by
`Finset.decidableDforallFinset` once `Decidable (Nat.Prime p ∧ …)` is in place
(`Nat.decidablePrime` is in Mathlib). So:

```lean
instance : Decidable (IsAdmissible H) := decidable_of_iff (IsAdmissibleBdd H) …
```

**Verification effort**: ~40 lines, no novel tactics. Mathlib lemmas needed:

- `Nat.decidablePrime` (exists)
- `Finset.card_image_le` (exists)
- `Finset.decidableDforallFinset` (exists)
- A bridge `decidable_of_iff` chaining the two forms (1 line)

### §3.2 `native_decide` viability on direct enumeration (Path A)

Once §3.1 lands, the finitary statement

```lean
theorem engelsma_lower_bound_finitary :
    ∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H → ¬ IsAdmissible H
:= by native_decide
```

is mechanically decidable. The cost is:

- `Finset.powersetCard 50 (Finset.range 246)` has cardinality $\binom{246}{50} \approx 1.7
  \times 10^{54}$. Lean cannot enumerate this in any reasonable time, *and* the
  representation `Finset (Fin 246)` in Lean stores each subset as a sorted list — total
  memory ≥ $50 \cdot \binom{246}{50}$ bytes, far beyond physical RAM.
- Even with `Finset.toList`-style streaming (which `decide` does not do), the linear time
  is $\sim 10^{54}$ admissibility checks. Trillions of years.

**Conclusion**: Path A is *not* viable as a stand-alone strategy. It would only suit
extremely small cases (admissible 5-tuples with diameter < 16, etc.) and is useful here
only as a *unit-test scaffold* against which Path B's pruner can be cross-checked.

### §3.3 Smaller-case sanity native_decides

To stress-test §3.1 before committing to Path B, we can `native_decide` weaker statements
that ARE feasible:

- `∀ H ∈ (Finset.range 10).powersetCard 5, IsAdmissible H ∨ ¬ IsAdmissible H`
  — trivial, just exercises the instance.
- `∀ H ∈ (Finset.range 16).powersetCard 6, 0 ∈ H → IsAdmissible H → H.max' (?) ≥ 12`
  — actual small-case Engelsma analogue. $\binom{16}{6} = 8008$; tractable.
- The Engelsma 50-tuple itself: `IsAdmissible engelsma50Tuple` (already done in OQ-03,
  via case-split on small primes — confirms that the brute-force route works for *one*
  tuple but not for $10^{54}$ tuples).

## §4. Engelsma's pruning algorithm (Path B target)

### §4.1 Source

Thomas Engelsma, "Permissible patterns and prime gaps" (2013, unpublished, hosted at
opertech8.com). The relevant Polymath 8b writeup (Tao et al., 2014) describes the
algorithm at a high level; Sutherland's later refinements (2014–2015) give tighter
bounds. For OQ-03-OQ-02 we need only the *correctness* of Engelsma's algorithm at
parameters `k = 50, w = 246`.

### §4.2 Algorithmic skeleton

Inputs: target diameter `w`, target size `k`. Output: every admissible `k`-tuple of
diameter ≤ `w`, or a certificate that none exists.

```
function search(w, k):
    primes = [2, 3, 5, 7, 11, …] up to some cutoff (Engelsma used p ≤ 50)
    candidates = {0, 1, …, w}
    for each prime p in primes:
        # constraint propagation
        for each permitted residue r ∈ Fin p:
            S_{p,r} := {n ∈ candidates : n % p ≠ r}
            recurse with primes' = primes \ {p}, candidates' = S_{p,r}
    return enumerate (k-subsets of candidates) and filter for admissibility
```

The crucial fact is that for an admissible tuple, *for each prime p there must exist a
permitted r*. So branching on `r` at each prime gives a tree of $\prod_p p$ leaves, but
most branches prune very early. Engelsma reports the effective search tree has on the
order of $10^6$ leaves at `(50, 246)`.

### §4.3 Lean representation choice

The Lean implementation has to choose between:

1. **Recursive function with `decide` accumulator**: write `engelsmaSearch` as a `def`
   returning a `Bool` indicating "any admissible (k, w) tuple found." Decidability of
   correctness reduces to functional equivalence. Hard to write but compiles fast.
2. **Inductive predicate witness**: define a `Prop` capturing "the search exhausted the
   tree and found nothing," prove the predicate by `decide`. Slower but more transparent.
3. **Hybrid**: write the search as a `def` and only export the `theorem engelsma_search_returns_none
   : engelsmaSearch 50 246 = false := by native_decide`; then derive `engelsma_lower_bound`
   from this equation + a correctness lemma proven by structural induction.

Option 3 is the standard pattern for certified computation in Lean 4 (cf. `Mathlib.Tactic.Norm
Num.Prime` for `Nat.Prime` checks). It is the recommended target for S3/S4.

### §4.4 Mathlib API gaps for Path B

The following are missing and would need to be built:

- `instance : Decidable (IsAdmissible H)` (§3.1) — strict prerequisite.
- `Finset.image_translate_admissible` — if `H'` is `H + c`, then `IsAdmissible H ↔
  IsAdmissible H'`. Easy.
- `Finset.maxDiam` / a clean treatment of `H.max' hne - H.min' hne`. Mathlib has
  `Finset.max'`, `Finset.min'`; the diameter is just their difference, no separate lemma.
- A combinator for "the search procedure preserves admissibility-correctness across the
  branches." This is essentially a verified backtracking framework — not in Mathlib.

### §4.5 Time budget

`native_decide` compiles its proposition to native code via Lean's compiler and runs it
once. Engelsma's algorithm at `(50, 246)` runs in ~1 second on modern hardware in C++.
The Lean version, after compilation, should run in 10–60 seconds depending on data
structure (Mathlib's `Finset` uses `Multiset` backed by `Quotient`, which is slow).

**Recommendation**: use `Array Nat` or `List Nat` as the runtime representation, with a
final lemma `searchOnArrays = searchOnFinset` to bridge. This is the same trick used in
`Mathlib.Data.Nat.Sieve` and Polymath gallery proofs.

## §5. Path C — Selberg / density sufficient condition (fallback)

### §5.1 The density gap

Let `δ_k := lim sup` of the minimal diameter of admissible `k`-tuples divided by `k log k`.
Polymath 8b (and Maynard's lemmas) give a lower bound `δ_k ≥ (1 + o(1)) / log k` via the
Selberg sieve "ε-perturbation" framework.

For `k = 50`, the prediction is `min_diam ≥ 50 × (log 50 / (1 + ε)) ≈ 195 + …`. The
Polymath 8b proof gets `min_diam ≥ 207` for `k = 50` (computational lower bound from a
sieve argument, not from Engelsma's exhaustive search). The gap to 246 is then ≈ 40.

### §5.2 Closing the gap in Lean

If we can prove **in Lean** the sieve-based bound `min_diam ≥ 207` (a few thousand lines,
substantial effort), then the residual claim is:

$$
\forall H \in \binom{\{0,\ldots,206\}}{50},\ \neg\mathrm{IsAdmissible}(H),
$$

i.e., no admissible 50-tuple has diameter < 207. The remaining search is even smaller in
the sense of "lower bound" (we already know there's no diameter < 207 tuple by the sieve
argument), but the *gap* [207, 245] for the second-step `native_decide` still has
$\binom{207}{50}$ many subsets — still infeasible without pruning.

**Verdict**: Path C does NOT eliminate the need for a pruned search. It only reduces the
constant. Not pursued in this iteration.

## §6. Risks and decision points

### §6.1 Risk: `IsAdmissible` instance + tuple translation are not the hard parts

`Decidable (IsAdmissible H)` is straightforward (~40 lines). The translation invariance
proof (~50 lines) is also standard. The hard part is **§4: the certified search**.
Roughly the order of effort by section is:

- §2.4 bridge: 50–100 lines (1 session).
- §3.1 decidability instance: 40 lines (½ session).
- §4 verified search: 500–1500 lines (5–10 sessions).
- Final wiring: 100 lines (1 session).

### §6.2 Risk: `native_decide` rejection by Mathlib reviewers

If we eventually upstream this, Mathlib's policy is that `native_decide` is *allowed* but
disfavored for foundational lemmas. The gallery has no such concern (we already use
`native_decide` extensively in OQ-03 for `engelsma50Tuple_admissible`, etc.). For the
gallery PR target this is a non-issue.

### §6.3 Risk: external dependency on Engelsma's correctness

Even with a verified search procedure, the *algorithm* is Engelsma's. We are verifying a
particular *implementation* of his approach. The algorithm itself is mathematically
trivial (admissibility check + branch-and-bound); the verification effort is concentrated
on the Lean encoding, not on validating a deep mathematical claim. So this is *not* a
risk in the usual sense.

### §6.4 Decision point: feasibility checkpoint at S4

After S2 (§3.1 instance) and S3 (a minimal Path-B prototype on small parameters, say
`(k, w) = (10, 30)`), we will have empirical evidence on `native_decide` runtime
scaling. If the (10, 30) case takes more than 10 seconds, full (50, 246) is impractical
and we fall back to **Path C-prime**: leave the axiom as-is, but contribute the §3.1
decidability instance and the §2.4 bridge as standalone gallery improvements, narrowing
the axiom to its irreducible content.

## §7. Mathlib API survey

Lemmas and instances that S2 will need:

- `Nat.decidablePrime` — `Mathlib.Data.Nat.Prime.Basic`
- `Finset.card_image_le` — `Mathlib.Data.Finset.Image`
- `Finset.decidableDforallFinset` — `Mathlib.Data.Finset.Basic`
- `decidable_of_iff` — `Mathlib.Init.Data.Bool.Lemmas` (or a similar root)
- `Finset.powersetCard` — `Mathlib.Data.Finset.Powerset`
- `Finset.image_image`, `Finset.card_image_of_injOn` — for translation lemmas
- `Finset.max'`, `Finset.min'`, `Finset.le_max'`, `Finset.min'_le` — already used in OQ-03
- `Nat.sub_add_cancel`, `Finset.image_sub_const` — for translating tuples

For Path B specifically (S3+):

- `Array.foldl`, `List.range`, `Nat.fold` — runtime-friendly iteration
- `Decidable.decide`, `native_decide` tactic — already used in OQ-03

No new Mathlib infrastructure is *required* for S2/S3; everything is glue.

## §8. Sibling lessons

From `BoundedPrimeGapsOQ03.lean`:

- The pattern `by_cases hp2 : p = 2; · subst hp2; native_decide` followed by `by_cases
  hp3 : p = 3; …` is how `engelsma50Tuple_admissible` discharges small-prime admissibility.
  For a general `Decidable (IsAdmissible H)` instance, we instead use `Finset.decidableDforallFinset`
  on `Finset.filter Nat.Prime (Finset.range (H.card + 1))`, which is cleaner.

From `BoundedPrimeGaps.lean`:

- Existing `admissible_subset` lemma (line 79): if `H₁ ⊆ H₂` and `IsAdmissible H₂`, then
  `IsAdmissible H₁`. Useful in §2.4 step 6 (taking a 50-subset of `H'` containing 0).
- `admissible_of_card_lt_two` (line 88): card-based admissibility shortcut.

From `BoundedPrimeGapsSieve.lean`: this file is the sieve-theoretic side and does NOT
contribute to Path B (which is purely combinatorial). Skip.

## §9. Next-action menu (for S2)

**Option A — Build the `Decidable (IsAdmissible H)` instance (~½ session)**
Foundational. Required by every other path. Low risk.
Files touched: `BoundedPrimeGapsOQ03OQ02.lean` (new file with the instance + a sanity
`#eval`-style test). ~50 lines.

**Option B — Prove the §2.4 bridge lemma (~1 session)**
`engelsma_lower_bound_of_finitary`. Reduces the axiom replacement to the finitary form.
Independent of Option A in terms of correctness, but in practice we need the
`Decidable` instance from A to even type-check the conclusion's `¬ IsAdmissible`. So A
should come first.

**Option C — Implement small-case Path B prototype (~2 sessions)**
Write the backtracking search for general `(k, w)`, prove correctness, and `native_decide`
it on a small case like `(6, 16)` or `(10, 30)`. This is the feasibility checkpoint for
the full `(50, 246)` run. Yields the most information per session.

**Recommendation**: Option A in S2 (foundational, minimal risk), Option B in S3 (bridge
to the finitary form), Option C in S4 (feasibility checkpoint at small scale). Full
`(50, 246)` run deferred to S6+ once C confirms scaling.

## §10. References

- T. Engelsma, *Permissible patterns and prime gaps*, http://www.opertech8.com/primes/index.html (2013, accessed via Polymath wiki).
- D. H. J. Polymath, *Variants of the Selberg sieve, and bounded intervals containing many primes*, Research in the Mathematical Sciences 1 (2014), #12.
- A. V. Sutherland, *Narrow admissible k-tuples*, https://math.mit.edu/~drew/admissible.html (2014, computational tables for k ≤ 5000).
- J. Maynard, *Small gaps between primes*, Annals of Mathematics 181 (2015), 383–413.

For Lean infrastructure:

- `proofs/Proofs/BoundedPrimeGaps.lean` — `IsAdmissible` definition (line 59)
- `proofs/Proofs/BoundedPrimeGapsOQ03.lean` — the axiom (line 134), the 50-tuple, the
  `native_decide`-style admissibility proof
- `Mathlib.Data.Finset.Powerset` — `Finset.powersetCard` for §2.3 finitary form
- `Mathlib.Tactic.NormNum.Prime` — `Nat.Prime` decision procedure pattern

## Session 2026-07-24 (researcher-3) — S26: SOUNDNESS REPAIR of the pruned search (bridge was FALSE as stated)

**Mode**: REVISIT (claimed via depth-first RICH tier). **Outcome**: progress — critical
repair; VERIFIED docker build succeeded, 1 intended sorry unchanged (the S11b-δ bridge).

### The finding (adversarial pre-work check, not new theorems-on-top)

Before attempting the planned S11b sound/complete decomposition (~190-300 LOC), I
hand-evaluated `searchAux` on degenerate parameters and found the sorried bridge
`engelsmaSearchPruned_eq_false_iff` was **FALSE as stated** — the planned development
was doomed:

- **Bug**: the legacy initial call `searchAux w k (primesUpTo k) (List.range w) [0]`
  passes candidates CONTAINING the committed `0` (chosen = [0]). The leaf test
  `candidates.length ≥ k - chosen.length` counts candidates as FRESH slots on top of
  chosen, so the surviving `0` is double-counted.
- **Minimal counterexample** `(w,k) = (1,2)`: sole surviving branch (p=2, r=1) reaches
  the leaf with candidates = chosen = [0] and accepts via `1 ≥ 2-1`; but `range 1` has
  no 2-element subset (bridge RHS vacuously true, forcing `false`). Machine-checked:
  `legacy_bridge_refuted`.
- **Second, non-vacuous manifestation**: the S11b-era sanity test asserted
  `engelsmaSearchPruned 11 5 = true` — but H(5) = 12 (Engelsma), so NO admissible
  5-tuple fits in {0..10}. The naive `engelsmaSearch 11 5` disagrees (false). The
  "sanity test" was certifying a WRONG value; its docstring claim ("verifies the pruned
  search agrees with the naive search") was never actually checked against the naive.

### The repair (S26)

1. `engelsmaSearchPruned` candidates are now `(List.range w).filter (· ≠ 0)` —
   restores the disjointness invariant `chosen ∩ candidates = ∅` the leaf needs.
2. Degenerate guard: `w = 0 ∨ k = 0 → false` (pinning 0 ∈ H impossible/forbidden;
   Nat truncation `k - 1 = 0` at `k = 0` made the legacy leaf accept spuriously).
3. Sanity test corrected: `engelsmaSearchPruned_11_5_eq_false` (with the H(5)=12
   mathematical justification in the docstring).
4. Legacy def kept verbatim as `engelsmaSearchPrunedLegacy` SOLELY so
   `legacy_bridge_refuted` stays machine-checked; not for consumption.
5. **Drop-in agreement grid**: `engelsmaSearchPruned_agrees_small` — repaired pruned
   == naive on ALL 78 pairs w ≤ 12, k ≤ 5 (covers both refuted points, all degenerate
   rows, and the positive (7,3) case). native_decide.

### Axiom/sorry accounting
- Bridge sorry (line ~989) UNCHANGED — 1 functional sorry before and after.
- New theorems: naive-side `engelsmaSearch_1_2_eq_false` is kernel-`decide`
  ([propext, Classical.choice, Quot.sound]); the searchAux-valued equations and grid
  use `native_decide` (ofReduceBool), consistent with the file's established S4+
  accounting. No new `axiom` declarations.
- Gallery meta bounded-prime-gaps-oq-03: additionalFile lineCount 997→1127; aggregate
  sorries 0→1 (the additionalFiles entry already disclosed sorries:1 — top-level was
  inconsistent with it).

### Guidance for the future S11b author (IMPORTANT)
- The bridge statement is now plausibly TRUE. State the sound/complete invariants with
  `chosen ∩ candidates = ∅` (or `0 ∉ candidates` at top level) as an EXPLICIT
  hypothesis — filtering preserves it through `tryBranch`.
- Leaf soundness sketch: on surviving paths chosen stays [0]; candidates avoid the
  branch residues r_p for every p ∈ primesUpTo k AND avoid 0; any (k-1)-subset S of
  candidates gives H = {0} ∪ S with card k, image mod p missing r_p (p ≤ k) and
  card k < p (p > k) — admissible. Completeness: admissible H ∋ 0 misses some r_p ≢ 0
  (mod p) per p ≤ k (0 ∈ H puts 0 in every image); the branch choosing those r_p
  retains H \ {0} ⊆ candidates at the leaf.
- Session-numbering note: prior state.md was stale (dated 2026-06-02, blockers B1-B3
  since cleared; the S11b-α combiner IS merged at line ~853; docker builds work fine).
