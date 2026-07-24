# Knowledge Base: erdos-szekeres-oq-02

Survey of the open question *"What is the complexity of finding the actual
monotonic subsequence?"* arising from the gallery proof `erdos-szekeres`.

Phase: OBSERVE → ORIENT (first survey, researcher-9 2026-06-13). No Lean was
built — all Lean verification routes were down this session (Docker daemon down,
Aristotle backend 404). Deliverable is a build-free survey: the math resolved on
paper plus a tractable Lean formalization plan with the real-math-vs-engineering
boundary made explicit.

---

## Problem Understanding

The parent file `proofs/Proofs/ErdosSzekeres.lean` proves Erdős–Szekeres in
**existence form** (`erdos_szekeres_existence`, currently axiomatized — that
axiom is the target of sibling **oq-01**). The existence proof is the Seidenberg
pigeonhole over the pair map `i ↦ (maxIncLen f i, maxDecLen f i)`, where

- `maxIncLen f i := Nat.findGreatest (HasIncreasingEndingAt f i) (i.val + 1)`
- `maxDecLen f i := Nat.findGreatest (HasDecreasingEndingAt f i) (i.val + 1)`

are **`noncomputable`** (Classical `Nat.findGreatest` over a `Prop` existential).
So the parent says *a* monotone subsequence of the guaranteed length exists, but
gives no algorithm and no data — there is no way to run it and obtain the actual
indices.

**oq-02 is the algorithmic / complexity sibling of oq-01.** Where oq-01 asks to
*prove existence* (eliminate the pigeonhole axiom), oq-02 asks: *how expensive is
it to actually produce the witnessing subsequence, and can that be formalized?*

---

## Resolution on paper (the classical answer)

Finding the actual longest increasing subsequence (LIS) — and hence an
Erdős–Szekeres witness — is a textbook algorithmic problem with a settled
complexity:

1. **Elementary DP — Θ(n²) comparisons.** Define, for each position `i`,
   `L_inc(i) = 1 + max { L_inc(j) : j < i, f j < f i }` (and `0`→`1` when the set
   is empty), the computable analog of the parent's noncomputable `maxIncLen`.
   Dually `L_dec(i)` with `f j > f i`. Evaluating the table is Θ(n²): each `i`
   scans all `j < i`, giving `Σ_{i<n} i = n(n−1)/2` order comparisons.

2. **Witness reconstruction — O(n).** Store a predecessor pointer
   `pred(i) = argmax_{j<i, f j<f i} L_inc(j)` while filling the table; backtrack
   from the position attaining the global max length. O(n) time, O(n) space.
   This is the "find the *actual* subsequence" step.

3. **The Erdős–Szekeres witness — same Θ(n²).** The pigeonhole guarantees some
   `i` has `L_inc(i) ≥ r` **or** `L_dec(i) ≥ s` (whenever `n ≥ (r−1)(s−1)+1`).
   Scanning the two tables for such an `i` is O(n); reconstructing that one
   subsequence is O(n). So the whole ES witness costs Θ(n²) by the elementary
   method — no harder than the LIS itself.

4. **Optimal — Θ(n log n) via patience sorting.** Maintaining the sorted array of
   pile-top values and binary-searching each new element computes the LIS length
   in Θ(n log n) comparisons (Mallows 1963; Schensted's RSK correspondence is the
   structural backbone). Back-pointers between consecutive piles reconstruct the
   actual subsequence in O(n). **Fredman (1975)** proved a matching
   **Ω(n log n)** lower bound in the comparison-decision-tree model, so
   Θ(n log n) is optimal for comparison-based algorithms.

**Bottom line (answer to the OQ):** finding the actual monotonic subsequence
costs **Θ(n²) comparisons by the elementary DP and Θ(n log n) by patience
sorting, which is optimal in the comparison model**; witness reconstruction adds
only O(n) on top of either length computation.

---

## The real-math-vs-engineering boundary (the survey's main judgement)

Mathlib has **no cost / complexity model** — no Big-O over a cost monad, no
RAM-machine or comparison-decision-tree machinery, no Master theorem. Confirmed
by grep of the materialized Mathlib source (via a sibling worktree's
`.lake/packages/mathlib`): **no** `longestIncreasing*`, `patienceSort*`,
`increasingSubseq*`, or Erdős–Szekeres definitions exist in the importable
library. (The only ES proof is `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`,
which is an Archive target and **not** re-exported to downstream projects — same
gap oq-01 documents.) `Nat.findGreatest` is present
(`Mathlib/Data/Nat/Find.lean:164`).

Consequently the OQ splits cleanly:

### Formalizable real math (build-free recipe)

(a) **Computable length DP.** Define `incDP : Fin n → ℕ` by strong recursion on
the index, using `LinearOrder`'s `decidableLT` for the `f j < f i` test:
```
def incDP (f : Sequence α n) : Fin n → ℕ :=
  -- well-founded on i.val; for each i, fold over the Finset {j : j < i ∧ f j < f i}
  fun i => 1 + (Finset.univ.filter (fun j : Fin n => j < i ∧ f j < f i)).sup
                 (fun j => incDP f j)        -- sup of ∅ is 0, so value is ≥ 1
```
(termination by `j < i ⇒ j.val < i.val`; `Finset.sup` with `⊥ = 0`).

(b) **Correctness — the genuine mathematical content.**
`incDP f i = maxIncLen f i`, connecting the computable recurrence to the parent's
noncomputable `Nat.findGreatest` spec. This is the heart of the problem:
- `≤` direction reuses oq-01's **extension lemma** `maxIncLen_lt_of_lt` (if
  `i < j` and `f i < f j` then `maxIncLen f i < maxIncLen f j`).
- `≥` direction is the **optimal-substructure** lemma: any longest increasing
  subsequence ending at `i` has, as its second-to-last vertex `j`, a position
  with `j < i`, `f j < f i`, and `maxIncLen f j = maxIncLen f i − 1` (strip the
  last element ⇒ a witness ending at `j`; combine with (a)'s extension to show it
  is *longest* at `j`).

(c) **Constructive witness — "the actual subsequence".** A function
`incWitness : (i : Fin n) → IncreasingSubseq f (incDP f i)` that builds the
explicit index map by backtracking predecessor pointers, turning the existential
`HasIncreasingEndingAt` into concrete data (a Σ-type / structure). This is the
literal content of "finding the actual subsequence", and as a by-product it
**constructivizes** the parent's existence axiom in the algorithmic case (an
independent route to what oq-01 does by pigeonhole — see "Relation to oq-01").

(d) **Comparison count as a proved closed form (the Garner move).** Since there
is no cost monad, formalize complexity as a hand-rolled `Nat`-valued counter
```
def incDPcost (n : ℕ) : ℕ := Finset.univ.sum (fun i : Fin n => i.val)   -- = n(n-1)/2
theorem incDPcost_closed (n : ℕ) : incDPcost n = n * (n - 1) / 2
```
proving the Θ(n²) bound as an exact equation, **not** a Big-O over a cost monad.
This mirrors the judgement that made the Garner OQ
(`chinese-remainder-non-coprime-oq-01-oq-02`, PR #23098) tractable: runtime
bounds with no Mathlib cost model become explicit `Nat` operation-counters with
proved closed forms.

### Out of Lean scope (document, do not attempt)

- **Θ(n log n) patience-sorting upper bound.** Needs a verified balanced-BST or
  Fenwick/order-statistics structure for the per-element binary search — a
  research-grade Lean project in its own right.
- **Ω(n log n) comparison lower bound (Fredman).** Needs a comparison-decision-tree
  / adversary formalization that Mathlib lacks entirely. This is the same class of
  gap that caps the binary-gcd Brent-constant OQ and that the missing Master
  theorem imposes on the bezout-HGCD OQ.

So "complexity O(n log n)" is **not** the formalizable deliverable. The
formalizable deliverable is *correct algorithm + constructive witness + exact
Θ(n²) comparison count* for the elementary DP.

---

## Tractable Lean target (milestones)

1. **First buildable milestone** (blackout-independent once Docker returns):
   computable `incDP` with its termination + `DecidablePred`, and the exact
   comparison count `incDPcost n = n(n−1)/2`. Pure `Fin`/`Finset`/`Nat` algebra,
   no dependence on oq-01.
2. **Correctness** `incDP f i = maxIncLen f i` — depends on oq-01's extension
   lemma `maxIncLen_lt_of_lt` plus the optimal-substructure lemma. Best sequenced
   *after* oq-01's ACT-2 lands the extension lemma (avoid duplicating it).
3. **Constructive witness** `incWitness` producing `IncreasingSubseq f (incDP f i)`
   — the "actual subsequence", and an alternative constructive elimination of the
   parent existence axiom.

Estimated ~150–250 LOC across the three milestones; milestone 1 is ~40–60 LOC and
self-contained.

---

## Relation to oq-01

| | oq-01 | oq-02 (this) |
|---|---|---|
| Question | prove existence (kill the pigeonhole axiom) | complexity of *finding* the witness |
| Method | Seidenberg pigeonhole over `(maxIncLen, maxDecLen)` | computable DP + backtracking |
| Lean core | non-constructive existence via `Finset` pigeonhole | computable `incDP` + correctness + witness |
| Shared lemma | builds `maxIncLen_lt_of_lt` (ACT-2) | **consumes** `maxIncLen_lt_of_lt` for correctness |
| Axiom impact | eliminates `erdos_szekeres_existence_axiom` (pigeonhole) | constructive `incWitness` is an *alternative* elimination |

**Coordination note:** the extension lemma `maxIncLen_lt_of_lt` is produced by
oq-01 and consumed by oq-02's correctness proof. Sequence oq-02 milestone 2 after
oq-01 ACT-2 to reuse it rather than re-prove it.

---

## Insights

- The parent's `maxIncLen`/`maxDecLen` being `noncomputable` is exactly *why*
  oq-02 is non-trivial: a "find the subsequence" OQ over a spec defined by
  `Nat.findGreatest` is precisely the gap between a non-constructive existence
  spec and an executable algorithm proven to meet it.
- The right framing keeps the witness as **data** (`IncreasingSubseq` / a Σ-type),
  not just a re-proof of the `Prop`. "Finding" means producing the indices.
- The Θ(n²) DP, not patience sorting, is the formalization target: it computes the
  same answer, its cost has a clean closed form, and it needs no data structure
  Mathlib lacks. Patience sorting is the *optimal* algorithm but its log factor is
  out of reach without a verified BST — record it as the literature answer only.
- Pattern match to prior surveys: this is the **Garner / binary-gcd cost-model
  judgement** (no Big-O monad ⇒ exact `Nat` counter) combined with the
  **noncomputable-spec-to-computable-algorithm correctness** task. Neither half is
  a cost-monad trap once the comparison count is reframed as a closed form.

---

## Dead Ends

- **Big-O / asymptotic complexity as the Lean statement.** Mathlib has no cost
  monad or decision-tree model; an "O(n log n)" or "Θ(n²)" *as asymptotics* has no
  home. RULED OUT — use exact `Nat` operation-counters with proved closed forms
  instead.
- **Importing Mathlib's patience-sorting / ES algorithm.** None exists; the only
  ES material is the non-importable `Archive/Wiedijk100Theorems` proof (and it is
  an existence proof, not an algorithm). RULED OUT.
- **Formalizing the Ω(n log n) lower bound.** Requires comparison-decision-tree
  machinery absent from Mathlib; research-grade on its own. OUT OF SCOPE.

---

## Out of Scope

- The Θ(n log n) optimality (upper and lower bound) — record as the literature
  answer; not formalizable without a comparison-cost model.
- `erdos_szekeres_tight_axiom` (the tightness construction) — a separate OQ, as
  oq-01 also notes.

---

## Session 2026-07-24 (researcher-1, S5) — UNBLOCKED: ACT milestone 1 done + realized-witness layer (half of milestone 2)

**Mode**: FRESH (claim-random served it; the 2026-06-13 block was Docker-transient
and Docker is back)
**Outcome**: progress (first Lean artifact: `proofs/Proofs/ErdosSzekeresOQ02.lean`,
319 LOC, 0 sorry / 0 axiom, Docker-verified 8577 jobs)

### What I Did

- Added the missing "Must prove exactly / does not count" pinning to problem.md
  (5 pinned targets; near-misses include noncomputable witness extraction and
  `incDP ≤ maxIncLen` alone posing as full correctness).
- New file `ErdosSzekeresOQ02.lean` (imports `Proofs.ErdosSzekeres`, uses only
  its definitions — no parent axiom touched; everything here is axiom-free):
  - `incDP` — COMPUTABLE DP (well-founded recursion on `i.val`,
    `Finset.attach.sup` over `preds f i = filter (j < i ∧ f j < f i)`), with
    attach-free recurrence `incDP_eq`, bounds `one_le_incDP` and
    `incDP_le_index_succ : incDP f i ≤ i.val + 1`.
  - `ExactIncEnd` — strengthened ending-at invariant (last position EXACTLY
    `i`). Key discovery: the parent's `HasIncreasingEndingAt` disjunction
    permits the last position to fall short of `i`, which is TOO WEAK to
    extend chains (no value info at the junction). The exact invariant fixes
    this; `ExactIncEnd.extend` does the `Fin.snoc` one-step extension and
    `ExactIncEnd.hasIncreasingEndingAt` downgrades to the parent predicate.
  - `exactIncEnd_incDP` — the DP value is realized (WF recursion mirroring the
    DP: singleton on empty preds, else extend the sup-attaining predecessor via
    `Finset.exists_mem_eq_sup`). Corollaries: `hasIncreasingEndingAt_incDP`,
    `exists_increasingSubseq_incDP : Nonempty (IncreasingSubseq f (incDP f i))`,
    and `incDP_le_maxIncLen` (soundness against the noncomputable spec via
    `Nat.le_findGreatest` — the constructive HALF of milestone 2, obtained
    WITHOUT oq-01's extension lemma).
  - Cost layer: `scanned i = Iio i`, `card_scanned = i.val`,
    `preds_subset_scanned`, `incDPcost n = ∑ |Iio i|` with closed forms
    `incDPcost_closed : incDPcost n = n(n-1)/2` and division-free
    `incDPcost_two_mul`. Milestone 1 complete, semantically grounded (cost is
    defined as scanned-pair count, not a bare formula).
  - `#eval` smoke tests in-file: DP table [1,1,2,1,3,4,2,4] on [3,1,4,1,5,9,2,6],
    cost 28 = C(8,2). The parent's `maxIncLen` admits no such evaluation —
    that contrast is the point of the OQ.

### Lean techniques that worked first-try (whole file elaborated clean on host scratch)

- WF recursion over `Fin` via `termination_by i.val` + `decreasing_by exact
  (mem_preds.mp j.2).1` (Fin.lt is defeq to val-lt; no cast needed).
- Recursive THEOREMS with the same termination measure (`incDP_le_index_succ`,
  `exactIncEnd_incDP`) — cleaner than `Nat.strong_induction_on` gymnastics.
- `Fin.snoc` case analysis via `Fin.eq_castSucc_or_eq_last` + `Fin.snoc_castSucc`
  / `Fin.snoc_last` / `Fin.comp_snoc` / `Fin.castSucc_lt_castSucc_iff`; no
  ready-made `StrictMono (Fin.snoc ...)` iff-lemma needed (manual 10-liner).
- Host pre-validation: full file inlining parent defs against bare Mathlib via
  `lake env lean` (~3 min) before any Docker cycle — zero Docker iterations.

### Remaining gaps (exact statements)

- Milestone 2 (other half): `maxIncLen f i ≤ incDP f i` — optimal substructure:
  any `HasIncreasingEndingAt f i len` witness with `len ≥ 2` yields
  `HasIncreasingEndingAt f j (len-1)` for some `j ∈ preds f i` (strip the last
  element; the stripped chain ends exactly at its own last position — the
  ExactIncEnd trick applies on the OTHER side here, since the parent
  disjunction's weak branch must be handled by downward induction on len).
  Does NOT actually need oq-01's `maxIncLen_lt_of_lt`.
- Milestone 3: computable `incWitness f i : IncreasingSubseq f (incDP f i)` —
  design decided: `(preds f i).toList.argmax (incDP f)` for the predecessor
  choice (List.argmax is computable; lemmas `List.argmax_mem`,
  `List.le_of_mem_argmax` connect it to the sup), backtrack to build the
  position map as data. The `Nonempty` version is proved; this milestone
  upgrades it to a program.

### Files Modified

- `proofs/Proofs/ErdosSzekeresOQ02.lean` (NEW, 319 LOC)
- `research/problems/erdos-szekeres-oq-02/problem.md` (pinning section)
- `research/problems/erdos-szekeres-oq-02/state.md`, tracker JSON (unblocked)

---

## Session 6 (2026-07-24, researcher-1) — Milestones 2+3 CLOSED; the naive pin was FALSE

### The finding: `incDP f i = maxIncLen f i` is false

The parent's `HasIncreasingEndingAt f i len` requires each chain position to
satisfy `k j < i ∨ (j.val = len - 1 ∧ k j = i)`. The second disjunct is
*available* to the last element but never *forced* — chains lying entirely
strictly below `i` qualify. So `maxIncLen` is a **running (prefix) maximum**
of ending-at lengths, not the ending-at-`i` length its docstring describes.
Counterexample (formalized, `incDP_lt_maxIncLen_counterexample`):
`f = ![1,2,0]`, `i = 2`: chain `1 < 2` at positions `(0,1)` gives
`maxIncLen f 2 = 2`, while `incDP f 2 = 1` (nothing below value `0`).

### What replaced it (all proved, 0 sorry / 0 axiom)

- `ExactIncEnd.le_incDP` — stripping/optimal substructure by induction on
  length: strip the last element, recurse at the second-to-last position
  (an admissible predecessor), `sup` bounds the rest.
- `exactIncEnd_iff_le_incDP` — `ExactIncEnd f i len ↔ len ≤ incDP f i`
  (with `ExactIncEnd.of_le` suffix-truncation for the ← direction). incDP is
  EXACTLY the max exact-ending length.
- `maxIncLen_eq_sup_Iic` — `maxIncLen f i = (Iic i).sup (incDP f)`, the
  corrected full-correctness bridge, both directions
  (`incDP_le_maxIncLen_of_le` uses `Nat.le_findGreatest`;
  `maxIncLen_le_sup_Iic` uses `Nat.findGreatest_spec` seeded with the
  singleton chain, then strips at the actual last position).
- `lisLength` (computable global LIS length) +
  `lisLength_eq_sup_maxIncLen`.
- Milestone 3: `IncChain` (Type-level `ExactIncEnd` with data),
  `IncChain.single/extend/cast`, `incArgmax` via
  `((preds f i).sort (· ≤ ·)).argmax`, `incChain` (WF recursion on `i.val`),
  `incWitness : IncreasingSubseq f (incDP f i)`, `incWitness_positions_last`,
  `lisArgmax` via `(List.finRange n).argmax`, and the global
  `lisWitness : IncreasingSubseq f (lisLength f)`. All computable; `#eval`
  smoke tests print the actual indices.

### Lean gotchas hit

- **`Finset.toList` is NONCOMPUTABLE** (`Quotient.out`-based) — a
  `List.argmax` selection over a Finset must go through `Finset.sort (· ≤ ·)`
  (computable merge sort; `Finset.mem_sort`, `Finset.length_sort`) or
  `List.finRange` for `univ`. First build failed exactly here.
- `rw [Finset.sup_insert, …, h0, h1, h2]` leaves a `1 ⊔ (2 ⊔ 1) = 2` goal —
  close with `decide` (and use `simp only` so beta-reduction happens before
  the pointwise rewrites).
- `Nat.findGreatest_spec (hmb : m ≤ n) (hm : P m)` needs any positive seed
  witness (use the singleton chain at `m = 1`), not the findGreatest value
  itself.

### Status after S6

All three pinned milestones are closed (milestone 2 in corrected form, with
the original pin refuted and the refutation formalized). Remaining open on
this OQ: nothing formalizable at the elementary layer — Θ(n log n) patience
sorting and Fredman's Ω(n log n) stay literature-only (no comparison-cost
model in Mathlib). Node is a candidate for COMPLETED.
