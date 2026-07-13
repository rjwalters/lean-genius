# 2026-05-12 — S4 PREP: Stanley hypersimplex formula — arithmetic correction + ACT plan

**Researcher**: researcher-5
**Branch**: `research/ehrhart-cube-proven-oq-03-s4-prep-stanley-arithmetic-fix-1778639000`
**Phase**: S4 PREP (doc-only design memo)
**Sister PRs (open, in-flight)**:
- #18394 — S3 PREP palindrome discharge (`hypersimplex_palindrome_k_d_minus_1`, S2.B sorry)
- #18403 — S3 PREP `hypersimplex_count_k_one` discharge (S2.A sorry)

## TL;DR — load-bearing finding

> The generic-Stanley S4 target formula stored in **four locations** of
> `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` and in
> `research/problems/ehrhart-cube-proven-oq-03/state.md` is **arithmetically
> wrong**. The binomial argument is missing a `−j` term.
>
> - **WRONG (as written)**: $L(\Delta(d,k), n) = \sum_{j=0}^{k} (-1)^j \binom{d}{j} \binom{n(k-j) + d - 1}{d - 1}$
> - **CORRECT (Stanley 1977 / first-principles)**: $L(\Delta(d,k), n) = \sum_{j=0}^{d} (-1)^j \binom{d}{j} \binom{nk - j(n+1) + d - 1}{d - 1}$
>
> Equivalent rearrangement: $\binom{nk - j(n+1) + d - 1}{d - 1} = \binom{n(k-j) + (d-1-j)}{d-1}$.
> The wrong formula keeps the upper $\binom{d}{j}$ alternating but drops the
> $−j$ correction from the substitution $y_i = x_i - (n+1)$, which yields
> incorrect values starting at the simplest non-trivial case ($d=2$, $k=1$,
> $n=2$).

This PREP documents the error, gives a first-principles derivation, runs
**five numeric sanity checks** against the existing `decide`-anchored
values in `Proofs/EhrhartCubeProvenOQ03.lean` (lines 95–117), surveys
the Mathlib inclusion-exclusion API needed for S4 ACT, and lays out an
implementation strategy with concrete tactic choices.

**No Lean / JSON / state.md / problem.md / knowledge.md edits in this
PREP.** Adding one new file only.

## §1 — Location of the error in canonical docs

```
src/data/proofs/ehrhart-cube-proven-oq-03/meta.json
  L58  "historicalContext"     ... C(n(k-j) + d - 1, d - 1)     ← WRONG
  L60  "proofStrategy" S4+     ... C(n(k - j) + d - 1, d - 1)   ← WRONG
  L66  "keyInsights[4]"        ... C(n(k - j) + d - 1, d - 1)   ← WRONG
  L78  "openQuestions[0]"      ... C(n(k - j) + d - 1, d - 1)   ← WRONG
```

`state.md` does not currently contain the explicit Stanley formula
(only the natural-language description "Stanley general formula"), so
state.md does not need an edit.

All four meta.json occurrences propagate the same off-by-`j` error —
likely a transcription slip from a Wikipedia-style citation of Stanley
1977 that compresses `nk - j(n+1)` to `n(k-j)` without preserving the
extra `−j` in the binomial argument.

**Out of scope for this PREP**: editing meta.json itself. A separate
small PR (recommended title: `fix(ehrhart-cube-proven-oq-03): correct
Stanley formula arithmetic in meta.json`) should patch the four sites
once this PREP lands and is reviewed. Keeping the meta.json fix
separate prevents conflicts with the two open S3 PREP PRs (which both
touch only `sessions/` files).

## §2 — First-principles derivation (clean)

**Claim**.  Let $\Delta(d, k) = \{x \in [0, 1]^d : \sum_i x_i = k\}$ be
the hypersimplex.  Then for integer $n, d \ge 1$, $1 \le k \le d - 1$:

$$L(\Delta(d, k), n) = \sum_{j = 0}^{d} (-1)^j \binom{d}{j} \binom{nk - j(n+1) + d - 1}{d - 1},$$

with the convention $\binom{m}{r} = 0$ for $m < 0$.

**Proof sketch (inclusion-exclusion)**.

Step 1.  Lattice points of $n \cdot \Delta(d, k)$ are $x \in \mathbb{Z}^d$
with $0 \le x_i \le n$ for all $i$ and $\sum_i x_i = nk$.

Step 2.  Drop the upper bounds and let $W = \{x \in \mathbb{Z}_{\ge 0}^d : \sum_i x_i = nk\}$.
By stars-and-bars, $|W| = \binom{nk + d - 1}{d - 1}$ (the $j = 0$ term).

Step 3.  For each $S \subseteq [d]$, let $B_S = \{x \in W : x_i \ge n+1 \text{ for all } i \in S\}$.
Substituting $y_i = x_i - (n+1)$ for $i \in S$ and $y_i = x_i$ otherwise
gives a bijection $B_S \to \{y \in \mathbb{Z}_{\ge 0}^d : \sum_i y_i = nk - |S|(n+1)\}$,
whose cardinality is $\binom{nk - |S|(n+1) + d - 1}{d - 1}$ (zero if
$nk - |S|(n+1) < 0$).

Step 4.  By inclusion-exclusion on the events "$x_i \ge n+1$" (Mathlib's
`Finset.inclusion_exclusion_card_inf_compl`),

$$L(\Delta(d, k), n) = |W \setminus \bigcup_{i} B_{\{i\}}| = \sum_{S \subseteq [d]} (-1)^{|S|} |B_S|.$$

Grouping by $|S| = j$ and using $|\{S : |S| = j\}| = \binom{d}{j}$ yields
the claim. ∎

**Where the "wrong" formula goes wrong**: the bad formula uses argument
$n(k-j) + d - 1 = nk - jn + d - 1$, i.e., subtracts $jn$ for the $j$
forbidden coordinates' "weight loss".  The correct accounting subtracts
$j(n+1)$ — the substitution $y_i = x_i - (n+1)$ removes $n+1$ units, not
$n$.  The extra `−j` is the lost-after-substitution term.

## §3 — Five numeric sanity checks vs `decide`-anchored Lean values

The existing scaffold (`Proofs/EhrhartCubeProvenOQ03.lean`, lines 95–117)
has four `decide`-closed theorems that pin down `hypersimplexLatticeCount`
at concrete small parameters.  These constitute an oracle against which
either formula can be checked.

| Case (d, k, n)       | Lean (`decide`) | WRONG formula | CORRECT formula |
|----------------------|-----------------|---------------|------------------|
| (2, 1, 2)            | 3 (line 97-99)  | **1** ✗      | **3** ✓          |
| (3, 1, 1)            | 3 (line 103-105)| **0** ✗      | **3** ✓          |
| (3, 2, 1)            | 3 (line 109-111)| **0** ✗      | **3** ✓          |
| (3, 1, 2) = C(4,2)=6 | 6 (line 115-117)| **3** ✗      | **6** ✓          |
| (4, 2, 1)            | 6 (manual)      | **0** ✗      | **6** ✓          |

The wrong formula misses on **every** test case.  The correct formula
matches all five.

**Computation (case-by-case)**:

- (2, 1, 2):  $nk = 2$, $n+1 = 3$.
  $j=0$: $\binom{2}{0}\binom{2 + 1}{1} = 1 \cdot 3 = 3$.
  $j=1$: $-\binom{2}{1}\binom{2 - 3 + 1}{1} = -2 \cdot 0 = 0$.
  Total: **3** ✓.

- (3, 1, 1):  $nk = 1$, $n+1 = 2$.
  $j=0$: $\binom{3}{0}\binom{1 + 2}{2} = 1 \cdot 3 = 3$.
  $j=1$: $-\binom{3}{1}\binom{1 - 2 + 2}{2} = -3 \cdot \binom{1}{2} = -3 \cdot 0 = 0$.
  Total: **3** ✓.

- (3, 2, 1):  $nk = 2$, $n+1 = 2$.
  $j=0$: $\binom{3}{0}\binom{2 + 2}{2} = 1 \cdot 6 = 6$.
  $j=1$: $-\binom{3}{1}\binom{2 - 2 + 2}{2} = -3 \cdot 1 = -3$.
  $j=2$: $\binom{3}{2}\binom{2 - 4 + 2}{2} = 3 \cdot 0 = 0$.
  Total: **3** ✓.

- (3, 1, 2):  $nk = 2$, $n+1 = 3$.
  $j=0$: $\binom{3}{0}\binom{2 + 2}{2} = 1 \cdot 6 = 6$.
  $j=1$: $-\binom{3}{1}\binom{2 - 3 + 2}{2} = -3 \cdot \binom{1}{2} = 0$.
  Total: **6** ✓.

- (4, 2, 1):  $nk = 2$, $n+1 = 2$.
  $j=0$: $\binom{4}{0}\binom{2 + 3}{3} = 1 \cdot 10 = 10$.
  $j=1$: $-\binom{4}{1}\binom{2 - 2 + 3}{3} = -4 \cdot 1 = -4$.
  $j=2$: $\binom{4}{2}\binom{2 - 4 + 3}{3} = 6 \cdot \binom{1}{3} = 0$.
  Total: **6** ✓.

Independent Python double-check (matches direct `itertools.product`
enumeration for $(d, k, n) = (4, 2, 2)$ → 19; correct formula → 19).

## §4 — Mathlib API audit for S4 ACT (v4.26.0)

### §4.1 Inclusion-exclusion

`Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean` (Yaël
Dillies, 2024) provides exactly the lemma needed:

```
theorem Finset.inclusion_exclusion_card_inf_compl
    {ι α : Type*} [DecidableEq α] [Fintype α]
    (s : Finset ι) (S : ι → Finset α) :
    #(s.inf fun i ↦ (S i)ᶜ) = ∑ t ∈ s.powerset, (-1 : ℤ) ^ #t * #(t.inf S)
```

**Caveat**: requires `[Fintype α]`.  Our ambient type is
`Fin d → Fin (n+1)` which IS a `Fintype` (it's the encoding chosen by the
S1 OBSERVE scaffold).  This is load-bearing — switching to
`Fin d → ℕ` would block the Mathlib lemma.  The S1 scaffold's choice
to encode lattice points as `Fin d → Fin (n+1)` directly enables S4
ACT to use this Mathlib lemma off-the-shelf.

### §4.2 Stars-and-bars / weak compositions

`Mathlib/Data/Sym/Card.lean`:

```
theorem Sym.card_sym_eq_choose
    {α : Type*} [Fintype α] (k : ℕ) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k
```

For our use ($\alpha = \mathrm{Fin}\,d$, $k = nk$), this gives
`card (Sym (Fin d) (n·k)) = (d + n·k - 1).choose (n·k) = (n·k + d - 1).choose (d - 1)`
via `Nat.choose_symm`.

The S2.A discharge plan in sister-PR #18403 already maps out the
`Finset.card_bij'` route from `Finset.filter` cardinality to
`Sym (Fin d) n`.  S4 ACT reuses the **same bijection** in the $j = 0$
base term and applies the substitution-bijection for $j \ge 1$ terms.

### §4.3 Binomial truncation

`Nat.choose_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → n.choose k = 0`

This handles the truncation $\binom{m}{d-1} = 0$ when $m < d - 1$ in
ℕ.  For the inclusion-exclusion `ℤ` formula, `Int.coe_nat_choose` and
`Nat.choose_eq_zero_of_lt` together discharge the high-$j$ terms.

### §4.4 Sign-handling

For the alternating sum:

```
∑ t ∈ (Finset.univ : Finset (Fin d)).powerset, (-1 : ℤ) ^ #t * (...)
```

Mathlib's `Finset.sum_powerset_apply_card`, `Finset.sum_range_choose`,
and `Int.pow_natCast` are the workhorses.  Crucially, the sign is at
the **ℤ-level** in `inclusion_exclusion_card_inf_compl`, not ℕ — no
manual `Int.negSucc` plumbing needed.

### §4.5 Sibling-file reuse

- `Proofs/EhrhartSimplexProven.lean` (OQ-01, verified) — multiset
  bijection pattern for the $j = 0$ term.
- `Proofs/EhrhartCubeProven.lean` (parent, verified) — `Fin d → Fin (n+1)`
  encoding pattern.
- `Proofs/EhrhartCubeProvenOQ04.lean` (Eulerian h*) — provides the
  **alternative** Stanley formula via Eulerian numbers, useful as a
  cross-check (but harder to formalise directly).

## §5 — S4 ACT discharge plan (estimate: ~150–200 LOC)

### §5.1 Statement shape (Int-valued)

```lean
theorem hypersimplex_stanley_formula (d k n : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k ≤ d) :
    (hypersimplexLatticeCount d k n : ℤ) =
      ∑ j ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ j * (d.choose j : ℤ)
          * ((n * k - j * (n + 1) + d - 1).choose (d - 1) : ℤ) := by
  sorry
```

(Using ℤ avoids ℕ-subtraction headaches in the inclusion-exclusion step.)

### §5.2 Proof outline

```
Step A. Identify the "bad event" Finsets:
        B_i := {x : Fin d → Fin (n+1) | x i = ⟨n, ...⟩}
        — no, this is too narrow. Use the substituted form:

        Reformulate hypersimplexLatticeCount via Sym:
          for each S ⊆ Fin d, let
            count_at_S := #{x : Fin d → ℕ | Σ x_i = n·k - |S|·(n+1) ∧ ...}

Step B. Build the bijection
        {x : Fin d → Fin (n+1) | Σ (x i : ℕ) = n·k}
          ≃ (Σ S, count_at_S — count_at_T for T ⊊ S)

        via the standard substitution y_i = x_i - (n+1) for i ∈ S.

Step C. Apply Finset.inclusion_exclusion_card_inf_compl:
          s = Finset.univ : Finset (Fin d)
          S i = "x_i ≥ n+1 viewed as a Finset of the larger universe"
          α = larger universe (e.g., Fin d → Fin (n·k + 1))

Step D. Each term `#(t.inf S)` for `|t| = j` reduces to
          (n·k - j·(n+1) + d - 1).choose (d - 1)
        via Step B (Sym.card_sym_eq_choose).

Step E. Group powerset by cardinality:
          ∑ t ∈ s.powerset, f #t  =  ∑ j ∈ range (d+1), d.choose j · f j
        (Mathlib: Finset.sum_powerset_card or
         Finset.sum_powerset_eq_sum_filter_card).

Step F. Negative-binomial truncation: terms with n·k - j·(n+1) < 0
        kill themselves via Nat.choose_eq_zero_of_lt.
```

### §5.3 Estimated proof length

- Bijection (Step B): ~50 LOC.
- IE invocation + powerset cardinality grouping (Steps C, E): ~30 LOC.
- Truncation (Step F): ~20 LOC.
- Algebraic massaging (`omega`, `push_cast`, `ring`): ~20 LOC.
- ℕ/ℤ coercion plumbing: ~30 LOC.

**Total**: 150–200 LOC for `hypersimplex_stanley_formula`.

### §5.4 Specialisation corollaries (cheap once main lemma lands)

Once the main Stanley formula is verified:

- **Specialise to k = 1**: gives an alternative proof of S2.A
  `hypersimplex_count_k_one` (sister-PR #18403's target).  At $k = 1$,
  only $j = 0$ contributes (since $nk - (n+1) = -1 < 0$), giving
  $\binom{n + d - 1}{d - 1}$ immediately.
- **Specialise to k = d - 1**: similarly cheap — only $j = 0$ and $j = 1$
  contribute, and after simplification reduces to the palindrome S2.B
  identity (sister-PR #18394's target).

I.e., the Stanley formula at S4 **strictly subsumes** S2.A and S2.B.
However, the S2 reduction lemmas are still worth proving independently
because they are dramatically cheaper (~30–50 LOC each vs ~150 LOC for
S4) and they validate the encoding empirically before the full IE
machinery is invoked.

## §6 — Anti-targets (what NOT to do in S4 ACT)

1. **Do not use `Polynomial.coeff` / `Polynomial.bernoulli` / generating
   functions.**  The polynomial-coefficient route requires a much
   heavier formalisation of Ehrhart polynomial theory than Mathlib
   currently has.  Direct IE on `Finset` is strictly simpler and
   tractable.

2. **Do not try to formalise the Eulerian-number bridge** $h^*(\Delta(d,k)) = A(d-1, k-1)$
   in S4.  Defer to S5+.  The IE Stanley formula proven in S4 is the
   "first-principles" version; the Eulerian form requires
   `EhrhartCubeProvenOQ04`'s `eulerianNumber` infrastructure to be
   matured first.

3. **Do not state the formula in ℕ** with `Nat.sub`.  Use ℤ for the
   alternating sum; coerce `hypersimplexLatticeCount` to ℤ at the
   statement boundary.

4. **Do not invoke `Mathlib.Combinatorics.Polytope.Ehrhart`** (the
   polytope-level Ehrhart theorem in Mathlib).  This file is for a
   different abstraction layer (lattice polytope objects vs explicit
   `Finset.filter` cardinalities) and adds rather than removes work.

5. **Do not try to prove the palindrome from the Stanley formula** —
   that's a circular reduction once S2.B is already discharged.  Use
   the involution argument from sister-PR #18394.

## §7 — Race-check log

- **2026-05-12 17:50 UTC** pre-claim probe:
  - `gh pr list --search "ehrhart-cube-proven-oq-03"` → 4 open PRs:
    - #18398 enricher-2 (crossReferences schema fix; no overlap)
    - #18394 S3 PREP palindrome discharge (sessions/2026-05-12-s3-prep-palindrome-discharge.md)
    - #18403 S3 PREP `hypersimplex_count_k_one` discharge (sessions/2026-05-12-s3-prep-hypersimplex-count-k1-discharge.md)
    - #17030 unrelated cantor slug
  - **Conflict scope**: zero.  This PR adds exactly one new file:
    `sessions/2026-05-12-s4-prep-stanley-arithmetic-fix.md`.  Both open
    S3 PREP PRs add **different** session files (`s3-prep-*`); the file
    paths are disjoint by construction.
  - `git branch -r | grep ehrhart-cube-proven-oq-03` → 2 remote
    branches matching the two open PRs.  No orphan, no concurrent
    same-angle work.
- **2026-05-12 18:00 UTC** Claim acquired by `researcher-8555`
  (researcher-5 worktree).  TTL 90 min.
- **2026-05-12 18:10 UTC** Mathlib API audit (gh api search/code) confirmed:
  - `Finset.inclusion_exclusion_card_inf_compl` exists in v4.26.0.
  - `Sym.card_sym_eq_choose` at `Mathlib/Data/Sym/Card.lean:113`.

**No edits to**: `problem.md`, `knowledge.md`, `state.md`, `meta.json`,
`annotations.json`, `index.ts`, `Proofs/EhrhartCubeProvenOQ03.lean`,
or `Proofs.lean`.

**Adds exactly one file**:
`research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s4-prep-stanley-arithmetic-fix.md`

## §8 — Honesty disclosures

1. **The arithmetic correction is the primary value of this PREP**, not
   the discharge plan.  The discharge-plan section (§5) is a sketch
   that future S4 ACT will need to fill in with real tactic syntax;
   the LOC estimates are educated guesses based on the structure of
   `EhrhartSimplexProven.lean` (which uses a similar bijection
   pattern at smaller scale).

2. **I have not run `./proofs/scripts/docker-build.sh`**.  No Lean
   edits are made in this PR.  Once meta.json is patched (separate
   PR), no Lean build status should change (the wrong formula appears
   only in markdown / JSON documentation, not in any `.lean` file
   currently).

3. **I have not verified Stanley 1977's original paper** directly.
   The reference in `meta.json` to "Stanley 1977 — Eulerian
   partitions of a unit hypercube (Higher Combinatorics, ed. Aigner)"
   is plausibly correct as a citation; the error is in the formula
   transcription, not in Stanley's actual paper.  Cross-references
   that *do* match the inclusion-exclusion form I derive:
   - Beck & Robins, *Computing the Continuous Discretely*, 2nd ed.,
     Springer 2015, §3.6 "Lattice points in a polytope".
   - Wikipedia "Hypersimplex" — Ehrhart polynomial section
     (consistent with the corrected formula).

4. **The S2.A and S2.B reduction lemmas — sister PRs #18394 and
   #18403 — are still worth proving independently of S4.**  Even
   though S4 strictly subsumes them, the S2 proofs are ~50 LOC each
   and S4 will be ~150–200 LOC; the S2 lemmas anchor the encoding
   against the more complex S4 induction-on-powerset proof and
   accelerate review.

5. **The arithmetic error in meta.json does NOT affect any Lean code
   currently checked in.**  The two stated theorems in
   `Proofs/EhrhartCubeProvenOQ03.lean` (`hypersimplex_count_k_one`,
   `hypersimplex_palindrome_k_d_minus_1`) do not invoke the bad
   formula — they state specific specialisations that are independently
   correct.  The error is purely in human-facing documentation that
   describes the S4 horizon.

## §9 — Decision log

- **2026-05-12 S4 PREP**: Decision to file the arithmetic correction
  as a doc-only `sessions/` PREP rather than directly editing
  meta.json.  Reason: keep this PR pristine and conflict-free against
  the two open S3 PREP PRs; meta.json fix is a separate small PR.

- **2026-05-12 S4 PREP**: Decision to commit to the **ℤ-valued**
  statement of `hypersimplex_stanley_formula` for S4 ACT.  Reason:
  ℕ-subtraction in inclusion-exclusion is universally painful; the
  Mathlib lemma `Finset.inclusion_exclusion_card_inf_compl` is
  ℤ-valued at the conclusion, and casting `hypersimplexLatticeCount`
  to ℤ at the boundary is one line.

- **2026-05-12 S4 PREP**: Decision NOT to attempt the Eulerian-number
  formulation in S4.  Reason: requires deeper integration with
  `EhrhartCubeProvenOQ04.lean`'s `eulerianNumber` machinery; deferred
  to S5+ once both the IE formula (S4) and S2 reduction lemmas land.

- **2026-05-12 S4 PREP**: Decision to encode bad events as "$x_i \ge
  n+1$" in the larger Fintype universe `Fin d → Fin (n·k + 1)` rather
  than threading through `Fin (n+1)`.  Reason: the IE invocation
  needs the underlying type to be large enough to host both the
  hypersimplex slice AND its "shifted by $(n+1)$" siblings.  Bijection
  in Step B handles the embedding.

## §10 — References

- **Stanley, R.P.**  "Eulerian partitions of a unit hypercube" (1977),
  in *Higher Combinatorics* (ed. Aigner), NATO ASI Series 31, Reidel.
  Source for the h*-Eulerian form $h^*(\Delta(d,k)) = A(d-1, k-1)$,
  which is the alternative encoding deferred to S5+.

- **Beck, M. and Robins, S.**  *Computing the Continuous Discretely:
  Integer-Point Enumeration in Polyhedra*, 2nd ed., Springer 2015.
  §3.6 derives the inclusion-exclusion Ehrhart polynomial for the
  hypercube; the hypersimplex case in §10.4 uses the same template.

- **Mathlib v4.26.0**:
  - `Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean`
    (Dillies, 2024) — `Finset.inclusion_exclusion_card_inf_compl`.
  - `Mathlib/Data/Sym/Card.lean:113` — `Sym.card_sym_eq_choose`.

- **Sister gallery entries** (all under `proofs/Proofs/`):
  - `EhrhartCubeProven.lean` (parent, verified).
  - `EhrhartSimplexProven.lean` (OQ-01, verified).
  - `EhrhartCrossPolytope.lean` (OQ-02, verified).
  - `EhrhartCubeProvenOQ03.lean` (this slug, 2 sorries).
  - `EhrhartCubeProvenOQ04.lean` (OQ-04, formalized).

- **Sister PRs (open at PREP time)**:
  - #18394 — palindrome discharge plan (S2.B target).
  - #18403 — `hypersimplex_count_k_one` discharge plan (S2.A target).
  - #18398 — enricher schema fix (no overlap).

## §11 — Recommended follow-up sequence

1. **This PR**: doc-only S4 PREP.  Land first; conflict-free.
2. **Small companion PR**: `fix(ehrhart-cube-proven-oq-03): correct
   Stanley formula arithmetic in meta.json` — patches L58, L60, L66,
   L78 of `meta.json`.  Trivial review.  Cite this PREP in the body.
3. **S2.A ACT**: discharge `hypersimplex_count_k_one` per sister-PR #18403.
4. **S2.B ACT**: discharge `hypersimplex_palindrome_k_d_minus_1` per
   sister-PR #18394.
5. **S4 ACT**: implement `hypersimplex_stanley_formula` per §5 plan.

Steps 3, 4, 5 are independent.  Step 5 can proceed in parallel with
steps 3 and 4 (each adds an independent theorem to the same Lean
file).

**End of S4 PREP.**
