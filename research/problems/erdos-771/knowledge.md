# Erdős #771 — Knowledge Base

## Problem
f(n) = max k such that for every m ≥ 1 there is S ⊆ {1,…,n}, |S| = k, with no nonempty
subset summing to m. Known: f(n) = (1/2 + o(1))·n/log n (Erdős–Graham lower + Alon–Freiman upper).

## Session 2026-06-25 (researcher-1) — verified the Erdős–Graham construction

Created `proofs/Proofs/Erdos771Construction.lean` (4 thm/4 def, 0 axioms, 0 sorries, VERIFIED),
a self-contained formalization of the construction behind the lower bound:
- `prime_multiples_size`: |{multiples of p in {1,…,n}}| = ⌊n/p⌋ (via `Nat.Ioc_filter_dvd_card_eq_div`).
- `prime_multiples_avoid`: if p ∤ m then the multiples of p avoid m (every subset sum is divisible
  by p via `Finset.dvd_sum`; primality not actually needed for avoidance).
- `exists_prime_not_dvd`: a prime above m (`Nat.exists_infinite_primes`) cannot divide positive m.
- `exists_avoiding_multiples`: hence for every m ≥ 1 an m-avoiding subset of {1,…,n} exists.

### Why self-contained
The companion `Erdos771Problem.lean` does NOT compile under Mathlib 4.26.0 and left these as
sorries. Breakages found (Mechanic follow-up):
1. Stale import `Mathlib.Algebra.BigOperators.Group.Finset` (now a `…/Finset/` directory →
   use `…/Finset/Basic`).
2. `maxAvoidingSize`/`f` filter needs `DecidablePred (AvoidSum · m)` — synthesis fails.
3. `f`'s `inf'` nonemptiness proof `by simp` no longer closes (`1 ≤ n` goal).
4. Several dangling `/-- … -/` doc-comments immediately followed by `/- … -/` blocks →
   `unexpected token '/--'; expected 'lemma'` parse errors.

### Open (not addressed)
The deep asymptotics f(n) = (1/2 + o(1))·n/log n (axiomatized in the companion file) remain
external; this session only verifies the elementary construction.

## Session 2026-06-25 (researcher-9) — quantitative bound via Bertrand

Extended `Erdos771Construction.lean` (now 6 thm/4 def, 0 axioms, 0 sorries, VERIFIED) with a
quantitative strengthening of `exists_avoiding_multiples`:
- `prime_gt_not_dvd`: a prime `p > m ≥ 1` cannot divide `m` (else `p ≤ m` by `Nat.le_of_dvd`).
- `exists_avoiding_multiples_quantitative`: via Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`), for every `m ≥ 1` there is a prime `m < p ≤ 2m`,
  giving an `m`-avoiding subset of `{1,…,n}` of size `⌊n/p⌋ ≥ ⌊n/(2m)⌋`. Size bound via
  `Nat.div_le_div_left hp2m hp.pos` (Nat division is antitone in the denominator).

### Why this matters
The bare existence used *some* prime `> m`, possibly enormous (least prime ∤ `m = lcm{2,…,t}`
grows with `t`), so `⌊n/p⌋` could be tiny. Bertrand pins the prime to within a factor of two
of `m`, turning existence into an explicit size lower bound.

### Still open
The per-m bound `⌊n/(2m)⌋` weakens as `m` grows; the n/log n lower bound needs a
uniform-over-all-m argument (primes near log n) not formalized here. Asymptotics remain external.

### Gotchas
- Docker down → offline typecheck with `LAKE_UNSAFE=1 elan run leanprover/lean4:v4.26.0 lake env
  lean Proofs/Erdos771Construction.lean`. Main repo's shared `.lake` had a CORRUPT
  `Mathlib/Data/Nat/Bits.olean.private` (invalid header) → typechecked in a sibling worktree
  (`r8-picard`) with an intact Mathlib build instead.
- `Nat.div_le_div_left (h : a ≤ b) (hpos : 0 < a) : k / b ≤ k / a` — args are the *smaller*
  denominator's `≤` and positivity.

## Session 2026-07-07 (researcher-5) — repaired Erdos771Problem.lean; sorries 7→3

The gallery's canonical `proofRepoPath` (`Erdos771Problem.lean`) had been non-compiling
since the Mathlib 4.26.0 bump. Repaired it and discharged 4 of the 7 sorries; it now **builds
clean** (0 build errors, 3 sorries, 2 axioms).

### Compile fixes
- `import Mathlib` (replaced the 6 stale specific imports; `…/BigOperators/Group/Finset` is now
  a directory).
- `AvoidSum · m` `DecidablePred` synthesis failed → supply it classically via `open Classical in`
  on the (already `noncomputable`) `maxAvoidingSize`. **Do NOT** add a computable `Decidable`
  instance referencing the `noncomputable` `subsetSums` — that compiled but segfaulted the C
  codegen (exit 139/135).
- `f`'s `inf'` nonemptiness: switched to dependent `if h : n = 0`, proving `1 ≤ n*n` from
  `h : n ≠ 0` via `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h h)` (the old `by simp` was
  unprovable — `Icc 1 (n*n)` is empty at n=0).
- Removed 4 dangling `/-- … -/` doc-comments that were followed by `/- … -/` blocks (parse error
  `unexpected token; expected 'lemma'`). Same trap: `open Classical in` must precede the
  doc-comment, not sit between it and the `def`.

### Sorries discharged (7→3)
- `prime_multiples_size`, `prime_multiples_avoid` — ported verbatim from the verified
  `Erdos771Construction.lean`.
- `erdos_graham_conjecture_true` — combined the two axiomatic bounds. For `n ≥ 2`, `L = n/log n > 0`,
  and the lower/upper bounds squeeze `f n / L ∈ [1/2−ε/2, 1/2+ε/2]`, giving
  `|f n/L − 1/2| ≤ ε/2 < ε`. Uses `div_le_iff₀`/`le_div_iff₀` (the `₀` forms — plain `div_le_iff`
  is deprecated) and `Real.log_pos`.
- `leading_constant` — the `Tendsto … (nhds (1/2))` limit form, via `Metric.tendsto_atTop` +
  `Real.dist_eq`, is now a one-liner off `erdos_graham_conjecture_true`.

### Remaining (3 sorries)
- `f_characterization` — relate the `inf'/sup` definition of `f` to `f_property`.
- `m_eq_one_case` (`maxAvoidingSize n 1 = n-1`) and `m_eq_two_case` (`≥ n-2`) — both need a
  "subset sum equals a small target ⟺ membership" lemma to bound the `sup` over the powerset.

### Axioms (kept, honest)
`erdos_graham_lower_bound`, `alon_freiman_upper_bound` — the deep Erdős–Graham / Alon–Freiman
bounds. Genuinely external; status stays `axiomatized`.

### Build gotcha
Codegen crash (exit 135/139) in this Docker env is **nondeterministic and masks real errors** —
tail of the log showed only the crash; a full `> log 2>&1` capture revealed the actual parse
error. Always capture full output when a build "crashes" with no diagnostic.

## Session 2026-07-09 (researcher-3) — companion sorry-elimination (Erdos771ProblemAristotle)

Erdos771Problem.lean is 0-sorry/2-axiom (deep erdos_graham_lower_bound + alon_freiman_upper_bound,
external/irreducible). Erdos771Construction.lean verified 0/0. The Aristotle companion
`Erdos771ProblemAristotle.lean` still carried 2 sorries (prime_multiples_size, prime_multiples_avoid)
— both ALREADY verified in Construction.lean. Ported verbatim (identical defs modulo `primeMutliples`
typo), companion now 0-sorry/0-axiom. PR #36849.
- prime_multiples_size: rw Icc_n=Ioc 0 n (omega) + `Nat.Ioc_filter_dvd_card_eq_div n p`.
- prime_multiples_avoid: intro hmem; mem_filter/mem_image/mem_powerset; `Finset.dvd_sum` (each elt
  p∣·) then hpm.

★UNVERIFIED — docker infra DOWN this session: `containerd metadata.db input/output error`, image
rebuild impossible (cached-image builds also unavailable now). Proofs are verbatim ports of
verified Construction.lean code → correctness inherited. Still open (unchanged): deep asymptotics
f(n)=(1/2+o(1))n/log n, the 2 external axioms. Erdos771Aristotle.lean still has 4 sorries (separate
companion; not addressed).

## Session 2026-07-09 (researcher-2) — structural: maxAvoidingSize monotone in n (0-axiom)

Added to `Erdos771Problem.lean` (does NOT touch the companion `Erdos771Aristotle.lean`
under active PR #37121):
- `maxAvoidingSize_le_succ (n m)`: `maxAvoidingSize n m ≤ maxAvoidingSize (n+1) m`.
- `maxAvoidingSize_monotone (m) : Monotone (fun n => maxAvoidingSize n m)`.

Enlarging the box `{1,…,n} ⊆ {1,…,n+1}` can only enlarge the family of `m`-avoiding
subsets (the `AvoidSum S m` predicate depends only on `S,m`, not the box), so the
`sup`-of-cardinality is non-decreasing. Proof: `apply Finset.sup_mono` on the unfolded
goal (kept the `filter`'s classical decidability instances aligned with the `open
Classical`-based def — a fresh `filter` term would have mismatched), then
`mem_filter`/`mem_powerset` + `Finset.Icc_subset_Icc (le_refl 1) (Nat.le_succ n)`.
This is the `maxAvoidingSize` analogue of the counting-function monotonicity used in
erdos-748, complementing the existing lower bounds (`interval_avoiding_lower`,
`primeMultiples_avoiding_lower`) and upper bound (`maxAvoidingSize_le`).

**UNVERIFIED** — docker infra down, no local Mathlib oleans this session. All lemma
names/signatures checked vs pinned `proofs/.lake/packages/mathlib`
(`Finset.sup_mono`, `Finset.powerset_mono`, `Finset.filter_subset_filter`,
`Finset.Icc_subset_Icc`, `monotone_nat_of_le_succ`); proof mirrors the verified
`maxAvoidingSize_le` in the same file. Substantive status unchanged: 2 deep external
axioms (Erdős–Graham / Alon–Freiman) remain BLOCKED.

## Session 2026-07-10 (researcher-3) — exact m=2 case (parallel to merged m=1)

Extended the self-contained `Erdos771Construction.lean` (now 12 thm/4 def, 0 axioms, 0 sorries,
VERIFIED locally) with the exact `m = 2` characterization, mirroring the merged `m = 1` group
(`one_mem_subsetSums_iff`/`avoid_one_iff`/`Icc_two_n_avoid_one`/`avoid_one_card_le`, PR #37364):
- `two_mem_subsetSums_iff`: `2 ∈ subsetSums S ↔ 2 ∈ S`. Among distinct positive naturals the
  only nonempty subset summing to 2 is `{2}` (an element `≥ 3` overshoots via `single_le_sum`;
  the remaining candidates `A ⊆ {0,1}` sum to `≤ 1` via `Finset.sum_le_sum_of_subset` +
  `Finset.sum_pair`).
- `avoid_two_iff`: `AvoidSum S 2 ↔ 2 ∉ S` (negation of the above).
- `Icc_erase_two_avoid_two (n) (hn : 2 ≤ n)`: witness `{1,…,n} ∖ {2}` avoids 2, sits in `{1,…,n}`,
  card `n − 1` (via `Finset.card_erase_of_mem` + `Nat.card_Icc`).
- `avoid_two_card_le (n) (hn : 2 ≤ n)`: optimality — any 2-avoiding `S ⊆ {1,…,n}` has `|S| ≤ n−1`.

Together they pin the exact maximum `n − 1` at `m = 2` for `n ≥ 2` — like `m = 1`, the `m = 2`
constraint does not push the value below `n − 1`. The `n ≥ 2` guard is genuine: at `n = 1`, `{1}`
already avoids 2, so the value is `1 = n`, not `n − 1 = 0`; the merged `m = 1` witness `Icc 2 n`
needs no such guard because `card (Icc 2 n) = n − 1` holds at all `n`.

### Verification
VERIFIED locally (docker image layer down — `docker images` I/O error, `docker info` OK).
Offline: `LEAN_PATH=<mainrepo>/proofs/.lake/packages/*/.lake/build/lib/lean` (NOTE the `/lean`
subdir) with `~/.elan/toolchains/leanprover--lean4---v4.26.0/bin/lean Proofs/Erdos771Construction.lean`
→ exit 0, no warnings, 0 sorries, 0 axioms. GOTCHAS: fresh worktree has no built `.lake` → borrow
the main checkout's oleans; `Finset.not_mem_erase` is deprecated → `Finset.notMem_erase`.

### Still open (unchanged)
Deep asymptotics `f(n) = (1/2 + o(1)) n / log n` (the two external axioms in
`Erdos771Problem.lean`) remain BLOCKED. This file is self-contained and not tracked in gallery
meta → Lean-only increment, no meta sync.

## Session 2026-07-11 (researcher-7) — exact m=4 case (first n−2 plateau)

Extended `Erdos771Construction.lean` (now 20 thm/4 def, 0 axioms, 0 sorries, VERIFIED) with the
exact `m = 4` characterization, continuing the per-`m` ladder (m=1/2/3 merged prior). PR #37665.
- `four_mem_subsetSums_iff`: `4 ∈ subsetSums S ↔ 4 ∈ S ∨ (1 ∈ S ∧ 3 ∈ S)`. Distinct-positive
  subsets summing to 4 are exactly `{4}`, `{1,3}`; all elements ≤4 ≠4 ⇒ `A ⊆ {0,1,2,3}`, then
  the forward `1∈A ∧ 3∈A` is `decide`d over the 16 subsets.
- `avoid_four_iff`, witness `Icc_erase_three_four_avoid_four` (`{1,…,n}∖{3,4}`, card n−2, n≥4),
  optimality `avoid_four_card_le` (n≥4): value pinned to **n−2**, EQUAL to m=3 — first plateau of
  the `n−⌈m/2⌉` staircase (each value held for two consecutive m: m=1,2→n−1; m=3,4→n−2).

### Key difference from m=3 (why decide)
m=3's representation `{1,2}` is the *consecutive* pair, so excluding either 1 or 2 leaves a set
(`{0,2}`/`{0,1}`) whose total `≤2<3` — the crude `Finset.sum_le_sum_of_subset` overshoot bound
isolates it directly. m=4's second representation `{1,3}` is a *gap* pair: excluding 1 leaves
`{0,2,3}` with total `5 ≥ 4`, so the crude bound fails. Deciding over the 16 subsets of `{0,1,2,3}`
sidesteps this cleanly. NB `decide` (kernel), NOT `native_decide` → axiom-free
`[propext,Classical.choice,Quot.sound]`, no `Lean.ofReduceBool`.

### Verification
VERIFIED axiom-free: `./bin/lake env lean Proofs/Erdos771Construction.lean` exit 0; `#print axioms`
on all 4 new thms = the 3 foundational axioms only. Recipe (docker-free, reaper-proof): external
worktree `/Users/rwalters/lg-r7-771` + symlink `proofs/.lake` → main's prebuilt 6.8G oleans, commit
IMMEDIATELY (the `.loom/worktrees/researcher-7` checkout was reverted mid-edit by a concurrent
`git reset` — the recurring shared-checkout thrash).

### Still open (unchanged)
Deep asymptotics `f(n)=(1/2+o(1))·n/log n` (external Erdős–Graham/Alon–Freiman) remain BLOCKED.
Next ladder rung m=5 first drops to n−3 (reps `{5},{1,4},{2,3}` — two disjoint gap pairs).

## Session 2026-07-12 (researcher-2) — GENERAL upper bound n − ⌈m/2⌉ (subsumes the m=1..4 ladder)

**Mode**: FRESH structural generalization (replaces one-off per-m rungs).
**Outcome**: progress (0-sorry/0-axiom, VERIFIED `lake env lean` against real oleans; `#print axioms` = 3 foundational only). PR on branch feature/researcher-2-771.

### What I Did
- Created `proofs/Proofs/Erdos771GeneralUpperBound.lean` (7 decls).
- Proved the **general optimality bound** `avoid_card_le_general`: for `1 ≤ m ≤ n`, any
  `m`-avoiding `S ⊆ {1,…,n}` has `|S| ≤ n − ⌈m/2⌉` (= `n − (m+1)/2` in ℕ). This subsumes the
  hand-proved `avoid_one/two/three/four_card_le` at once and settles the small-`m` regime.

### Route (by mechanism: "disjoint family of m-representations → forced deletions")
- `blk m i` = `{m}` (i=0) or `{i, m−i}` (i≥1): the `⌈m/2⌉` blocks indexed by `i < (m+1)/2`.
- `blk_sum` (each sums to m), `blk_subset` (⊆ {1,…,n} when m≤n), `blk_disjoint` (pairwise
  disjoint over `i < (m+1)/2` — pure `omega`, which handles the ℕ-division bound `(m+1)/2`).
- Since `AvoidSum S m`, no block ⊆ S (`sum_mem_subsetSums` general helper: A⊆S, ∑A=m>0 ⟹
  m∈subsetSums S), so each block meets `D := {1,…,n} \ S`. `Finset.card_biUnion` on the disjoint
  `F i = blk m i ∩ D` gives `|D| ≥ Σ 1 = ⌈m/2⌉`; then `|S| = n − |D| ≤ n − ⌈m/2⌉`.
- `avoid_card_le_general_matches_ladder`: reproduces n−1 (m=2) and n−2 (m=4).

### Gotchas
- `Finset.card_biUnion` wants `(↑s : Set _).PairwiseDisjoint t`, NOT the `∀i∈s∀j∈s,i≠j→Disjoint`
  form — build the `PairwiseDisjoint` term (intro + `mem_coe`+`mem_range`).
- Subset form of card-sdiff is `Finset.card_sdiff_of_subset` (bare `Finset.card_sdiff` is the
  unconditional `#(t\s)=#t−#(s∩t)`).
- omega natively reasons about `(m+1)/2` (ℕ division by a literal) — no manual `2*i ≤ m` needed.

### Files Modified
- `proofs/Proofs/Erdos771GeneralUpperBound.lean` (new)

### Still open (unchanged)
- Deep asymptotics `f(n)=(1/2+o(1))·n/log n` (Erdős–Graham / Alon–Freiman) remain BLOCKED.
- Matching general LOWER bound (a witness of size `n − ⌈m/2⌉` for every `m ≤ n`) — the tightness
  half; the per-m witnesses `{1,…,n}∖(hitting set)` exist for m=1..4, general construction is next.

## Session 2026-07-12 (researcher-2, cont.) — MATCHING general LOWER bound (exact max n − ⌈m/2⌉)

**Outcome**: progress (0-sorry/0-axiom, VERIFIED `lake env lean`). Added to branch/PR of the
upper bound (#38524). Together they pin the EXACT maximum `f_m(n) = n − ⌈m/2⌉` for `1 ≤ m ≤ n`.

### What I Did — `Erdos771GeneralLowerBound.lean` (5 decls)
- Uniform tight witness `avoider n m := (Finset.Icc ((m+1)/2) n).erase m` (delete the ⌈m/2⌉−1
  smallest AND m itself). No case analysis on m.
- `avoider_avoids`: a nonempty subset summing to m lives in {⌈m/2⌉,…,m−1} (bigger elements
  overshoot); a single one is <m, two distinct are ≥ ⌈m/2⌉+(⌈m/2⌉+1)=2⌈m/2⌉+1 > m ⟹ none sums
  to m. `avoider_card` = n − ⌈m/2⌉; `avoider_subset ⊆ {1,…,n}`; `exists_avoiding_card_eq` packages.

### Key formalization facts
- Two distinct elements a≠b both ≥K ⟹ a+b ≥ 2K+1 is pure `omega` (feed a≠b, K≤a, K≤b).
- `Finset.add_sum_erase A (fun x=>x) ha` (= a + Σ_{erase} = Σ) + `Finset.single_le_sum` bound b
  ≤ Σ_{erase}, then `omega` closes vs Σ=m using 2*((m+1)/2) ≥ m.
- singleton case: `Finset.card_eq_one` after `card_pos` (nonempty since Σ=m≥1) + a≠m.

### Status
Small-m regime (1≤m≤n) now EXACTLY resolved: max avoiding-set size = n − ⌈m/2⌉ (upper #38524 +
this lower). Deep asymptotics f(n)=(1/2+o(1))·n/log n (Erdős–Graham/Alon–Freiman) remain BLOCKED.

## Session 2026-07-19 (researcher-1) — INTERMEDIATE-regime upper bound f_m(n) ≤ ⌊m/2⌋ (n < m ≤ 2n)

**Mode**: extend the disjoint-family upper-bound mechanism into the OPEN intermediate regime.
**Outcome**: progress (0-sorry/0-axiom, Docker-GREEN under v4.31.0, foundational axioms only —
no native_decide). New file `proofs/Proofs/Erdos771IntermediateUpper.lean` (3 thms + 1 helper).

### Frontier before this session
The cluster pins the exact value at BOTH ends of the range of m:
- small m (1 ≤ m ≤ n): f_m(n) = n − ⌈m/2⌉ (`Erdos771GeneralUpper/LowerBound`);
- high m (T(n−1) < m ≤ T(n), T(k)=k(k+1)/2): f_m(n) = n − 1 (`Erdos771HighRegime`, #39123).
Open: the **intermediate regime n < m ≤ T(n−1)** — the genuine matching-number core, where the
value is governed by the max number of pairwise-disjoint representations of m in {1,…,n}.

### What I did — pair-only bound for the bottom slice n < m ≤ 2n
Reused the `blk`/`blk_sum`/`blk_disjoint`/`sum_mem_subsetSums` machinery from
`Erdos771GeneralUpperBound` verbatim; only the singleton block `{m}` (no longer ⊆ {1,…,n} once
m > n) is dropped and the pair index restricted so both endpoints stay in range:
`{i, m−i}` for `m−n ≤ i < ⌈m/2⌉`. These `⌈m/2⌉−(m−n)` pairs are pairwise-disjoint m-reps ⊆ {1,…,n}.
- `blk_subset_high`: pairs stay in {1,…,n} (lower index bound m−n≤i ⟹ m−i≤n; i<⌈m/2⌉ ∧ m≤2n ⟹ i≤n).
- `avoid_card_le_intermediate`: f_m(n) ≤ n − (⌈m/2⌉ − (m−n)) for 1≤n, n<m≤2n.
- `avoid_card_le_intermediate_closed`: the RHS is exactly `⌊m/2⌋` (pure omega, ℕ-division).
- `intermediate_top_matches_high`: at m=2n−1 the bound is n−1, matching the high regime — the
  pair-only family stops improving on n−1 there and above.

Combined with the always-valid f_m(n) ≤ n−1 (every m ≤ T(n) is a subset sum of {1,…,n}), this is
`f_m(n) ≤ min(n−1, ⌊m/2⌋)` — a STRICT improvement over n−1 for m ≤ 2n−3. For n ≥ 5 the whole slice
n<m≤2n−1 sits strictly below T(n−1)=n(n−1)/2, so this genuinely advances the open regime.

### Tightness (machine-checked ground truth via brute force, NOT claimed as a theorem)
EXACT at the bottom: f_5(4)=2=⌊5/2⌋, f_6(5)=3, f_7(6)=3, f_8(6)=4, f_7(8)=4, f_9(7)=4.
LOOSE near m=2n (triples add disjoint reps the pair-family misses): f_9(5)=3 < 4=⌊9/2⌋,
f_10(6)=4 < 5, f_14(7)=4 < 7. Pinning the exact value throughout n<m≤T(n−1) remains open.

### Gotchas
- Index over `Finset.Ico (m−n) ((m+1)/2)`; card via `Nat.card_Ico` = `(m+1)/2 − (m−n)`.
- omega natively reasons about both `(m+1)/2` and `m/2` (ℕ division by literal 2) — the closed-form
  `n − ((m+1)/2 − (m−n)) = m/2` under n<m≤2n is a single omega.
- `blk_subset_high` case-splits `mem_blk`; the i=0 (singleton) branch is vacuous under m−n≤i (omega).

### Still open (unchanged)
- Exact value in the UPPER intermediate regime 2n < m ≤ T(n−1) and the loose sub-part of n<m≤2n
  (needs the triple/general-matching count, not just pairs).
- Deep asymptotics f(n)=(1/2+o(1))·n/log n (Erdős–Graham/Alon–Freiman) remain external.
