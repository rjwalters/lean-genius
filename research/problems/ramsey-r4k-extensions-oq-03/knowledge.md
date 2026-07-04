# Knowledge Base: ramsey-r4k-extensions-oq-03

Insights accumulated during research on this problem.

---

## PART XIII — general deletion-window theorem unifying the M=0/M=1 special cases (researcher-14, 2026-07-04)

**Mode**: REVISIT (RICH, score 33). **Outcome**: progress (+1 general theorem
`ramsey_deletion_window` in `RamseyR4kExtensionsOQ03Deletion.lean`; two existing
theorems refactored into one-line corollaries; still 0 sorries / 0 axioms).
**Machine-verified**: docker-build clean, 7744 jobs, exit 0; `#print axioms
ramsey_deletion_window` = `propext / Classical.choice / Quot.sound` only (Tier-A
axiom-free).

### What this closes
PART X extracted the `M=1` regime as `ramsey_deletion_one_past`, and
`ramsey_deletion_generalizes_first_moment` handled `M=0`, but the two lived as
separate ad-hoc theorems keyed to specific floor values. This session states the
**one** general mechanism they are both instances of.

### Shipped
- **`ramsey_deletion_window (hk : 2 ≤ k) (hkn : k ≤ n) (M : ℕ)
  (hlo : M·2^C(k,2) ≤ 2·C(n,k)) (hhi : 2·C(n,k) < (M+1)·2^C(k,2))`** ⇒ a 2-colouring
  `c` of `Kₙ` and a set `R` with `n − M ≤ |R|` and no monochromatic `Kₖ`, i.e.
  `R(k,k) > n − M`. The window pair pins `⌊2·C(n,k)/2^C(k,2)⌋ = M` exactly
  (`Nat.le_div_iff_mul_le` + `Nat.div_lt_iff_lt_mul` + `omega`), then chains
  `ramsey_deletion`. Stated by window index instead of the raw floor.
- **Refactor**: `ramsey_deletion_generalizes_first_moment` is now the `M=0` corollary
  (`(by simp) (by simpa using hbound)`), `ramsey_deletion_one_past` the `M=1` corollary
  (`ramsey_deletion_window hk hkn 1 (by simpa using hlo) (by simpa using hhi)`). Both
  keep their **exact original signatures**; the concrete k=6/7/8 witnesses are untouched.

### Gotcha (reconfirmed, important)
The `.loom/worktrees/researcher-14` "worktree" is NOT an isolated git worktree — its
`show-toplevel` is the main repo and a background deployer runs `git reset --hard
origin/main` on that shared checkout on a short cycle, silently wiping uncommitted edits
mid-session (reflog shows repeated `reset: moving to origin/main`). Edits + a full docker
build were destroyed once this way. Fix that worked: `git worktree add -b <branch>
/Users/rwalters/lg-wt/<name> origin/main` (a *genuine* external worktree under
`/Users/rwalters/lg-wt`, NOT `/tmp` — macOS cleans `/private/tmp` and removed the first
attempt), edit + build + commit + push entirely there.

### Still open (unchanged)
`SymmetricLLLForRamsey` (Spencer's conditional-probability induction + the probability-
space construction and mutual-independence `hindep`) remains the >1000-line measure-theory
undertaking flagged BLOCKED since PART VIII. See sibling `lovasz-local-lemma-oq-01`.

---

## PART XII — machine-checked deletion witness at k=8 (R(8,8)>45, +3 over union bound) (researcher-14, 2026-07-03)

**Mode**: REVISIT (RICH, score 33). **Outcome**: progress (+2 verified theorems in
`RamseyR4kExtensionsOQ03Deletion.lean`; still 0 sorries / 0 axioms).
**Machine-verified**: docker-build clean, 7744 jobs, exit 0; `#print axioms` =
`propext / Classical.choice / Quot.sound` only (Tier-A axiom-free) for both new theorems.

### What this closes
The deletion-method family had concrete witnesses at k=6 (R(6,6)>18, +1) and k=7
(R(7,7)>29, +2). This session extends the sequence to **k=8, continuing the +1, +2, +3
gain pattern**, so the "deletion strictly beats the sharp union bound" phenomenon is now
witnessed at three consecutive `k`.

### Shipped
- **`unionBound_caps_at_42_for_K8`**: `2·C(42,8)=236060370 < 2^28=268435456` and
  `¬(2·C(43,8)=290017026 < 2^28)` ⇒ the sharp union/first-moment test caps at n=42,
  i.e. R(8,8)>42.
- **`deletion_no_mono_K8`**: at n=46, k=8, `deletionBound 46 8 = 46−⌊2·C(46,8)/2^28⌋
  = 46−⌊521865630/268435456⌋ = 46−1 = 45` ⇒ a 2-colouring of K₄₆ and a set R with
  `45 ≤ |R|` and no monochromatic K₈, i.e. **R(8,8)>45 (+3 over the union bound)**.
  `n=46` is the *top* of the M=1 window for k=8 (`2^28 ≤ 2·C(46,8) < 2·2^28`; C(47,8)
  already forces M=2), so it is the largest bound `ramsey_deletion_one_past` yields here.

### Technique / gotcha (reconfirmed)
The k=8 binomials (`C(42,8), C(43,8), C(46,8) ≈ 10⁸`) are far past the naive
`decide`-on-`Nat.choose` range, so all three are evaluated via
`Nat.choose_eq_descFactorial_div_factorial` (single-recursion `descFactorial`, `k` kernel
multiplications), staying axiom-free (`of_decide_eq_true`, no `Lean.ofReduceBool`). The
final `deletionBound`/inequality `decide`s then operate on plain ℕ literals. No
`maxHeartbeats` bump was needed (the k=6 witnesses need it only because they `decide` on
raw `Nat.choose`). Python-verified: k=8 union cap at n=42, M=1 window top at n=46, giving
deletionBound 45.

### Still open (unchanged)
The symmetric-LLL avoidance principle `SymmetricLLLForRamsey` (Spencer's conditional-
probability induction) remains the one non-Mathlib ingredient — the >1000-line
measure-theoretic undertaking flagged BLOCKED since PART VIII. See sibling
`lovasz-local-lemma-oq-01`.

---

## PART XI — both numeric premises of `avoidance_pos` discharged for the Ramsey events (researcher-8, 2026-07-04)

**Mode**: REVISIT (RICH, score 29). **Outcome**: progress (+2 theorems in
`RamseyR4kExtensionsOQ03.lean`; +1 pre-existing-breakage repair; still 0 sorries/0
axioms). **Machine-verified**: docker-build clean, 7744 jobs, exit 0 (worktree +
`LEAN_SKIP_CACHE=true` build). Tier-A axiom-free by construction (no
decide/native_decide/sorry/axiom; deps `ErdosRamseyLowerBound` + Mathlib are 0-axiom).

### What this closes
The general asymmetric LLL `LovaszLocalLemmaOQ01StrongInduction.avoidance_pos` consumes
two numeric hypotheses (besides the measure-theoretic `hindep`): `hx1` (`xᵢ < 1`) and
`hlll` (`μ(Aᵢ) ≤ xᵢ·∏_{j∈S₁}(1-xⱼ)` for every all-neighbour sub-block `S₁`). PART VII–IX
proved the *full-neighbourhood* numeric bound `cliqueMonoProb_le_symmetric_lll_rhs`
(`p ≤ x·(D/(D+1))^D`), but the **per-sub-block** form `avoidance_pos` actually needs was
only asserted in a docstring comment. This session makes both premises theorems.

### Shipped (`RamseyR4kExtensionsOQ03.lean`)
- **`symmetric_reserved_lt_one` `(hk : 2 ≤ k) (hkn : k ≤ n)`** ⇒ `1/(D+1) < 1`. Valid
  because `D = cliqueDependencyBound n k = k.choose 2 · (n-2).choose (k-2) ≥ 1` for
  `2 ≤ k ≤ n` (both factors positive by `Nat.choose_pos`). This is the `hx1` premise.
- **`cliqueMonoProb_le_symmetric_lll_block` `(hcond) (S₁) (hcard : |S₁| ≤ D)`** ⇒
  `p ≤ (1/(D+1))·∏_{j∈S₁}(1 - 1/(D+1))`. In the symmetric instantiation `xⱼ ≡ 1/(D+1)`
  the product is `(D/(D+1))^{|S₁|}`; since the base `D/(D+1) ∈ [0,1]`, shrinking the
  exponent from `D` to `|S₁| ≤ D` only increases it (`pow_le_pow_of_le_one`), so chaining
  the existing full-neighbourhood bound gives the block form. This is the `hlll` premise.

### Reusable gotchas (researcher-8)
- **Rebuild exposes latent `field_simp; ring`.** `cliqueMonoProb_le_symmetric_lll_rhs`
  shipped (and merged) with `_ = ... := by field_simp; ring`, but the *current* Mathlib
  4.26 `field_simp` closes that goal outright, so `ring` errors `No goals to be solved`.
  Merged gallery files are NOT always re-verified from scratch against the live cache;
  a from-scratch rebuild can surface such breakages. Fix: drop the redundant `ring`.
- **`pow_le_pow_of_le_one (0≤a) (a≤1) (m≤n) : a^n ≤ a^m`** is the ℝ lemma for shrinking
  the exponent of a `≤1` base (the primed monoid version `pow_le_pow_right_of_le_one'`
  drops the `0≤a` arg but is for ordered monoids, not ℝ directly).
- **Build recipe that dodges the deployer sync revert**: run `docker-build.sh` FROM an
  external worktree with `LEAN_SKIP_CACHE=true` after hardlinking `.lake/packages`. The
  main tree is on `chore/sync-data-*` and its sync reverts staged edits mid-build.

### Still open (unchanged)
Only `hindep` (mutual independence of the monochromatic-clique bad events under the
uniform edge-colouring measure, based on edge-disjointness) plus the probability-space
construction and the positivity⇒existence extraction remain to discharge
`SymmetricLLLForRamsey` outright — the >1000-line measure-theory undertaking flagged
BLOCKED since PART VIII. See sibling `lovasz-local-lemma-oq-01`.

---

## PART X — the general `M=1` gain theorem unifying the k=6/k=7 witnesses (researcher-14, 2026-07-03)

**Mode**: REVISIT (RICH, score 29). **Outcome**: progress (+1 general theorem
`ramsey_deletion_one_past` in `RamseyR4kExtensionsOQ03Deletion.lean`; still 0 sorries/0
axioms). **Machine-verified**: docker-build clean, 7744 jobs, `#print axioms` =
`propext / Classical.choice / Quot.sound` only (Tier-A axiom-free).

### What this closes
PARTS VIII/IX shipped the concrete deletion witnesses `deletion_no_mono_K6` (R(6,6)>18,
n=19) and `deletion_no_mono_K7` (R(7,7)>29, n=30) as *ad-hoc* `decide`-on-`deletionBound`
calculations. Both land in the same structural regime — one step past the sharp union
threshold, where the deletion count `M = ⌊2·C(n,k)/2^C(k,2)⌋ = 1`. This session extracts
that regime as a **general, k-uniform theorem** so the concrete witnesses become instances
of a stated mechanism rather than isolated numeric facts.

### Shipped
- **`ramsey_deletion_one_past (hk : 2 ≤ k) (hkn : k ≤ n)
  (hlo : 2^C(k,2) ≤ 2·C(n,k)) (hhi : 2·C(n,k) < 2·2^C(k,2))`** ⇒ a 2-colouring `c` of
  `Kₙ` and a set `R` with `n − 1 ≤ |R|` and no monochromatic `Kₖ`.
  Reading: `hlo` says the union-bound test `2·C(n,k) < 2^C(k,2)` *fails* at `n` (first
  moment certifies nothing on all of Kₙ); the pair pins `M = 1`, so deletion still keeps
  `n − 1` vertices. This is exactly the +1-over-the-threshold gain, uniform in `k`.
- Verified both concrete witnesses sit in this window (Python + kernel): k=6,n=19:
  `2^15=32768 ≤ 54264 < 65536`; k=7,n=30: `2^21=2097152 ≤ 4071600 < 4194304`. Both give
  `deletionBound = n−1` (=18, =29), matching PARTS VIII/IX.

### Reusable gotcha (researcher-14)
- **`M = 1` collapse without nonlinear `omega`.** To prove `x/b = 1` from `b ≤ x < 2b`
  with `b` a *variable* (`b = 2^C(k,2)`), `omega` alone fails (it can't reason about the
  variable division). Route through the two `Nat` div-iff lemmas to turn the quotient into
  linear facts, then `omega`:
  `rw [Nat.le_div_iff_mul_le hbpos]` reduces `1 ≤ x/b` to `1·b ≤ x` (`simpa using hlo`);
  `rw [Nat.div_lt_iff_lt_mul hbpos]` reduces `x/b < 2` to `x < 2·b` (`exact hhi`, matches
  the RHS `n*k` shape exactly with n=2). Then `1 ≤ x/b` and `x/b < 2` give `x/b = 1` by
  `omega`. This is the k-uniform replacement for PART VIII/IX's per-witness
  `decide`-on-`deletionBound`, and needs NO large binomial evaluation.

### Still open (unchanged)
The symmetric-LLL avoidance principle `SymmetricLLLForRamsey` (Spencer's conditional-
probability induction) remains the one non-Mathlib ingredient — a >1000-line measure-
theoretic undertaking. See sibling `lovasz-local-lemma-oq-01`.

---

## PART VIII — the deletion method STRICTLY beats the sharp union bound (researcher-14, 2026-07-03)

**Mode**: REVISIT (RICH, score 25). **Outcome**: progress (+1 def, +3 theorems in
`RamseyR4kExtensionsOQ03Deletion.lean`; still 0 sorries / 0 axioms).
**⚠️ Machine-verification BLOCKED**: host disk 100% full (181Mi free), Docker.raw full
→ mathlib cache `leantar` decompress fails with ENOSPC; no complete olean set exists in
any worktree. Arithmetic independently verified in Python; Lean hand-audited; NOT built.

### The narrative gap this closes
PART VII established (honestly) that the symmetric LLL *as set up in this entry* does
NOT beat the sharp first-moment/union bound at small `k` (LLL caps `R(6,6)>13`,
`R(7,7)>22`; sharp union bound gives `R(6,6)>17`, `R(7,7)>27`). Open question left
implicit: does ANY elementary probabilistic upgrade beat the sharp union bound at
those `k`? **Answer: the deletion/alteration method does.** The union bound is the
`M=0` special case of `ramsey_deletion`; keeping the surviving set past the threshold
`deletionBound n k = n − ⌊2·C(n,k)/2^{C(k,2)}⌋` strictly exceeds it.

### Numbers (Python-verified)
- **k=6**: union bound feasible up to n=17 (`2·C(17,6)=24752<2^15`; fails at 18:
  `2·C(18,6)=37128≥32768`) ⇒ `R(6,6)>17`. Deletion max `deletionBound n 6 = 18`,
  attained at n=19 (`M=⌊54264/32768⌋=1`, 19−1=18) and n=20..22 ⇒ `R(6,6)>18`. **+1.**
- **k=7**: union bound up to n=27 (`2·C(27,7)=1776060<2^21`; fails at 28) ⇒ `R(7,7)>27`.
  Deletion max 29 at n=30..36 ⇒ `R(7,7)>29`. **+2.** (Prose remark only — see gotcha.)

### Shipped (PART: "DELETION STRICTLY BEATS THE SHARP UNION BOUND")
- `def deletionBound n k := n − (2·C(n,k))/2^{C(k,2)}` — the guaranteed surviving size.
- `ramsey_deletion_bound` — restatement of `ramsey_deletion` in terms of `deletionBound`;
  proved by `:= ramsey_deletion hk hkn` (works by **defeq**: `deletionBound` is a plain
  `def` that unfolds to the exact conclusion expression — no tactic needed).
- `unionBound_caps_at_17_for_K6` — `2·C(17,6)<2^15 ∧ ¬(2·C(18,6)<2^15)`, by `decide`.
- `deletion_no_mono_K6` — ∃ 2-colouring of K₁₉ + set R, `18 ≤ R.card`, no mono K₆; via
  `obtain … ramsey_deletion_bound (n:=19)(k:=6)`, `have h : deletionBound 19 6 = 18 := by
  decide`, `rw [h] at hRcard`.

### Reusable gotchas (researcher-14)
- **`decide` on `Nat.choose` DOES reduce** (structural recursion; empirically the merged
  `unionBound_beats_lll_at_6` proves `2·C(17,6)<2^15` by decide). BUT it is naive
  two-way recursion with ~C(n,k) leaves and NO kernel memoisation, so cost scales with
  the binomial value: `C(17,6)=12376` is default-heartbeat-safe; `C(19,6)=27132` needs a
  `set_option maxHeartbeats 800000 in` bump; `C(30,7)≈2·10⁶` is impractical (dropped k=7
  to a prose remark). Rule of thumb: keep `decide`-on-choose to binomials ≲ 30k.
- **`ramsey_deletion_bound := ramsey_deletion` by defeq**: wrapping an existing bound in a
  named `def` and re-exposing it needs no proof, just term-mode `:= <orig> args`, since
  `theorem T : … := pf` checks `pf`'s type up to `def`-unfolding.
- `decide` is axiom-free (`of_decide_eq_true`); it does NOT add `Lean.ofReduceBool` the
  way `native_decide` would — so the file stays Tier-A axiom-free even with `decide`.

### Still open (unchanged)
The symmetric-LLL avoidance principle `SymmetricLLLForRamsey` (Spencer's conditional-
probability induction) is the one non-Mathlib ingredient; a full formalization is a
>1000-line measure-theoretic undertaking (BLOCKED). See sibling `lovasz-local-lemma-oq-01`.

---

## PART VII — honest comparison with the OPTIMIZED union bound (researcher-4, 2026-07-03)

**Mode**: REVISIT (RICH, score 20). **Outcome**: progress (4 new axiom-free theorems, still 0 sorries/0 axioms, builds Mathlib 4.26).

### Motivation / correction
The entry advertised the LLL as "beating the first moment" via `R(6,6)>13` vs
`R(6,6)>8`. But `8 = 2^{⌊6/2⌋}` is the **weakened closed-form** first moment, not
the sharp optimum. The honest optimized union bound `E[# mono k-cliques] < 1 ⟺
2·C(n,k) < 2^{C(k,2)}` reaches `R(6,6) > 17` and `R(7,7) > 27`, **strictly beating**
the LLL region (13, 22). So the symmetric-LLL setup of this file does **not** improve
on the sharp union bound at small `k`; its factor-`Θ(k)` gain is genuinely asymptotic.

### Added (PART VII in `RamseyR4kExtensionsOQ03.lean`)
- **`firstMomentCondition n k`** `:= 2·C(n,k) < 2^{C(k,2)}` — the sharp union-bound
  test; `Decidable` by `infer_instance` after `unfold`.
- **`lll_core_eq_firstMoment_core`** (`2 ≤ k`): `C(n,2)·(6·d) = 3·C(k,2)²·(2·C(n,k))`.
  Rescale `cliqueDependency_total_identity` by 6 (needs `(n := n) (k := k)` to pin the
  implicit `n` in the standalone `have`, else "don't know how to synthesize `n`").
  Both tests compare their core to the same budget `2^{C(k,2)}`, so the ratio
  `3·C(k,2)²/C(n,2)` is the **exact finite crossover criterion**.
- **`lll_core_le_firstMoment_core`** (`2 ≤ k`, `2 ≤ n`, `3·C(k,2)² ≤ C(n,2)`):
  `6·d ≤ 2·C(n,k)` (LLL more permissive in the large-`n`, `n≳k²` regime).
  `rw [core_eq]; gcongr` then cancel `C(n,2)>0`.
- **`unionBound_beats_lll_at_6` / `_at_7`**: `firstMomentCondition 17 6 ∧
  ¬RamseyLLLCondition 17 6` and same at `(27,7)`; `refine ⟨by decide, ?_⟩;
  rw [ramseyLLLCondition_iff]; decide`.

Numeric check (crossover): `3·C(6,2)² = 675 > 136 = C(17,2)` → small-`n` side, union
bound wins at `k=6`, consistent with the theorems. LLL only overtakes once
`3·C(k,2)² < C(n,2)`, i.e. `n` at least ~quadratic in `k` (the `n≈2^{k/2}` regime).

### Still open (unchanged)
The sole remaining piece is the symmetric-LLL avoidance principle
`SymmetricLLLForRamsey` (Spencer's conditional-probability induction); not in Mathlib.

---

## PART VI — why LLL beats the union bound, quantified (researcher-4, 2026-07-03)

Appended to `RamseyR4kExtensionsOQ03.lean` on top of the decidable-criterion
PART V (integer test `6·(d+1) ≤ 2^{C(k,2)}` + concrete `R(6,6)>13`, `R(5,5)>7`
witnesses). Two axiom-free unconditional theorems (`#print axioms` = only
`propext, Classical.choice, Quot.sound`):

- **`cliqueDependency_total_identity`** (`2 ≤ k`):
  `C(n,2) · cliqueDependencyBound n k = C(k,2)² · C(n,k)`. Double-count
  `(k-clique, edge-inside-it)` incidences via Mathlib's subset-of-a-subset
  identity `Nat.choose_mul (s := 2)`
  (`n.choose k * k.choose 2 = n.choose 2 * (n-2).choose (k-2)`), then two `ring`
  steps around one `rw [← h]`. Gives `d/C(n,k) = C(k,2)²/C(n,2)`: the LLL
  dependency degree is a `Θ(k⁴/n²)` fraction of the total bad-event count — the
  exact reason the *local* LLL test succeeds where the *global* union bound fails.
- **`cliqueDependencyBound_le_total`** (`2 ≤ k`, `2 ≤ n`, `C(k,2)² ≤ C(n,2)`):
  `d ≤ C(n,k)`. Cancel `C(n,2) > 0` via
  `le_of_mul_le_mul_left … (Nat.choose_pos hn)`; `≤` side by `gcongr`.

**Gotcha**: `Nat.choose_mul` is in `Mathlib/Data/Nat/Choose/Basic.lean:160`,
`{n k s} (hsk : s ≤ k) : n.choose k * k.choose s = n.choose s * (n-s).choose (k-s)`;
instantiate `(s := 2)`, feed `hk : 2 ≤ k`. `ring` works over ℕ since `n-2`, `k-2`
stay opaque atoms.

**Remaining gap unchanged**: the only non-Mathlib ingredient is the
measure-theoretic step inside `SymmetricLLLForRamsey` (positive avoidance
probability ⇒ existence). All numeric/combinatorial content is now discharged.
See sibling `lovasz-local-lemma-oq-01`.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### Key Lemma decomposition of the LLL-for-Ramsey input (researcher-5, 2026-07-03)

The symmetric LLL feasibility test `e·p·(d+1) ≤ 1` needs exactly two
Ramsey-specific quantities, both of which are **pure finite counting** and
independent of the (unformalized) measure-theoretic LLL machinery:

- **Key Lemma 3 — dependency degree `d`.** `#{T : |T|=k, |S∩T|≥2} ≤
  C(k,2)·C(n−2,k−2)`. Lives in `Proofs/RamseyR4kExtensionsOQ03.lean`
  (namespace `RamseyLLL`). Cover the dependency set by the C(k,2) fixed-edge
  families; each edge anchors ≤ C(n−2,k−2) cliques via `T ↦ T∖e`.
- **Key Lemma 2 — bad-event probability `p`.** `p = 2^{1−C(k,2)}`. SHIPPED this
  cycle as gallery `ramsey-r4k-extensions-oq-03-oq-01`,
  `Proofs/RamseyR4kExtensionsOQ03OQ01.lean` (0-axiom, 0-sorry, verified;
  `#print axioms` = only propext/Classical.choice/Quot.sound). A k-clique has
  C(k,2) edges ⇒ 2^{C(k,2)} colourings, of which exactly two are constant
  (`card_constant_colorings`: over any nonempty finite domain the constant
  Bool-colourings are the injective image of `Bool`, so there are exactly 2).
  `clique_monochromatic_probability` divides to get `2/2^{C(k,2)} = 2^{1−C(k,2)}`
  in ℝ via `zpow_sub₀`.

### Reusable Lean gotchas (researcher-5, 2026-07-03)

- `Fintype.card (α → Bool)` via `Fintype.card_fun` (needs `[DecidableEq α]`),
  and `Fintype.card {e // e ∈ s}` via `Fintype.card_coe = s.card`.
- Injective-image counting: `Finset.card_image_of_injective s hinj` takes the
  Finset explicitly and injectivity explicitly (f implicit).
- `card_constant_colorings` is stated for codomain `Bool`; instantiate the
  *domain* (the edge subtype) as `α`, NOT the function type.

---

## Dead Ends / Repair Needed

- **`Proofs/RamseyR4kExtensionsOQ03.lean` (Key Lemma 3) does NOT build under
  Mathlib 4.26 as of 2026-07-03** — it was left as untracked WIP by an earlier
  researcher and never merged. Multiple API-drift failures in
  `edge_containing_cliques_card_le`: `Finset.card_le_card_of_injOn` now hands the
  "maps into" hypothesis with `∈ ↑s` (Set coercion), so `rw [Finset.mem_filter,
  Finset.mem_powersetCard] at hT` fails (pattern `_ ∈ filter _ _` not found — need
  `Finset.mem_coe` first); `Finset.card_sdiff (Finset.subset_univ e)` reports
  "function expected"; and the final injectivity step needs `heq` beta-reduced
  (`have hsdiff : T1 \ e = T2 \ e := heq` works, plain `rw [heq]` does not).
  Key Lemma 2 was shipped standalone precisely because it is self-contained and
  verified; repairing Key Lemma 3 is the next incremental step.

## PART IX — machine-checked deletion witness at k=7 + Deletion-file compile repair (researcher-8, 2026-07-04)

**Mode**: REVISIT (RICH, score 26). **Outcome**: progress (+2 verified theorems; repaired a
pre-existing compile error). **Machine-verified**: docker-build clean, 7744 jobs, all 5
Deletion-file theorems axiom-free (`propext / Classical.choice / Quot.sound` only).

### What this closes
PART VIII proved the general `ramsey_deletion` theorem (all k) but only shipped a concrete
`k = 6` witness (`deletion_no_mono_K6`, R(6,6)>18); the `k = 7` improvement was left as a
**prose remark** because `decide` on `C(30,7) ≈ 2·10⁶` is impractical (naive two-way
`Nat.choose` recursion, ~C(n,k) leaves, no kernel memoisation). This session makes k=7
machine-checked:
- `unionBound_caps_at_27_for_K7`: `2·C(27,7)=1776060 < 2^21` and `¬(2·C(28,7)=2368080 < 2^21)`
  ⇒ sharp union bound caps at n=27, i.e. R(7,7)>27.
- `deletion_no_mono_K7`: `deletionBound 30 7 = 30 − ⌊2·C(30,7)/2^21⌋ = 30 − ⌊4071600/2097152⌋
  = 30 − 1 = 29` ⇒ a 29-vertex mono-K₇-free 2-colouring of K₃₀, i.e. **R(7,7)>29 (+2 over the
  union bound)**.

### Technique (lifts the researcher-14 decide-on-choose cap for exact values)
To evaluate a large binomial by kernel `decide` without the exponential `choose` blowup,
rewrite `Nat.choose n k = n.descFactorial k / k !` via
`Nat.choose_eq_descFactorial_div_factorial`. `descFactorial` is **single** recursion (k
multiplications on kernel-accelerated `Nat` literals), so
`rw [Nat.choose_eq_descFactorial_div_factorial]; decide` proves `C(30,7)=2035800` instantly
and axiom-free (`of_decide_eq_true`; no `Lean.ofReduceBool`). PART VIII's "keep
decide-on-choose ≲ 30k" rule only applies to the *naive* route; this identity removes it for
exact-value goals.

### Repair (integrity)
`RamseyR4kExtensionsOQ03Deletion.lean` did **not** compile on the current Mathlib pin: both
k=6 witnesses put a `/-- doc -/` comment *before* `set_option maxHeartbeats 800000 in`, which
Lean rejects — a doc comment must attach to a declaration, not to `set_option … in`. Canonical
repo order is `set_option … in` **then** `/-- doc -/` **then** `theorem` (used by ~dozens of
gallery files). Reordered both; whole file now builds clean. (Consistent with the earlier
finding that the parent entry `RamseyR4kExtensions.lean` also silently failed to compile.)

### Still open (unchanged)
The symmetric-LLL avoidance principle `SymmetricLLLForRamsey` (Spencer's conditional-
probability induction) remains the one non-Mathlib ingredient — a >1000-line measure-theoretic
undertaking (BLOCKED). See sibling `lovasz-local-lemma-oq-01`.
