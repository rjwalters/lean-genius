# Knowledge Base: erdos-564-incomplete-01

Parent: Erdős Problem #564 — 3-uniform hypergraph Ramsey numbers R₃(n).
**OPEN, $500 prize.** Known (Erdős–Hajnal–Rado 1965): 2^{cn²} < R₃(n) < 2^{2^n}.
Erdős asks whether the lower bound can be raised to 2^{2^{cn}} (tower height 2).

---

## Session 1 (2026-06-27, researcher-3): verified tower-growth theory

**Deliverable:** `proofs/Proofs/Erdos564Incomplete01.lean` (110 lines, 11 theorems,
0 defs, **verified 0-sorry 0-axiom** — `#print axioms` lists only
propext/Classical.choice/Quot.sound; the parent's R/EHR axioms and its sorry are
NOT pulled in).

The parent `Erdos564Problem.lean` defines `tower k n = 2↑↑k` from base n but proves
almost no theory of it (only `tower_zero/one/two` and `tower_pos`). Since the whole
problem is phrased in terms of "tower height", that growth theory was the missing
scaffolding. Added:

* `tower_succ`: `tower (k+1) n = 2 ^ tower k n` (rfl rewrite lemma).
* `tower_lt_succ_height`: `tower k n < tower (k+1) n` for ALL k,n — from `m < 2^m`
  (`Nat.lt_two_pow_self`); no positivity hypothesis needed (works at m=0: 0<1).
* `tower_strictMono_height`: `StrictMono (k ↦ tower k n)` via
  `strictMono_nat_of_lt_succ`.
* `self_le_tower`: `n ≤ tower k n` (height-monotone at 0 ≤ k, tower 0 n = n).
* `tower_strictMono_base`: `StrictMono (tower k)` — induction on k, successor step
  composes IH with strict monotonicity of `2^(·)` (`Nat.pow_lt_pow_right`).
* `tower_mono_base`: non-strict corollary.
* `tower_two_eq`: `tower 2 n = 2 ^ (2 ^ n)`.
* `tower_one_lt_tower_two`: **the crux** — `2^n < 2^{2^n}` for every n. This is the
  formal statement that the singly-exponential known lower bound (height 1) sits
  strictly below the doubly-exponential conjectured one (height 2): exactly the gap
  Erdős #564 asks to close.
* Concrete checks: `tower 2 3 = 256`, `tower 3 1 = 16`, `5 ≤ tower 4 5`.

**Parent fix.** `Erdos564Problem.lean` did NOT parse on main: six dangling `/--`
doc comments (lines 65, 66, 153, 154, 164, 186) sat before `/-` block comments /
other doc comments with no intervening declaration → `unexpected token '/--';
expected 'lemma'`. Converted those six to `/-`. Same bug class as the
puiseux-theorem parent fix. (The parent still has its 3 axioms and 1 sorry
`bounds_gap_enormous` — legitimate for an open problem; untouched.)

GOTCHAs (session 1):
* Parent olean was MISSING (file didn't parse, so never built). Had to build it
  single-file AFTER the parse fix: `LAKE_UNSAFE=1 ./bin/lake env lean
  Proofs/Erdos564Problem.lean -o .lake/build/lib/lean/Proofs/Erdos564Problem.olean`
  — note the **extra `lean/` segment** in the dep-olean libdir (`build/lib/lean/Proofs`,
  not `build/lib/Proofs`); `lake env lean` resolves imports against the former.
* Importing a parent with axioms+sorry does not taint downstream `#print axioms`
  unless the theorem transitively uses them — confirmed all 11 results 0-axiom.
* `Nat.lt_two_pow_self` (m < 2^m) and `Nat.pow_lt_pow_right` (strict mono of b^·,
  b>1) are the only nontrivial Mathlib lemmas used.

## Dead ends / deferred
* The open conjecture R₃(n) ≥ 2^{2^{cn}} is out of reach ($500 open problem).
* Parent's `bounds_gap_enormous` (rpow inequality 2^{2^n}/2^{n²} > 10^100, n≥10)
  left as the parent's sorry — provable via `2^n ≥ n²+924` induction + `rpow_sub`
  + monotonicity + `norm_num` on `2^924 > 10^100`, but messy over rpow; deferred.

---

## Iteration 2 (researcher-1, 2026-06-28): parent sorry discharged

Discharged the only `sorry` in the parent `Erdos564Problem.lean`
(`bounds_gap_enormous`, line 205): for `n ≥ 10`,
`2^(2ⁿ) / 2^(n²) > 10¹⁰⁰`.

Proof outline (axiom-free — `#print axioms` = `propext/Classical.choice/Quot.sound`):
- `Real.rpow_sub (0 < 2)` collapses `2^a / 2^b` to the single power `2^(a−b)`.
- Auxiliary `nsq_add_four_hundred_le_two_pow`: `n² + 400 ≤ 2ⁿ` for `n ≥ 10`, by
  `Nat.le_induction` (base `norm_num`; step `2·2^m ≥ 2(m²+400) ≥ (m+1)²+400`,
  closed by `nlinarith [ih, 2m ≤ m²]`). Cast to ℝ ⇒ `2ⁿ − n² ≥ 400`.
- `Real.rpow_le_rpow_of_exponent_le` lifts that to `2^400 ≤ 2^(2ⁿ−n²)`.
- `10¹⁰⁰ < 16¹⁰⁰ = 2⁴⁰⁰` via `Nat.pow_lt_pow_left` + cast (NOT by evaluating
  100-digit literals), then `← pow_mul` for `16^100 = 2^400`.

Gotchas: `pow_lt_pow_left` is gone in Mathlib 4.26 → use `Nat.pow_lt_pow_left`.
`linarith` choked on the `rpow` atoms → finish with `lt_of_lt_of_le`.

Parent now **0 sorries**. The 3 remaining `axiom`s (`R`, `erdos_hajnal_rado_upper`,
`erdos_hajnal_rado_lower`) are the legitimate open-problem axiomatization (the
hypergraph Ramsey number and the EHR 1965 bounds) — not provable here. The open
conjecture (raising the lower bound to tower height 2, $500) is out of reach.

## Session 2 (2026-06-28, researcher-4): Ramsey-property monotonicity API

**Heads-up for future sessions:** the parent sorry `bounds_gap_enormous` was already
eliminated on `origin/main` by a concurrent researcher (`nsq_add_four_hundred_le_two_pow`,
`+400` margin) — do NOT re-prove it. (researcher-4 independently proved it with a `+924`
margin before noticing the collision; that work was discarded. Lesson: `git show
origin/main:<path> | grep -c sorry` right after claiming.)

Added the **first verified theory of the property predicate** `HasHypergraphRamseyProperty`
itself (the parent only axiomatizes the number `R`). Child file 110→153 lines, 11→13
theorems, still **0-sorry / 0-axiom** (`#print axioms`: propext/Classical.choice/Quot.sound
only; the R/EHR axioms are untouched):

* `hasHypergraphRamseyProperty_mono {k m m' n} (m ≤ m') : property k m n → property k m' n`
  — **vertex monotonicity**. Restrict a colouring of `Fin m'` along `Fin.castLEEmb (m≤m')`,
  solve downstairs, push the clique back up. Key lemmas: `Finset.subset_map_iff`
  (`s ⊆ t.map f ↔ ∃ u ⊆ t, s = u.map f`), `Finset.card_map`. The clique-membership goal
  closes by `simpa using hSmono e …` (beta-reduces the restricted colouring `c' (e.map f)`).
* `hasHypergraphRamseyProperty_antitone_clique {k m n n'} (n' ≤ n) : property k m n →
  property k m n'` — **clique-size antitonicity**. Take an `n'`-subset of the solved clique
  via `Finset.le_card_iff_exists_subset_card.mp (hScard ▸ hnn)`; its k-subsets are k-subsets
  of the original clique, so still monochromatic.

These are the structural facts that make `R k n` (least `m` with the property) a sensible
*threshold*: the good-`m` set is upward closed, and `R k ·` is monotone in clique size.

GOTCHAs (session 2): `Fin.castLEEmb (h : n ≤ m) : Fin n ↪ Fin m` is the embedding;
`Finset.le_card_iff_exists_subset_card : n ≤ s.card ↔ ∃ t ⊆ s, t.card = n` is the
subset-of-given-size lemma (NOT `exists_smaller_set`/`exists_subset_card_eq` in this Mathlib).

## Iteration (researcher-3, 2026-06-28): faithful quadratic crux + general height gap

**Mode**: BUILD (Docker down; offline `LAKE_UNSAFE=1 ./bin/lake env lean`, REAL_EXIT 0, clean).
**Base**: rebased onto origin/main 153-line/13-thm version (which already had the Ramsey
monotonicity session) — caught that my initial worktree base was a stale 110-line snapshot
and re-applied onto the current file rather than clobbering the merged Ramsey lemmas.

### What I Did
The file's crux `tower_one_lt_tower_two` compares `2^n < 2^{2^n}` (LINEAR exponent), but the
real EHR lower bound is `2^{cn²}` — a QUADRATIC exponent. Added the faithful form:
- `nsq_lt_two_pow_self {n} (5 ≤ n) : n^2 < 2^n` — `Nat.le_induction` from base `25 < 32`;
  step `2m+1 ≤ m²` (`nlinarith [hm]`) + ih to clear `(m+1)² < 2^m + 2^m = 2^{m+1}`. Tight at n=4.
- `ehr_lower_lt_tower_two {n} (5 ≤ n) : 2^(n^2) < tower 2 n` — the genuine gap: the
  quadratic-exponent known lower bound `2^{n²}` is still a whole tower level below the
  conjectured `2^{2^n} = tower 2 n`. More faithful to Erdős #564 than the linear crux.
- `tower_lt_of_height_lt {j k n} (j < k) : tower j n < tower k n` — general height gap.

### Verification
- `#print axioms` on all three → foundational only; NONE of the parent's 3 axioms pulled in.
- 13→16 theorems, 153→192 lines, 0 axioms, 0 sorries. The open conjecture ($500) stays out of reach.

## Session (researcher-2, 2026-06-30): triviality boundary of the Ramsey property

**Mode**: SOLVED→look-outward (sharp boundary). File 192→259 lines, 16→20 thm,
still 0-axiom / 0-sorry (`#print axioms` of the new headline = propext/Classical.choice/
Quot.sound; parent R/EHR axioms untouched). VERIFIED via docker-build.

The monotonicity API (sessions 1–2) described how the property *propagates* but had **no
base case**. Added the triviality boundary — `R_k(n) = n` for `n ≤ k`:
- `hasHypergraphRamseyProperty_clique_zero` — n=0, S=∅, only subset ∅ monochromatic (c ∅).
- `hasHypergraphRamseyProperty_clique_lt_uniformity (hn : n<k) (hnm : n≤m)` — n-clique has
  no k-subsets ⟹ edge condition vacuous; witness any n-set, colour `true`. Edge contradiction
  via `e.card ≤ S.card = n < k` + omega.
- `hasHypergraphRamseyProperty_diagonal_base (hkm : k≤m)` — n=k, only k-subset of a k-set is
  itself (`Finset.eq_of_subset_of_card_le`), colour := c S.
- `hasHypergraphRamseyProperty_of_clique_le_uniformity (hn : n≤k) (hnm : n≤m)` — unified
  via `rcases lt_or_eq_of_le hn`. The sharp statement that R₃(n) is degenerate for n ≤ 3,
  so Erdős #564's content lives strictly above the diagonal.

GOTCHAs: this Mathlib uses `Finset.le_card_iff_exists_subset_card` (n ≤ s.card ↔ ∃ t⊆s, card=n)
to extract a fixed-size subset — NOT `exists_subset_card_eq`. Build `n ≤ univ.card` for Fin m
by `simpa using hnm` (univ.card → Fintype.card (Fin m) → m). `Finset.eq_of_subset_of_card_le
he (le_of_eq (hScard.trans hecard.symm))` for the n=k single-subset step.

The open $500 conjecture (R₃(n) ≥ 2^{2^{cn}}) remains out of reach.
