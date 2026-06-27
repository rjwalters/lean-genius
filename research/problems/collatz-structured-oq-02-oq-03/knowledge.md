# Knowledge Base: collatz-structured-oq-02-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-03 asks whether Tao's 2019 almost-all result (logarithmic density 1) can be
formalized in Lean with Mathlib. Tao (2019, *Forum Math. Pi*): for every
`f : ℕ → ℝ` with `f n → ∞`, the set `{n : Col_min(n) < f n}` has **logarithmic
density 1**. This subsumes Terras (1976) / Korec (1994) (almost all n have finite
stopping time, in natural density).

---

## Insights

- **Statement formalizes cleanly.** "Logarithmic density 1" becomes the predicate
  `HasLogDensityOne S := Tendsto (fun N => (∑_{n≤N,n∈S} 1/n)/(∑_{n≤N} 1/n)) atTop (𝓝 1)`.
  `Set.indicator` (classical, no `DecidablePred` needed) handles the filtered sum.
  Tao's theorem is then a single clean `axiom tao_2019` quantified over all `f → ∞`.
- **The elementary half is axiom-free.** Even numbers drop in one step
  (`collatz n = n/2 < n`), and powers of two collapse to 1
  (`collatz^[k] (2^k) = 1`, induction via `collatz (2·m) = m` + `pow_succ'` +
  `Function.iterate_succ_apply`). These give explicit large families in the
  almost-all set without any analysis.
- **Orbit minimum** `colMin n := sInf {m | ∃ k, collatz^[k] n = m}`; `colMin_le_self`
  is just `Nat.sInf_le ⟨0, Function.iterate_zero_apply ..⟩`.
- **Orbit positivity ⇒ `colMin ≥ 1`.** `collatz` preserves positivity
  (`collatz_pos`: even branch `n/2 ≥ 1` for `n>0`, odd branch `3n+1 ≥ 1`), so by
  induction no iterate of a positive start is `0` (`collatz_iterate_pos`). Hence
  `0 ∉` the orbit set, and `Nat.sInf_eq_zero` rules out both disjuncts, giving
  `colMin_pos : 0 < n → 0 < colMin n`. This **sharpens** `colMin_pow_two_le_one`
  to the exact `colMin (2^k) = 1` (orbit hits 1, never goes below).
- **Bridge Parts II↔III.** `attainsBelow_colMin_lt : AttainsBelow n → colMin n < n`
  (just `Nat.sInf_le ⟨k, rfl⟩` then `lt_of_le_of_lt` against the witness step).
  This connects the explicit drop-below families to Tao's `Col_min` predicate at
  `f n = n`, so the whole 3/4-density family (even ∪ `1+4ℕ`) has
  `colMin n < n` unconditionally (`even_or_mod_four_one_colMin_lt`).
- **The 3/4 floor is now a machine-checked counting bound, not prose.**
  `attainsBelow_density_lower : 3*N - 1 ≤ #{n ∈ Icc 1 (4N) | AttainsBelow n}`.
  Proof exhibits two disjoint injective images inside the drop-below set: the evens
  `2,4,…,4N` (`Icc 1 (2N)` under `j ↦ 2j`, card `2N`) and the class `1+4ℕ` with
  value `≥ 5`, i.e. `5,9,…,4N-3` (`Icc 1 (N-1)` under `j ↦ 4j+1`, card `N-1`);
  parity gives `Disjoint`, so `card ≥ 2N + (N-1) = 3N-1` via
  `card_union_of_disjoint` + `card_le_card`. Dividing by `4N`, the drop-below set
  has **lower natural density `≥ 3/4`**, unconditionally and axiom-free
  (`#print axioms` → only `propext/Classical.choice/Quot.sound`; independent of
  `tao_2019`). This is the quantitative floor under Tao's density-one theorem.
  GOTCHAs that cost build cycles: (1) `Finset.image (fun j => 2*j)` leaves
  *beta-redexes* `(fun j => 2*j) i` that `omega` treats as opaque atoms — force
  reduction with `show 2*i % 2 = 0` (goals) or `have h' : 2*a = 2*b := h` (the
  `Injective` hypothesis); (2) the `filter` predicate `AttainsBelow` is not
  decidable, so the *statement* needs `open Classical in` (the in-body `classical`
  tactic is too late); (3) `open Classical in` goes **before** the `/-- … -/`
  docstring, not between docstring and `theorem`.
- **Density is capped at 3/4 for the bounded-step closed-form method.** The
  uncovered residues are exactly `n ≡ 3 (mod 4)`, which *climb* initially
  (`4m+3 ↦ 12m+10 ↦ 6m+5 > n`, then `↦ 9m+8`); no fixed step count with a linear
  closed form drops them below `n` (verified: 11→34→17→52→26→13→…→5 hits below
  only after a non-monotone excursion). Splitting mod 8/16 does not help — the
  2-adic valuations vary with the parameter, so "drops below in *k* steps with a
  closed form" genuinely fails past `1+4ℕ`. Pushing further is equivalent to the
  drop-below conjecture itself, i.e. BLOCKED by elementary means.

---

## Dead Ends / Blockers

- **Full proof of Tao (2019) is BLOCKED.** The proof evolves tuned measures on the
  3-adics and controls their concentration (a transport estimate) plus a
  Fourier-analytic input — none present in Mathlib. A direct formalization is a
  multi-thousand-line project, not a near-term target. So the file states the
  theorem as an axiom and proves only the independent elementary content.
- Suggested intermediate milestone: formalize the Terras/Korec *natural*-density
  stopping-time result first (easier than the logarithmic-density sharpening).

---

## Deliverable

`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` (0 sorries, 1 deep axiom, 17
axiom-free theorems, 5 defs). Gallery entry under
`src/data/proofs/collatz-structured-oq-02-oq-03/`. Build offline (Docker
containerd meta.db still I/O-corrupt): `cd proofs && LAKE_UNSAFE=1 ./bin/lake env
lean Proofs/CollatzStructuredOQ02OQ03.lean` → EXIT 0 (oleans under
`.lake/packages/mathlib/.lake/build/lib/lean/`, 7382 present). `#print axioms` on
the four new colMin lemmas → only `[propext, Classical.choice, Quot.sound]`.

---

## Session 2026-06-27 (researcher-6) - Density floor 13/16 → 7/8 via mod 32

**Mode**: REVISIT (MODERATE knowledge tier)
**Outcome**: progress (axiom-free; offline-verified EXIT 0)

### What I Did
- Computed, for every odd residue mod 32, whether n=32m+r drops below itself within its
  residue-determined window (all step parities forced by n mod 32). Found exactly two NEW
  determined-drop classes beyond the existing 3 (mod 16): **11 (mod 32)** and **23 (mod 32)**,
  each dropping in **8 steps** (Python-verified over m=0..199, single step-count per class).
- Added `mod_thirtytwo_eleven_attainsBelow` (32m+11 → 96m+34 → 48m+17 → 144m+52 → 72m+26
  → 36m+13 → 108m+40 → 54m+20 → 27m+10 < 32m+11) and
  `mod_thirtytwo_twentythree_attainsBelow` (32m+23 → … → 27m+20 < 32m+23), mirroring the
  mod-16 proof style (collatz_odd;ring / collatz_even;omega per step, 8× iterate_succ_apply').
- Added `attainsBelow_density_lower_32`: ≥ 28N−1 of [1,32N] drop below themselves, via five
  pairwise-disjoint image families (evens 2j; 1+4ℕ as 4j+1; 3+16ℕ as 16j+3; 11+32ℕ as 32j+11;
  23+32ℕ as 32j+23), disjoint by residues mod 2/4/16, counted by nested card_union_of_disjoint.
- Added colMin corollaries + combined `even_or_mod_four_one_or_mod_thirtytwo_{attainsBelow,colMin_lt}`.

### Key Findings
- Stable fraction does NOT double per level: 3/4 → 13/16 → 7/8 (gained 1/16 then 1/16), i.e.
  +1 stable residue at level 16, +2 at level 32. Path to density 1 is the Terras
  finite-stopping-time theorem, not a finite residue computation.
- Both new stable classes terminate at coefficient 27 (27m+10, 27m+20): three 3n+1 ascents
  interleaved with five halvings over the 8 forced steps.
- The mod-32 split stabilises the "high half" of an unstable mod-16 class: 7→{23 stable, 7 not},
  11→{11 stable, 27 not}; 15→{15,31 both unstable}. 31 (mod 32) climbs fastest (→243m+242).

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+7 theorems: 22→29; 1 axiom unchanged)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (description, conclusion, highlights, theoremCount)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (knowledge)

### Next Steps
- Push to mod 64/128 (which of 7,15,27,31 mod 32 stabilise mod 64?) — diminishing returns,
  the real milestone is formalizing Terras natural-density-1. Tao axiom remains BLOCKED.
