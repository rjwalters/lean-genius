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

## Session 2026-06-27 (researcher-9) — mod 32: density floor 13/16 → 7/8

**Mode**: REVISIT · **Outcome**: progress (axiom-free)

### What I Did
- Computed (symbolically) which odd residues `r ≡ 3 (mod 4)` mod 32 drop within their
  residue-determined window. Of the 8 such classes, `{3,19}` (= `3 mod 16`, already covered)
  plus the **new** `{11, 23}` drop; `{7,15,27,31}` still have `m`-dependent stopping times.
- Added `mod_thirtytwo_eleven_attainsBelow` (`32m+11 → … → 27m+10`, 8 steps) and
  `mod_thirtytwo_twentythree_attainsBelow` (`32m+23 → … → 27m+20`, 8 steps); every parity
  is forced by `n mod 32` (each intermediate `am+b` has `a` even at the decision).
- Added `attainsBelow_density_lower_32`: `≥ 28N−1` of `[1,32N]` drop below themselves, via
  five pairwise-disjoint image families (`2j`, `4j+1`, `16j+3`, `32j+11`, `32j+23`).
  `16N + (8N−1) + 2N + N + N = 28N−1` ⇒ lower natural density `≥ 7/8`.
- Combined packaging + `colMin` corollaries (`mod_thirtytwo_colMin_lt`, full 7/8 packaging).

### Key Findings
- Determinism budget = power of 2 in the leading coefficient: starting `a = 32 = 2^5`
  allows at most 5 halvings before parity decouples from the residue; that is exactly why
  some lifts stabilise at level 32 and others need a finer modulus.
- The unconditional floor climbs `3/4 → 13/16 → 7/8` at moduli `4, 16, 32`; each newly
  determined residue mod `2^k` contributes `1/2^k` — the Terras stopping-time density
  inching toward 1 by purely elementary residue dynamics.

### Files Modified
- `proofs/Proofs/CollatzStructuredOQ02OQ03.lean` (22 → 28 theorems; +7/8 density theorem)
- `src/data/proofs/collatz-structured-oq-02-oq-03/meta.json` (counts, description, highlights)
- `src/data/research/problems/collatz-structured-oq-02-oq-03.json` (knowledge)

### Verification
`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/CollatzStructuredOQ02OQ03.lean` → EXIT 0 (51s).
`#print axioms` on the four new headline lemmas → only `[propext, Classical.choice, Quot.sound]`
(no `tao_2019`, no `sorryAx`, no `ofReduceBool`).

### Next Steps
- Push to mod 64/128 (lifts of `7,15,27,31 mod 32`); expect floor `7/8 → ~15/16`.
- Tao axiom remains BLOCKED (deep analytic, ≫1000 lines).
