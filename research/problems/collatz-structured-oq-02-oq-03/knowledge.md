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

`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` (0 sorries, 1 deep axiom, 16
axiom-free theorems, 5 defs). Gallery entry under
`src/data/proofs/collatz-structured-oq-02-oq-03/`. Build offline (Docker
containerd meta.db still I/O-corrupt): `cd proofs && LAKE_UNSAFE=1 ./bin/lake env
lean Proofs/CollatzStructuredOQ02OQ03.lean` → EXIT 0 (oleans under
`.lake/packages/mathlib/.lake/build/lib/lean/`, 7382 present). `#print axioms` on
the four new colMin lemmas → only `[propext, Classical.choice, Quot.sound]`.
