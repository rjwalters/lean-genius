# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S2)
**Iteration**: 2

## Current Focus

S2 (researcher-3): ACT iteration delivering the **`g(3)` lower bound**
witness — the first Lean-level deliverable for the OQ-01 child of
`lagrange-four-squares-waring-g2` (parent: $g(2) = 4$).

**Theorem proved (0 sorries, 0 axioms):**
- `WaringG2OQ01.twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23`

**Supporting infrastructure:**
- `WaringG2OQ01.IsSumOfCubes : ℕ → ℕ → Prop` — the `IsSumOf`-style
  predicate specialised to cubes.
- `WaringG2OQ01.representations23_empty` — finite-search lemma over
  the $3^8 = 6561$ tuples `Fin 8 → Fin 3`, discharged by kernel
  `decide`.
- A concrete `example : IsSumOfCubes 9 23` using the canonical
  representation $23 = 2^3 + 2^3 + 7\cdot 1^3$ (`decide`-verified).

**File added:** `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`
(~110 lines including docstrings). Umbrella `proofs/Proofs.lean`
updated to include the new module (alphabetical position after
`Proofs.LagrangeFourSquaresWaringG2`).

## Active Approach

**Two-tier strategy: lower bounds verified, upper bounds axiomatized.**
S2 executes the lower-bound side for $k = 3$ (the smallest non-trivial
case after the parent's $k = 2$).

**Proof technique (S2):** finite search via `decide` on `Fin 8 → Fin 3`.

1. *Bounding step:* if $\sum_{i=0}^{7} (f i)^3 = 23$ then $(f i)^3 \le
   23 < 27 = 3^3$, hence $f i \le 2$ (via `Nat.pow_le_pow_left` and
   `omega`).
2. *Lifting step:* every $f : \text{Fin } 8 \to \mathbb{N}$ with each
   $f i < 3$ lifts to $g : \text{Fin } 8 \to \text{Fin } 3$ with
   `(g i : ℕ) = f i` (definitional via `Fin.val ⟨f i, _⟩`).
3. *Decision step:* `Finset.univ.filter (· cubes sum = 23) = ∅` is
   discharged by `decide` (kernel evaluator, ~6.5k cases, sub-second).

The pattern generalises to all small-$k$ lower bounds; the
`decide`-search is feasible exactly when $\lceil n^{1/k} \rceil^{s+1}$
fits in Lean's evaluator budget:
- $k = 3, n = 23, s = 8$: $3^8 = 6561$ ✓
- $k = 4, n = 79, s = 18$: $3^{18} \approx 4 \cdot 10^8$ ✗ — mod-16
  argument required.
- $k = 5, n = 223, s = 36$: $3^{36}$ ✗ — mod-32 argument required.

## Blockers

None for S2 (verified locally and via Docker build).

Infrastructure note:
- The worktree's `proofs/.lake` symlink resolves to the main repo's
  self-referential `proofs/.lake` (per
  `feedback_researcher_lake_symlink_broken.md`); Docker build does a
  fresh ~25-minute clone of Mathlib + ~10-minute cache fetch. S2 build
  was successful end-to-end (~45 minutes).

## Next Action

**S3 (any researcher): mod-9 / finite-search hybrid for $k = 4$ lower bound.**

The next deliverable is `g4_lower : ¬ IsSumOfCubes 18 79` — wait,
that's the wrong predicate. For $k = 4$ we need:

```lean
def IsSumOfFourthPowers (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 4) = n

theorem g4_lower : ¬ IsSumOfFourthPowers 18 79
```

A pure `decide`-search is infeasible ($3^{18} \approx 4 \cdot 10^8$),
so S3 must use **mod 16 arithmetic**: fourth powers mod 16 are in
$\{0, 1\}$ (since $a^4 \equiv (a \bmod 16)^4 \pmod{16}$, and direct
computation gives $0^4 \equiv 0$, $1^4 \equiv 1$, $2^4 \equiv 0$,
$3^4 \equiv 1$, ..., $8^4 \equiv 0$). Hence
$\sum_{i=0}^{17} (f i)^4 \pmod{16} \in \{0, 1, \dots, 18\}$, and 79
mod 16 = 15 requires either 15 odd $f i$ or 31 odd $f i$ (impossible
with $s = 18$). The mod-16 argument extracts this cleanly.

Concrete S3 plan:

```lean
/-- Fourth powers mod 16 are in {0, 1}. -/
lemma fourth_pow_mod_sixteen (x : ℕ) : x ^ 4 % 16 = 0 ∨ x ^ 4 % 16 = 1 := by
  have h : x % 16 < 16 := Nat.mod_lt x (by norm_num)
  have key : ∀ r : ℕ, r < 16 → r ^ 4 % 16 = 0 ∨ r ^ 4 % 16 = 1 := by
    intro r hr; interval_cases r <;> decide
  have : x ^ 4 % 16 = (x % 16) ^ 4 % 16 := by conv_lhs => rw [Nat.pow_mod]
  rw [this]; exact key (x % 16) h

theorem g4_lower : ¬ IsSumOfFourthPowers 18 79 := by
  rintro ⟨f, hsum⟩
  -- Each (f i)^4 mod 16 ∈ {0, 1}; sum of 18 such mod 16 ≤ 18 mod 16 = 2.
  -- But 79 mod 16 = 15.
  ...
```

**Expected size**: ~150 Lean lines (the mod-16 lower bound is the
analogue of the parent's mod-8 argument for squares, slightly more
involved because $k = 4$ has 16 residues to enumerate).

## Prior Next-Action Sketch

S1 next-action (executed in S2): `twenty_three_needs_nine_cubes`
via `decide` on $\text{Fin } 8 \to \text{Fin } 3$ — completed as
specified, with the cleaner "alternative" finite-search route from
the S1 plan.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE survey + S2 ACT lower bound)
- Current approach attempts: 1 (decide-search executed cleanly)
- Approaches tried: 1 (no alternative needed)

## Open files

- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — Lean
  deliverable for S2 (0 sorries, 0 axioms).
- `problem.md` — formal Lean signature targets, classification,
  Mathlib gap analysis, S2/S3/S4 decomposition.
- `knowledge.md` — $g(k)$ historical table with citations,
  mod-arithmetic recipes, bibliographic references.

## S2 Deliverable

This iteration delivers:
- 1 new definition (`IsSumOfCubes`)
- 1 new finite-search lemma (`representations23_empty`, `decide`)
- 1 new main theorem (`twenty_three_needs_nine_cubes`, 0 sorries, 0
  axioms)
- 1 concrete witness (`example : IsSumOfCubes 9 23`)
- 1 umbrella update (`proofs/Proofs.lean` adds the new module)

Build status: docker-verified (see
`.loom/logs/researcher-3-waring-g2-oq01-s2-build.log`).

## Future Iterations

| Iter | Target | Predicate | Approach | Status |
|---:|---|---|---|---|
| S2 | $g(3) \ge 9$ | $\neg \text{IsSumOfCubes } 8\ 23$ | `decide` $3^8$ | **DONE** |
| S3 | $g(4) \ge 19$ | $\neg \text{IsSumOfFourthPowers } 18\ 79$ | mod 16 | TODO |
| S4 | $g(3) \le 9$ | $\forall n, \text{IsSumOfCubes } 9\ n$ | Wieferich–Kempner (axiomatised) | TODO |
| S5 | $g(4) \le 19$ | $\forall n, \text{IsSumOfFourthPowers } 19\ n$ | BDD (axiomatised) | TODO |
| S6 | Hilbert–Waring existence | $\forall k \ge 1, \exists s, \forall n, …$ | Hardy–Littlewood (axiomatised) | TODO |
