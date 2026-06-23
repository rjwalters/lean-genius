# S4a ACT — Tight Sylvester Upper Bound (researcher-1, 2026-05-31)

## Summary

Refines S3c's loose `frobeniusNumber3 a b c ≤ (a - 1) * (b - 1)` to the tight
`≤ (a - 1) * (b - 1) - 1`, matching the classical 2-generator Sylvester
identity `g(a, b) = a*b - a - b = (a - 1)*(b - 1) - 1` for coprime `a, b ≥ 1`.

Build verified: `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`
→ `✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (28s)`,
`Build completed successfully (3059 jobs)`, `=== Build succeeded ===`.

## Delta

- `proofs/Proofs/FrobeniusNumberOQ03.lean`: 225 → 253 LOC (+28 LOC).
- New theorem: `frobeniusNumber3_le_sylvester_bound_tight`.
- 16 theorems / 2 definitions / 0 sorries / 0 axioms (was 15 / 2 / 0 / 0).
- No new imports (uses existing `csSup_le`, `csSup_empty`, `bot_le`,
  `Set.not_nonempty_iff_eq_empty` from S3a's import stack).
- `src/data/proofs/frobenius-number-oq-03/meta.json`: lineCount 226 → 253,
  theoremCount 15 → 16, description and assumptions updated to mention S4a,
  new section entry `s4a-tight-sylvester-upper-bound`.

## Proof Strategy

Same backbone as S3c (contrapositive of S3b's `large_representable3_via_two_gen`
bridge applied via `frobeniusNumber3_le_of_subset_Iio`-style argument), but
inlined to avoid the loose `≤ K` packaging and directly produce `≤ K - 1`:

```lean
theorem frobeniusNumber3_le_sylvester_bound_tight {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1 := by
  unfold frobeniusNumber3
  by_cases hne : ({ n : ℕ | ¬ Representable3 a b c n }).Nonempty
  · refine csSup_le hne ?_
    intro n hn
    by_contra hge
    push_neg at hge
    have hlt : (a - 1) * (b - 1) ≤ n := by omega
    exact hn (large_representable3_via_two_gen hab ha hb hlt)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty]
    exact bot_le
```

The `omega` step handles the ℕ-subtraction case-split uniformly:

- If `(a - 1) * (b - 1) ≥ 1`: from `hge : (a - 1) * (b - 1) - 1 < n`,
  we get `(a - 1) * (b - 1) ≤ n` directly (standard `K - 1 < n → K ≤ n`
  for `K ≥ 1` in ℕ).
- If `(a - 1) * (b - 1) = 0` (degenerate `a = 1 ∨ b = 1`): `0 - 1 = 0` in
  ℕ, so `hge : 0 < n`, giving `0 = (a - 1) * (b - 1) ≤ n` trivially.

The `csSup_empty` branch handles the case where the non-representable set is
empty (e.g., `a = 1`: every `n` is representable as `n * 1 + 0 * b + 0 * c`),
where `csSup ∅ = ⊥ = 0` in ℕ and `bot_le` closes `0 ≤ (a-1)*(b-1) - 1`.

## Comparison with S3c (Loose Form)

| Form | Bound | Tightness vs Sylvester `g(a,b) = ab - a - b` |
|------|-------|----------------------------------------------|
| S3c (loose) | `≤ (a - 1) * (b - 1)` | one higher than tight (slack = 1) |
| S4a (tight) | `≤ (a - 1) * (b - 1) - 1` | exact for 2-gen specialisation (c = 0 collapse) |

The tight form equals `ab - a - b` exactly (algebraic identity
`(a-1)(b-1) - 1 = ab - a - b + 1 - 1 = ab - a - b`), so it matches the
classical Sylvester-Frobenius theorem. For the 3-generator setting it remains
a valid upper bound (the third generator `c` can only shrink, never enlarge,
the non-representable set), with the Roberts d=1 closed-form
`g(n, n+1, n+2) = ⌊(n-2)/2⌋·n + (n-1)` being asymptotically half this bound
(strict for `n ≥ 4`).

## Conflict-Freedom with S5

The S5 ACT primary next-action (per state.md before this PR) is
`large_representable3` for three-consecutive `(n, n+1, n+2)` toward the
Roberts d=1 closed form. S4a adds a single new theorem at the end of the
`FrobeniusOQ03` namespace below S4's `set_non_representable3_finite_of_coprime_ab`,
touching no existing API. S5 (when shipped) will add further theorems below
this; merge order is irrelevant.

## Bearer Inventory

No new bearers beyond what S3a/S3b/S3c/S4 already established:

- Mathlib: `csSup_le`, `csSup_empty`, `bot_le`, `Set.not_nonempty_iff_eq_empty`
  (all from `Mathlib.Data.Nat.Lattice` / `Mathlib.Tactic` transitive imports).
- Local: `Representable3`, `frobeniusNumber3`, `large_representable3_via_two_gen`
  (S3b at line 163).
- Parent: none used directly (S3b's bridge already encapsulates the parent
  `FrobeniusNumber.large_representable` quotation).

## Forward Outlook

S5 ACT remains the primary next-action: `large_representable3` for
three-consecutive `(n, n+1, n+2)` (Route A direct numerical bound ~80 LOC,
Route B Apéry-set ~150 LOC). S4a discharges the optional / parallel-sibling
S4a item from the state.md roadmap, leaving S5 / S6 / S6+ as the remaining
work toward the slug's Roberts target.

## Non-Actions (Explicit)

1. **No state.md rewrite of the S5 primary next-action.** The S5 picker's
   design pass should remain authoritative; S4a is a sibling addition, not
   a redirection.
2. **No JSON tracker rewrite of `progressSummary` history.** Append-only
   discipline preserved (one new bullet, prior content verbatim).
3. **No `pnpm annotations:build` rerun.** Annotations are unchanged
   (gallery section structure preserved through S4 unchanged; only the new
   S4a section entry was added to `meta.json` directly per gallery convention).
4. **No `Proofs.lean` umbrella refresh.** `import Proofs.FrobeniusNumberOQ03`
   already in place since S2 (PR #18937).
5. **No `relatedProofs` cross-reference changes.** Slug's cross-reference
   graph is unchanged; S4a is internal API tightening.
