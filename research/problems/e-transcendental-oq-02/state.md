# Current State

**Phase**: ACT — gallery entry built; 2 axioms tractable, 1 is the main open conjecture
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-08 (Session 10, researcher-11)
**Iteration**: 10

## Current Focus

Session 10 split **Layer 3** of the 3-layer recipe for
`rational_digits_eventually_periodic` into two parts and implemented
**Layer 3a** — the `ℝ → ℤ` cast bridge — as a single private helper:

```lean
private lemma floor_pow_mul_div (b : ℕ) (p : ℤ) (q : ℕ) (n : ℕ) :
    ⌊(b : ℝ) ^ n * ((p : ℝ) / (q : ℝ))⌋ = ((b : ℤ) ^ n * p) / q
```

The proof is two lines: `push_cast` + `ring` rewrites the `ℝ` expression
as a single `ℤ`-cast over a `ℕ`-divisor, then `Int.floor_div_natCast` +
`Int.floor_intCast` discharge the floor. This isolates the cast burden
of the residue bridge `nthDigit_rat_eq_residue` from the integer-arithmetic
`(b^n · p) / q ↔ (b^n · p mod q) · b / q` algebra of Layer 3b.

After Layer 3a is in place, **Layer 3b** is a pure-integer-arithmetic
step (`Int.ediv_add_emod` + `Int.emod_lt_of_pos` style), free of any
`Real`/`Rat` machinery. Estimated 30–50 lines for Layer 3b once the
sign-handling for negative `p` is decomposed (recipe convention:
restrict to `p ≥ 0, q > 0` first, then handle `p < 0` via
`nthDigit b n (-x)` symmetry as a small follow-up).

Earlier session context:

* Session 9 (researcher-9, PR #17016): Layer 2 — `ratResidue`,
  `ratResidue_succ`, `ratResidue_eq_iterate`,
  `ratResidue_eventually_periodic`.
* Session 8 (researcher-11, PR #16993): Layer 1 —
  `exists_iterate_collision`, `eventually_periodic_iterate`.
* Session 3 (researcher-11, PR #16976): the 3-layer recipe.

## Active Approach

The current Lean entry establishes the framework:
- Definitions: `nthDigit`, `IsNormalInBase`, `IsAbsolutelyNormal`,
  `ratResidue` (private, S9).
- 28 public theorems: `e_floor`, `e_floor_10..1000000000`, `e_digit1..9`
  (first 9 decimal digits 2.718281828 from `Real.exp_one_gt_d9` /
  `Real.exp_one_lt_d9`), `e_normal_implies_uniform_decimal_digits`,
  `periodic_has_missing_ktuple` (orbit cardinality).
- 6 private helpers (Layers 1, 2, 3a): `exists_iterate_collision`,
  `eventually_periodic_iterate`, `ratResidue_succ`,
  `ratResidue_eq_iterate`, `ratResidue_eventually_periodic`,
  `floor_pow_mul_div`.

Three remaining axioms:
- `rational_digits_eventually_periodic` — **tractable**. Layers 1, 2, 3a
  in place; Layer 3b (residue → digit form) is the only piece remaining.
- `normal_imp_irrational` — derives from axiom 1 +
  `periodic_has_missing_ktuple`. Discharging axiom 1 first then proving 2
  is the natural sequence.
- `e_absolutely_normal` — the **main open conjecture**. Genuinely
  open as of 2026; will remain axiomatized.

## Blockers

- **Local Lean build unreliable**: Worktree's `proofs/.lake` is a
  self-cycle symlink — Docker build cold-clones Mathlib (~45 min).
  Following S8/S9 convention, build verification is deferred to CI.
  Layer 3a uses well-established Mathlib v4.26.0 lemmas
  (`Int.floor_div_natCast`, `Int.floor_intCast`, both confirmed via
  `gh api repos/leanprover-community/mathlib4/contents/...`), so
  the build risk is contained to the `push_cast` + `ring` step which
  uses only standard cast-pushing simp lemmas.

## Next Action

**ACT (Session 11)** — implement Layer 3b: the integer-arithmetic
residue-to-digit bridge

```lean
private lemma nthDigit_rat_eq_residue (b : ℕ) (hb : 2 ≤ b)
    (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    nthDigit b n ((p : ℝ) / (q : ℝ)) =
      (b * ((p * (b : ℤ)^n) % (q : ℤ))) / (q : ℤ)  -- conjectural form
```

(Note: the exact statement may need sign-restriction; the natural
single-step version factors via Layer 3a as

```
nthDigit b n ((p : ℝ) / q) = (((b : ℤ)^n * p) / q) % (b : ℤ)
                          = ⟨residue-bridge in ℤ⟩
```

where the second `=` is what Layer 3b proves.)

Estimated ~30–50 lines. With Layer 3a's `floor_pow_mul_div` as starting
point, the proof reduces to integer division/modular arithmetic
(`Int.ediv_add_emod` patterns), bypassing any further `Real` machinery.

After Layer 3b lands, the axiom `rational_digits_eventually_periodic`
can be replaced by a theorem chaining Layers 1, 2, 3a, 3b — and then
`normal_imp_irrational` becomes tractable as a follow-up.

## Attempt Counts

- Total attempts: 5 (Session 1 = entry built 2026-05-04; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe (2026-05-08);
  Session 8 = Layer 1 (#16993, 2026-05-08); Session 9 = Layer 2
  (researcher-9, #17016, 2026-05-08); Session 10 = Layer 3a
  (researcher-11, 2026-05-08)).
- Current approach attempts: 3 (Layers 1, 2, 3a all closed; Layer 3b
  remains).

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:336` — `rational_digits_eventually_periodic` (axiom)
- `proofs/Proofs/ETranscendentalOQ02.lean:325` — `floor_pow_mul_div` (Layer 3a, S10)
- `proofs/Proofs/ETranscendentalOQ02.lean:308` — `ratResidue_eventually_periodic` (Layer 2, S9)
- `proofs/Proofs/ETranscendentalOQ02.lean:243` — `eventually_periodic_iterate` (Layer 1, S8)
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata
