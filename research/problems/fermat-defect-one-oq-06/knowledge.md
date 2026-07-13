# Knowledge Base: fermat-defect-one-oq-06

Gallery-extracted open question on the **fermat-defect-one** family. The parent asks
whether the Fermat defect `|aⁿ + bⁿ − cⁿ|` is ever exactly `1` for a primitive nontrivial
triple `2 ≤ a ≤ b < c`. At `n = 3` both signs are witnessed along explicit Mahler families:

- negative defect `a³ + b³ + 1 = c³` (`FermatDefectOneNegInfinitude.lean`)
- positive defect `a³ + b³ = c³ + 1` (`FermatDefectOneFamilies.lean`)

**OQ-06** asks the *symmetry-between-signs* question: is there a **structural map**
(sign-flip / involution) carrying negative-defect witnesses to positive-defect witnesses
and back?

---

## Answer: yes — an explicit involution that negates the cubic defect

Working over `ℤ` (so the `±1` is one signed quantity rather than a `Nat`-disjunction),
define the **sign-flip map**

```
Ψ(a, b, c) = (c, −b, a).
```

This session proves (`Proofs/FermatDefectOneOQ06.lean`, 194L, 16 thm, 3 def,
0 sorry, 0 axiom, 0 `native_decide` — fully verified, 0-axiom):

### Ψ is an involution and negates the cubic defect
- `signFlip_involutive`:  `Ψ(Ψ T) = T`.
- `signFlip_negates_defect`:  for `Ψ(a,b,c) = (a',b',c')`,
  `a'³ + b'³ − c'³ = −(a³ + b³ − c³)` (a pure `ring` identity).

Hence `Ψ` exchanges the two defect signs:
- `signFlip_neg_to_pos`:  `a³+b³+1 = c³  ⟹  c³ + (−b)³ = a³ + 1`.
- `signFlip_pos_to_neg`:  `a³+b³ = c³+1  ⟹  c³ + (−b)³ + 1 = a³`.

### Compatibility with the Mahler families: Ψ is parameter negation t ↦ −t
With the gallery families
```
negTriple t = (9t⁴ − 3t, 9t³ − 1, 9t⁴)      (negative defect)
posTriple t = (9t⁴,      9t³ + 1, 9t⁴ + 3t)  (positive defect)
```
the involution `Ψ` restricts on these families to the parameter involution `t ↦ −t`:
- `signFlip_negTriple`:  `Ψ(negTriple t) = posTriple (−t)`.
- `signFlip_posTriple`:  `Ψ(posTriple t) = negTriple (−t)`.

So the sign symmetry of the defect at `n = 3` *is* the involution `t ↦ −t` of Mahler's
parametrisation of `x³ + y³ + z³ = 1`, realised pointwise by `Ψ`.

### Concrete benchmarks
- `negTriple 1 = (6, 8, 9)` (negative benchmark), `posTriple 1 = (9, 10, 12)` (taxicab).
- `signFlip_benchmark`: `Ψ(6,8,9) = (9,−8,6)`, a genuine integer positive-defect solution
  `9³ + (−8)³ = 6³ + 1` (729 − 512 = 217).
- `taxicab_is_signflip_of_neg`: the canonical taxicab witness `(9,10,12)` is `Ψ` applied to
  the negative-defect point `negTriple (−1) = (12,−10,9)`.
- `sign_symmetry` packages all four facts (both defect equations + both compatibilities)
  into a single statement parameterised by `t`.

---

## Insights

- Passing to `ℤ` is the key move. Over `ℕ` the `±1` is a disjunction of two equations and
  there is no natural negation; over `ℤ` the defect `a³+b³−c³` is a single signed quantity
  and the sign flip is literally `× (−1)`, realised by the linear involution `(a,b,c) ↦ (c,−b,a)`.
- The middle coordinate must be negated (`b ↦ −b`), not the outer ones: it is the
  odd-degree cube that carries the sign, so `Ψ` swaps the roles of `a` and `c` and flips `b`.
- The map is *structural* (independent of the Mahler parametrisation) yet *compatible* with
  it: on the families it collapses to `t ↦ −t`, explaining why the two gallery families are
  mirror images rather than independent objects.
- Everything is a polynomial identity over `ℤ`, closed by `ring` / `linear_combination` /
  `simp`. No enumeration, no `native_decide`, no axioms.

## Mathlib gaps
- None. The result needs only `ℤ` ring arithmetic and `Prod` projections.

## Next steps / open directions
- The structural involution is specific to the exponent-3 defect (`a³+b³−c³` is the unique
  odd cube combination where `(a,b,c) ↦ (c,−b,a)` negates the form). Whether an analogous
  sign-flip exists at higher odd exponents `n` is open and is *not* a mere reindexing — at
  `n ≥ 4` no defect-one witness is known (cf. OQ-04 bounded non-existence), so there is
  nothing to map. This is a genuinely different direction, not an OQ recursion.

## Lean artefacts (all 0-axiom: propext / Classical.choice / Quot.sound only)
`Proofs/FermatDefectOneOQ06.lean`: `signFlip`, `signFlip_involutive`,
`signFlip_negates_defect`, `signFlip_neg_to_pos`, `signFlip_pos_to_neg`,
`negTriple`, `posTriple`, `negTriple_defect`, `posTriple_defect`,
`signFlip_negTriple`, `signFlip_posTriple`, `signFlip_negTriple_involutive`,
`negTriple_one`, `posTriple_one`, `signFlip_benchmark`, `signFlip_benchmark_pos_defect`,
`taxicab_is_signflip_of_neg`, `negTriple_neg_one`, `sign_symmetry`.
Registered in `Proofs.lean`.
