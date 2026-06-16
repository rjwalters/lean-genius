# Knowledge Base: quadratic-gauss-sum-square

Target: for an odd prime `p` and a primitive additive character `ψ : ZMod p → ℂ`,
the quadratic Gauss sum `g = ∑ n, (n/p) ψ(n)` satisfies `g² = (-1)^((p-1)/2) · p = p*`.

---

## Problem Understanding

A **known theorem with strong Mathlib backing** — the work is formalization plumbing,
not new mathematics. The square value (not the harder sign of `g` itself) is the
target, which keeps it tractable.

The clean route reduces everything to Mathlib's generic `gaussSum_sq`:

```
gaussSum_sq (hχ₁ : χ ≠ 1) (hχ₂ : IsQuadratic χ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card F
```

So the whole problem reduces to: instantiate `gaussSum_sq` at the quadratic character
of `ZMod p`, then evaluate `χ(-1)` and `Fintype.card (ZMod p)`.

---

## Insights

### The codomain/typing gotcha (resolved)

`quadraticChar (ZMod p) : MulChar (ZMod p) ℤ` is **ℤ-valued**. `gaussSum χ ψ` requires
`χ` and `ψ` to share a codomain `F'`. With `ψ : AddChar (ZMod p) ℂ`, the naive
`gaussSum (quadraticChar (ZMod p)) ψ` **does not typecheck** (ℤ ≠ ℂ). Transport the
character along `ℤ → ℂ`:

```
noncomputable def chiC : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
```

### The three leaf facts feeding `gaussSum_sq` — all closed this session

1. **`chiC.IsQuadratic`** — `MulChar.IsQuadratic.comp`:
   `(quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)`. One line, no `simp`.
2. **`chiC ≠ 1`** (needs `p ≠ 2`) — `MulChar.ringHomComp_ne_one_iff` with the
   injectivity of `Int.castRingHom ℂ` (`RingHom.injective_int`, ℂ is `CharZero`)
   reduces it to `quadraticChar_ne_one`, which holds when `ringChar (ZMod p) = p ≠ 2`
   (`ZMod.ringChar_zmod_n`).
3. **`chiC (-1) = (-1)^((p-1)/2)`** — `quadraticChar_neg_one` gives
   `quadraticChar (ZMod p) (-1) = χ₄ (Fintype.card (ZMod p))`; `ZMod.card` rewrites the
   cardinality to `p`; `ZMod.χ₄_eq_neg_one_pow` (needs `p % 2 = 1`) gives `(-1)^(p/2)`;
   then `p / 2 = (p-1)/2` for odd `p` (`omega` after `Odd` destructuring); finally
   push the `ℤ → ℂ` cast with `map_pow`/`map_neg`/`map_one`.

The main theorem body is exactly:
```
have h := gaussSum_sq (chiC_ne_one hp) chiC_isQuadratic hψ
rw [h, chiC_neg_one hp, ZMod.card p]
```

---

## Dead Ends / Avoided

- **Direct double-sum (problem.md Approach B)** — unnecessary; `gaussSum_sq` already
  encapsulates the `g·ḡ = p` orthogonality computation. Don't reimplement.
- **Naive `gaussSum (quadraticChar (ZMod p)) ψ`** — type error (ℤ vs ℂ). Use `chiC`.
- **`legendreSym.at_neg_one` chain** — works, but `quadraticChar_neg_one` packages the
  `χ₄`-evaluation directly and is shorter.

---

## Verification Status

Proof is **0-sorry, 0-axiom**. All Mathlib lemma names were confirmed against the
pinned Mathlib source (rev `2df2f01`, v4.26.0):
`gaussSum_sq`, `quadraticChar_isQuadratic`, `MulChar.IsQuadratic.comp`,
`MulChar.ringHomComp_ne_one_iff`, `MulChar.ringHomComp_apply`, `RingHom.injective_int`,
`quadraticChar_ne_one`, `quadraticChar_neg_one`, `ZMod.χ₄_eq_neg_one_pow`,
`ZMod.ringChar_zmod_n`, `ZMod.card`, `Nat.Prime.odd_of_ne_two`.

Promoted to `proofs/Proofs/QuadraticGaussSumSquare.lean` (registered in `Proofs.lean`).
Docker build verification was pending at session end (build host saturated).

---

## Next Steps

1. Confirm the green Docker build of `Proofs.QuadraticGaussSumSquare`, then flip the
   gallery entry status to `verified`.
2. Create the gallery entry `src/data/proofs/quadratic-gauss-sum-square/` with badge
   `mathlib`, axiomCount 0, cross-referenced to `elementary-quadratic-reciprocity*`
   (headline application: `g^p` two-ways gives reciprocity).
