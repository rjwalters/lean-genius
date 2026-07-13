# de-moivre-oq-02-oq-02-oq-01-oq-02: Chebyshev antisymmetric mixed product (U·T Wronskian)

**Target**: linearize the *mixed* product `U_m·T_n` purely into second-kind
polynomials. The obvious symmetric reading (`½(U_{m+n}+U_{m−n})`, equivalently
`2·T_m·U_n = U_{m+n}+U_{n−m}`) is already proved in the sibling
`DeMoivreOQ02OQ02.T_mul_U_product` — so a plain U·T product-to-sum would be a
duplicate. The genuinely new content is the **antisymmetric** combination.

## Result (VERIFIED, 0-axiom, Tier-A)

For every `CommRing R` and all `m, n : ℤ`, in `R[X]`:

  **U_m · T_n − U_n · T_m = X · U_{m−n−1}.**   (`U_mul_T_antisymm`)

Division-free — no factor of 2 anywhere — so it holds in every characteristic
(unlike the symmetric product-to-sum formulas). Machine-checked:
`docker-build.sh Proofs.DeMoivreOQ02OQ02OQ01OQ02` → 7744 jobs, clean; axioms are
only `propext / Classical.choice / Quot.sound`.

Supporting new identities in the same file:
- `U_wronskian`: `U_{m−1}·U_n − U_m·U_{n−1} = U_{m−n−1}` — the second-kind
  Chebyshev **Wronskian / d'Ocagne / Casoratian** identity (not in Mathlib).
- `U_mul_T_sub`: `U_{m−1}·T_n − T_m·U_{n−1} = U_{m−n−1}` — mixed subtraction
  formula (polynomial `sin(mθ)cos(nθ) − cos(mθ)sin(nθ) = sin((m−n)θ)`).
- `T_eq_U_sub_X_U`: `T_k = U_k − X·U_{k−1}` — division-free first-from-second.

## Key idea (why it is division-free, and non-inductive)

Symmetric product-to-sum formulas *average* two angle-addition formulas, so a
factor 2 is baked in. The antisymmetric combination *subtracts* them and the 2
cancels. Concretely, writing `T_k = U_k − X·U_{k−1}` (integer coefficients!):

  U_m T_n − U_n T_m = U_m(U_n − X U_{n−1}) − U_n(U_m − X U_{m−1})
                    = X·(U_{m−1} U_n − U_m U_{n−1})   [the U·U terms cancel]
                    = X·U_{m−n−1}.                    [Wronskian]

The Wronskian itself is proved **without induction** by evaluating the second-kind
addition formula `U_{a+b} = U_a T_b + T_{a+1} U_{b−1}`
(`ChebyshevPolynomialsOQ01OQ01.U_add`, already verified in the gallery) at
`(a,b) = (m−1, −n)` and reflecting via `T_{−n}=T_n` (`T_neg`) and
`U_{−n−1}=−U_{n−1}` (`U_neg_sub_one`). Every lemma closes by `linear_combination`.

Numeric cross-checks (over ℤ): (m,n)=(2,1): U_2 T_1 − U_1 T_2 = (4x²−1)x − 2x(2x²−1)
= x = X·U_0 ✓. (m,n)=(2,0): U_2 − U_0·T_2 = (4x²−1)−(2x²−1) = 2x² = X·U_1 ✓.

## Sessions

### Session 2026-07-04 (Session 1) — FRESH, ORIENT→ACT→VERIFY

**Mode**: FRESH  **Outcome**: SHIPPED (verified, 0-axiom)

#### What I Did
- Claimed the EMPTY problem (tractability 7). Confirmed via the sibling
  `DeMoivreOQ02OQ02.T_mul_U_product` that the *symmetric* U·T linearization already
  exists — so I targeted the antisymmetric closed form instead (a real gallery gap).
- Derived `U_m T_n − U_n T_m = X·U_{m−n−1}` and verified it by hand-trig and small
  numeric cases before formalizing.
- Found the division-free route through `T_k = U_k − X·U_{k−1}` and the second-kind
  Wronskian, letting the whole file be `linear_combination` on top of the already-
  proven `U_add` (no fresh induction).
- Wrote `proofs/Proofs/DeMoivreOQ02OQ02OQ01OQ02.lean` (lemmas `T_eq_U_sub_X_U`,
  `U_mul_T_sub`, `U_wronskian`; theorem `U_mul_T_antisymm`; two ℤ examples).
- Built green: `docker-build.sh Proofs.DeMoivreOQ02OQ02OQ01OQ02` → 7744 jobs.
- Created gallery data (`meta.json`, `annotations.json`) as `verified/original`.

#### Key Findings
- The antisymmetric mixed product carries **no factor of 2** — genuinely stronger
  (characteristic-free) than the sibling's symmetric `2·T·U`.
- The second-kind **Wronskian** `U_{m−1}U_n − U_m U_{n−1} = U_{m−n−1}` is the engine;
  it is a clean reusable identity absent from Mathlib.
- Evaluating an addition formula at a **negative argument** + reflection replaces a
  fresh two-step ℤ induction entirely.

#### Files Modified
- `proofs/Proofs/DeMoivreOQ02OQ02OQ01OQ02.lean` (new, 115 lines)
- `src/data/proofs/de-moivre-oq-02-oq-02-oq-01-oq-02/{meta,annotations}.json` (new)

#### Next Steps / Open Directions
- Antisymmetric first-kind analogue `T_m U_{n−1} − T_n U_{m−1}`: does it also give a
  single-term closed form, and how does it relate to this Wronskian?
- Christoffel–Darboux summation `∑_k U_k(x)U_k(y)` for the second-kind family.
- Dickson-polynomial / associated-Chebyshev generalization of the division-free
  antisymmetric identity.
