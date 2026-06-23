# Literature for laws-of-large-numbers-oq-02

## Primary sources

- Chebyshev, P.L. (1867). *Des valeurs moyennes.* Journal de mathématiques pures et appliquées (2) **12**, 177–184. — Quantitative WLLN at rate O(1/n).
- Lindeberg, J.W. (1922). *Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung.* Mathematische Zeitschrift **15**, 211–225. — Lindeberg's proof of CLT.
- Berry, A.C. (1941). *The accuracy of the Gaussian approximation to the sum of independent variates.* Trans. AMS **49**, 122–136. — One half of Berry–Esseen.
- Esseen, C.-G. (1942). *On the Liapunoff limit of error in the theory of probability.* Arkiv för matematik, astronomi och fysik **A28**, 1–19. — Other half.
- Stein, C. (1972). *A bound for the error in the normal approximation to the distribution of a sum of dependent random variables.* Proc. Sixth Berkeley Symp., Vol. 2, 583–602. — Stein's method (modern Berry–Esseen alternative).

## Mathlib references (pinned SHA `2df2f01...`)

- `Mathlib.Probability.StrongLaw` — SLLN for i.i.d. integrable random variables.
- `Mathlib.Probability.Moments.Variance` — `IndepFun.variance_sum`, `variance_smul`,
  `variance_const_mul`. **Load-bearing for discharging `variance_sampleMean`** — see
  `../s1-observe-variance-sampleMean-bearer-audit.md`.
- `Mathlib.Probability.Distributions.Gaussian.{Basic,Real,Fernique}` — Gaussian measure.
- `Mathlib.MeasureTheory.Measure.CharacteristicFunction` — characteristic functions of
  measures.
- `Mathlib.Probability.Independence.CharacteristicFunction` — `IndepFun ↔ χ factors`.
- `Mathlib.Probability.Inequality.Chebyshev` (via `Mathlib.Probability.Moments.Basic`) —
  Chebyshev's inequality, already used by `chebyshev_convergence_rate`.

## Notes

- A formalization of the CLT would likely follow Lindeberg's swap argument, which
  matches Mathlib's expected style (it's elementary and avoids characteristic-function
  inversion).
- A Berry–Esseen formalization is research-level (no analogous Mathlib formalization
  exists for any quantitative CLT).
