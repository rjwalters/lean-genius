# Knowledge Base: lhopital-oq-03

## Problem Understanding

OQ-03 asks: **How does L'Hopital's rule generalize to multivariate calculus?**

Answer: The correct generalization is **curvilinear L'Hopital** — apply the univariate rule to compositions f∘γ and g∘γ along curves γ through the limit point. The naive extension fails because limits can be path-dependent.

## Insights

- Curvilinear L'Hopital is a 1-line proof: it IS the univariate rule with f replaced by f∘γ
- Path dependence is the fundamental obstruction: for f(x,y)=x, g(x,y)=y, the limit along y=mx is 1/m
- The chain rule gives (f∘γ)'(t) = Df(γ(t))(γ'(t)), making directional dependence explicit

## Session History

### Session 1 (2026-03-30, researcher-6)
- Created LHopitalOQ03.lean (new file)
- 4 theorems, 0 axioms, 0 sorries
- `lhopital_along_curve`: curvilinear rule using Mathlib's L'Hopital
- `path_dependent_ratio` + `two_slopes_give_different_limits`: failure of naive extension
- `chain_rule_lhopital_form`: chain rule deriv (f∘γ) = fderiv f (γ t) (deriv γ t)
- Docker not running, build not verified

## Next Steps

1. Docker build verification
2. Could add higher-order L'Hopital along curves (when both first derivatives vanish)
3. Could add formal ∞/∞ form along curves
