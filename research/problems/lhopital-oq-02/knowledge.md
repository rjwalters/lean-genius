# Knowledge Base: lhopital-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Mathlib has 26 L'Hopital variants but ALL are 0/0 form. The infinity/infinity form is a genuine gap.
Only g -> infinity is needed (not both f and g), making this more general than the naive 1/f, 1/g reduction.

---

## Proof Strategy (SUCCESSFUL)

### Reduction to c = 0
Define h(x) = f(x) - c*g(x). Then:
- h'(x) = f'(x) - c*g'(x), so h'(x)/g'(x) = f'(x)/g'(x) - c -> 0
- h(x)/g(x) = f(x)/g(x) - c
- If h/g -> 0 then f/g = h/g + c -> c

### The c = 0 Case (Core Argument)
Given: f'/g' -> 0 and g -> +infinity as x -> a+

1. Fix epsilon > 0. Get delta_1 where |f'/g'| < epsilon/2.
2. Choose x_0 in (a, a + delta_1) with g(x_0) > 0.
3. Set M = max(g(x_0)+1, 2|f(x_0)|/epsilon + 1). Get delta_2 where g(x) >= M.
4. For x with a < x < x_0 and g(x) >= M:
   - By Cauchy MVT on [x, x_0]: exists xi with (f(x)-f(x_0))/(g(x)-g(x_0)) = f'(xi)/g'(xi)
   - Algebraic identity: f(x)/g(x) = R * (1 - g(x_0)/g(x)) + f(x_0)/g(x)
   - |R| < epsilon/2, |1-g(x_0)/g(x)| <= 1, |f(x_0)/g(x)| < epsilon/2
   - Total: |f(x)/g(x)| < epsilon

### Key Insight: No Rolle's Argument Needed
g(x) >= M > g(x_0) gives g(x) != g(x_0) directly.

---

## Dead Ends

- Reducing infinity/infinity to 0/0 via substitution: only works when BOTH f and g -> infinity.

---

## Remaining Work

Three variant reductions (standard substitutions, good Aristotle candidates):
1. `lhopital_infty_left`: via u = a + b - x
2. `lhopital_infty_atTop`: via u = 1/x
3. `lhopital_infty_atBot`: via u = -x
