# Knowledge Base: sqrt2-plus-sqrt3-irrational-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

- Target: prove f(x) = x⁴ - 10x² + 1 is the minimal polynomial of α = √2+√3 over ℚ
- Step 1: verify f(α) = 0 by direct computation (α² = 5+2√6, α⁴ = 49+20√6)
- Step 2: prove f is irreducible over ℚ (rational root theorem + no quadratic factor)
- Step 3: conclude [ℚ(√2+√3):ℚ] = 4

---

## Insights

- α² = 5 + 2√6 (from (√2+√3)² = 2 + 2√6 + 3)
- α⁴ = (5 + 2√6)² = 25 + 20√6 + 24 = 49 + 20√6
- f(α) = α⁴ - 10α² + 1 = (49 + 20√6) - 10(5 + 2√6) + 1 = 49 + 20√6 - 50 - 20√6 + 1 = 0 ✓
- Rational root theorem: rational roots of x⁴-10x²+1 would be ±1; f(1)=-8≠0, f(-1)=-8≠0
- For quadratic factorization: (x²+ax+b)(x²-ax+c) = x⁴ + (b+c-a²)x² + a(c-b)x + bc
  Matching: b+c-a²=-10, a(c-b)=0, bc=1, and x³ coeff = 0 (already satisfied)
  From a(c-b)=0: either a=0 or b=c
  Case a=0: b+c=-10, bc=1 → b,c are roots of t²+10t+1=0, giving t = (-10±√96)/2 ∉ ℚ
  Case b=c: 2b-a²=-10, b²=1 → b=±1
    b=1: 2-a²=-10 → a²=12, a∉ℚ
    b=-1: -2-a²=-10 → a²=8, a∉ℚ
  → f is irreducible over ℚ ✓

---

## Dead Ends

- None yet (problem is tractable with direct computation)
