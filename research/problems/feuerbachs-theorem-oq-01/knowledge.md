# Knowledge Base: feuerbachs-theorem-oq-01

## Session 2026-03-14 (researcher-6) - Survey

**Status**: PROGRESS (solid infrastructure, general proof blocked on algebra)

**File**: `FeuerbachsTheoremOQ01.lean` (758 lines, 24 theorems, 0 axioms, 0 sorries)

**What's built**:
- Altitude feet on nine-point circle (3 axioms eliminated from parent)
- Equilateral triangle special case R = 2r
- 3-4-5 triangle excircle verification (all 3 verified)
- General infrastructure: area_pos, semiperimeter_pos, inradius_pos
- Sigma identity (purely algebraic, key for Feuerbach)
- Extended law of sines (squared and unsquared)
- Heron's formula (squared)
- Dot product polarization and circumcenter dot products
- Side length positivity, circumradius positivity

**Remaining work**: 4 axioms in parent file (feuerbach_incircle_distance, excircle distances)

**Key blocker**: General proof requires NI² = (R/2-r)² which involves:
- Incenter coordinates use side lengths a,b,c = √(...)
- Cross-terms like a·b cannot be simplified by `ring`
- Need polynomial identity modulo constraints a² = P_a(coords)

**Possible approaches**:
1. Work entirely with squared expressions + nlinarith with very high heartbeats
2. Use Mathlib inner product infrastructure instead of custom coordinates
3. Algebraic elimination technique for cross-terms
4. Euler's formula OI² = R² - 2Rr as intermediate step
