# herons-formula-oq-07 — Weitzenböck's Inequality

## Session 2026-07-01 (researcher-7): Weitzenböck's inequality a²+b²+c² ≥ 4√3·Area [VERIFIED, SOLVED]

**Mode**: ACT (fresh EMPTY problem). **Outcome**: SOLVED — new file
`proofs/Proofs/HeronsFormulaOQ07.lean` (188 L, 3 defs / 6 theorems), plus gallery entry
`src/data/proofs/herons-formula-oq-07/` (meta.json + annotations.json). **Docker build
VERIFIED** (`docker-build.sh Proofs.HeronsFormulaOQ07`, `✔ [3058/3058]`); **0-sorry,
0-axiom**, no native_decide.

### What was delivered (namespace `WeitzenbockHeronOQ07`)
- defs `semiperimeter`, `heronProduct` (= Area²), `area` (self-contained, mirrors OQ06 style).
- `heronProduct_nonneg` — Heron product ≥ 0 for a nondegenerate triangle.
- **`sq_sum_sub_heron`** (SOS identity, the core) : `(a²+b²+c²)² − 48·heronProduct =
  2((a²−b²)²+(b²−c²)²+(c²−a²)²)`, closed by `unfold; ring`.
- **`weitzenbock_sq`** : `48·heronProduct ≤ (a²+b²+c²)²` — holds for ALL reals (no triangle
  hypothesis), via `nlinarith` on the three `sq_nonneg` + the identity.
- `weitzenbock_sq_eq_iff` : squared equality ⇔ a²=b² ∧ b²=c².
- **`weitzenbock`** (headline) : `4·√3·area ≤ a²+b²+c²` for a nondegenerate triangle.
- **`weitzenbock_eq_iff`** : equality ⇔ a=b ∧ b=c (equilateral).

### Recipe / gotchas
- Squaring trick: both sides ≥0, so `4√3·Area ≤ X ⇔ (4√3·Area)² ≤ X²`. Compute
  `(4·√3·A)² = 16·(√3)²·A² = 48·heronProduct` using `Real.sq_sqrt` for (√3)²=3 and A²=hp.
  Upgrade squared→linear with `Real.sqrt_le_sqrt` then `Real.sqrt_sq` (both sides ≥0).
- SOS identity verified numerically first (3-4-5: 2500−1728=772=2·386 ✓; equilateral: 0 ✓).
- (4√3)² = 48 is the magic constant. `48·hp = 3·(a+b+c)(−a+b+c)(a−b+c)(a+b−c)`.
- Equality: a²=b², a,b>0 ⇒ a=b via factoring (a−b)(a+b)=0 with a+b>0.

### Follow-up directions (for Seeker, depth-1 → allowed)
- Finsler–Hadwiger: a²+b²+c² ≥ 4√3·Area + (a−b)²+(b−c)²+(c−a)² — same SOS technique, sharper.
