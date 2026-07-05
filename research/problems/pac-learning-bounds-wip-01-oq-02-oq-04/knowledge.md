# Knowledge Base: pac-learning-bounds-wip-01-oq-02-oq-04

Covering-number bounds via pseudo-dimension / fat-shattering dimension.

Target (Anthony–Bartlett *Neural Network Learning*, Thm 12.2; Pollard 1984; ABCH 1997):
for `F ⊆ [0,1]^X` with pseudo-dimension `Pdim(F) = d`,
```
N(γ, F, L∞(x_{1:m}))  ≤  Σ_{k=0}^{d} C(m,k) (2/γ)^k  =  O((m/γ)^d).
```

---

## Problem Understanding

The parent `pac-learning-bounds-wip-01-oq-02` (files `PACLearningBoundsWIP01*.lean`) supplies a
**fully verified, 0-axiom Boolean VC / Sauer–Shelah stack** over an *arbitrary* ground type `α`:

| Verified lemma (namespace `PACLearningBoundsWIP01`) | Statement |
|---|---|
| `trace H S` / `Shatters H S` / `VCDim H` | trace `{h ∩ S : h∈H}`, shattering, VC dimension |
| `vcDim_eq` | parent `VCDim H = Finset.vcDim H` (bridge to Mathlib) |
| `card_le_sum_choose_vcDim` | `[Fintype α]`: `|H| ≤ Σ_{k≤VCDim H} C(|α|,k)` |
| **`trace_card_le_sum_choose`** | **`|Π_H(S)| ≤ Σ_{i≤VCDim H} C(|S|,i)`, no `Fintype α`** |
| `trace_card_le_sum_range_choose` | same in `Σ_{i∈range(d+1)}` form for any `d ≥ VCDim H` |
| `vcDim_mono`, `vcDim_powerset_le`, … | monotonicity toolkit |

`trace_card_le_sum_choose` is the exact Boolean growth-function bound and is the *transport target*.

---

## Insights (this session — ORIENT, 2026-07-04)

### I1. The Boolean case of oq-04 is **already fully solved** by verified gallery infra — not open.

For a `{0,1}`-valued class `F` and any scale `γ ∈ (0,1]`, two Boolean functions are within `L∞`
distance `< 1` iff identical, so a `γ`-cover of `F|_{x_{1:m}}` has size exactly the growth function
`|Π_F(m)|`, and pseudo-dimension collapses to VC dimension (`Pdim = VCdim` for `{0,1}`-valued
classes). Hence the oq-04 LHS **equals** `|Π_F(S)|` with `|S|=m`, and since `2/γ ≥ 2 > 1`,
```
N(γ,F,L∞) = |Π_F(S)| ≤ Σ_{k≤d} C(m,k)          (parent `trace_card_le_sum_choose`)
                     ≤ Σ_{k≤d} C(m,k)(2/γ)^k    (each B^k ≥ 1).
```
So the oq-04 statement is genuinely new **only** for real/integer-valued classes with `b ≥ 2`
quantization levels. This sharpens the scoping in `problem.md`.

### I2. Approach A (hypograph → Boolean VC) is correct and reaches `O((m/γ)^d)`, but **not** the sharp constant.

Discretize `F ⊆ [0,1]^X` at scale `γ` to `F_b ⊆ {0,…,b}^X`, `b = ⌈2/γ⌉` (a `γ`-cover count is
≤ the number of distinct quantizations `|F_b|_{x_{1:m}}|`). For `g ∈ F_b` define the **hypograph set**
```
B_g = { (x,t) ∈ X×{1,…,b} : g(x) ≥ t }.
```
Then `g ↦ B_g` is injective (`g(x) = |{t : (x,t)∈B_g}|`), so `|F_b| = |{B_g}|` over ground
set `X×{1,…,b}`.

**VCdim of the hypograph class = pseudo-dimension.** A pseudo-shattered set `{x_1,…,x_k}` with
witness thresholds `t_1,…,t_k` corresponds *exactly* to the VC-shattered set
`{(x_1,t_1),…,(x_k,t_k)}` of `{B_g}` — and no VC-shattered set of `{B_g}` can contain two points
`(x,t),(x,t')` in the same column (`t<t'`): realizing "in-`t`, out-`t'`" needs `g(x)≥t' ∧ g(x)<t`,
impossible. Hence `VCdim({B_g}) = Pdim(F_b) ≤ Pdim(F) = d` (quantization is monotone
post-composition, which never increases pseudo-dimension).

Applying the **verified parent Boolean Sauer–Shelah** to `{B_g}` restricted to the `m·b` sample
points `[m]×{1,…,b}`:
```
N(γ,F,L∞) ≤ |F_b|_{x_{1:m}}| = |Π_{ {B_g} }([m]×{1..b})|
          ≤ Σ_{k≤d} C(mb, k)          (parent `trace_card_le_sum_choose`, ground size mb)
          = O((mb)^d) = O((m/γ)^d).    ✓ matches the problem's second equality
```
Leading term: `Σ_{k≤d} C(mb,k) ∼ (mb)^d/d!` and the sharp `Σ_{k≤d} C(m,k)(2/γ)^k ∼ (2m/γ)^d/d!`
agree to leading order, so **Approach A delivers the operationally-central `O((m/γ)^d)` claim in
full**. It does *not* deliver the exact middle expression `Σ C(m,k)(2/γ)^k` — that needs the
refined Natarajan/Haussler column-aware shifting (see Gaps).

### I3. `problem.md`'s "Key Lemma 1: `Pdim(F) = VCdim(subgraph class)`" is right, but the bound it
then yields via Boolean SS is `Σ C(mb,k)`, **not** the sharp `Σ C(m,k)(2/γ)^k`. Recording this so a
future session does not over-promise the constant from Approach A alone.

---

## Mathlib / infrastructure gaps

| Item | Status | Size estimate | Verdict |
|---|---|---|---|
| Boolean Sauer–Shelah growth bound | **have it** (verified parent) | — | reuse |
| Integer-valued class `F_b : X → Fin (b+1)`; hypograph map `B_g`; injectivity | build | ~40–60 lines | BUILD |
| Pseudo-shattering / `Pdim`; `VCdim(hypograph) = Pdim` (both directions) | build | ~80–120 lines | BUILD |
| `L∞` `γ`-covering number of a finite function class; quantization `q_γ`; `#covers ≤ #quantizations` | build | ~50–80 lines | BUILD (elementary, no measure theory) |
| **Route A total** (asymptotic `O((m/γ)^d)`) | build on verified infra | **~150–260 lines** | **BUILDABLE** |
| Sharp constant `Σ C(m,k)(2/γ)^k` (Natarajan/ABCH refined shifting) | genuine gap | ~400–600 lines new multivalued shifting | defer |
| Fat-shattering dimension route (ABCH 1997) | genuine gap | open-ended (scale-sensitive) | defer |

No Mathlib primitive exists for pseudo-/fat-shattering dimension or function-space covering
numbers; but Route A needs *none* of the heavy analysis — the hypograph reduction turns everything
into `Finset` combinatorics already covered by the verified parent stack.

---

## Lean formalization plan (Route A — execute when build/Aristotle are back)

New file `proofs/Proofs/PACLearningBoundsWIP01OQ02OQ04.lean`, `import
Proofs.PACLearningBoundsWIP01SauerShelah`, `namespace PACLearningBoundsWIP01`:

1. `def hypograph (g : X → Fin (b+1)) : Finset (X × Fin b)` (or a `Finset (Finset (X×Fin b))`
   family `hypoFam F_b`). Prove `Function.Injective hypograph` via value-recovery.
2. `def PdimShatters` / `def Pdim` for integer classes; prove
   `vcDim (hypoFam F_b) = Pdim F_b` (⊇ from pseudo-shatter, ⊆ from the same-column obstruction).
3. Chain: `hypoFam` restricted to `[m]×Fin b` has `VCDim ≤ d`, feed to
   `trace_card_le_sum_range_choose` ⇒ `|F_b|_{x_{1:m}}| ≤ Σ_{k∈range(d+1)} C(mb,k)`.
4. Covering layer: `def covNum (γ) (F) (xs)`; quantization `q γ`; lemma
   `covNum γ F xs ≤ (F.image (q γ ∘ ·|xs)).card`; combine ⇒
   `covNum γ F xs ≤ Σ_{k∈range(d+1)} C(mb,k) = O((m/γ)^d)`.
5. Arithmetic glue only (Nat): `C(m,k) ≤ C(m,k)*B^k` for `B≥1` — for the Boolean corollary I1.

**Do NOT** attempt to hit the sharp `(2/γ)^k` constant in this file; state Route A's `Σ C(mb,k)`
form and the `O((m/γ)^d)` corollary, and leave the sharp constant as a documented follow-up.

---

## Session note — dual-tool blackout (2026-07-04)

This ORIENT was produced with **no local verification available**: `docker run` fails
(containerd blob EIO; `docker-build.sh` unusable) and the Aristotle MCP returns `Resource not
found` (404). No new `proofs/Proofs/*.lean` was committed — the lakefile globs `Proofs.*`, so an
unverifiable file could break the gallery build. All Lean above is a *plan*, not verified code.
Next session with a working build should execute Route A (steps 1–4); it is BUILDABLE (~150–260
lines) entirely on the verified parent Sauer–Shelah stack.

---

## Dead Ends

- **Thermometer/hypograph + Boolean SS does NOT give the sharp `Σ C(m,k)(2/γ)^k`** — it gives
  `Σ C(mb,k)` (same leading order, looser constant). The sharp constant is a separate,
  column-aware multivalued shifting argument (Natarajan/Haussler), not a black-box reduction.

---

## Next Steps

1. (build back) Execute Route A steps 1–4 → verified `O((m/γ)^d)` covering bound + Boolean
   corollary I1. Target: 0 sorries, 0 axioms, reusing `trace_card_le_sum_range_choose`.
2. Only after 1: attempt the sharp `(2/γ)^k` constant via multivalued shifting (large, optional).
3. Fat-shattering route (ABCH) is a separate follow-up problem, not this one.
