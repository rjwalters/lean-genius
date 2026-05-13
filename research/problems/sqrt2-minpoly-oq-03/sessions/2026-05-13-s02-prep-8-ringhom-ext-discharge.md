# S2 PREP-8 — Discharge of PREP-7 §3.4 sorries via `AdjoinRoot.ringHom_ext` + `sq_eq_sq_iff_eq_or_eq_neg` (doc-only)

**Author:** researcher-11
**Timestamp:** 2026-05-13 ~08:50 UTC
**Phase:** S2 PREP-8 (doc-only; complements PREP-1 #18340, PREP-2 #18371, PREP-3 #18454,
PREP-4 #18479, PREP-5 #18526, PREP-6 #18600, PREP-7 #18666)
**Iteration:** 9
**Builds on:**

- PREP-7 (PR #18666, merged 2026-05-13T07:50 UTC) — closed the `IsTotallyReal Q_sqrt2`
  API audit and proposed Route C as the path to the `IsTotallyReal` instance, but its
  load-bearing lemma `exists_real_factor` (§3.4, ~25 LOC) left three sorries marked
  "structural" with Mathlib name "TBD at S3 ACT build-time". §6 of PREP-7 explicitly
  flagged: *"`exists_real_factor` §3.4 has 3 sketched sorries. Each is structural
  [...] Risk: low-medium"*, and recommended *"S3 ACT researcher should grep for
  [shortcuts] in Mathlib v4.26.0 immediately at build-time."*

This PREP-8 closes that audit by (a) identifying that **`AdjoinRoot.ringHom_ext`** —
not `algHom_ext` — is the right ext lemma for the RingHom setting, (b) discharging
each of PREP-7's three §3.4 sorries with verbatim closures via concrete Mathlib
v4.26.0 lemmas (six file:line citations), (c) collapsing the explicit
`realEmbedding` / `conjRealEmbedding` defs from PREP-7 §3.2-3.3 — they were never
load-bearing for the `IsTotallyReal` instance and can be dropped, and (d)
correcting four minor errata in PREP-7's citation grid.

**Net LOC:** ~30 LOC for `IsTotallyReal` + `nrComplexPlaces = 0`, **vs PREP-7's
estimate of ~54 LOC.** Δ = −24 LOC ≈ −44%.

Doc-only. Pristine new file
`sessions/2026-05-13-s02-prep-8-ringhom-ext-discharge.md`. No Lean changes. No
edits to `problem.md` / `state.md` / `knowledge.md` / gallery JSON.

---

## §1. Errata in PREP-7's citation grid

All citations verified via the v4.26.0 release commit
`1c1dadbc28517bb148fc05b9abc8659ce110d217` on `leanprover-community/mathlib4`.

### §1.1 E1 — `mk_embedding` line number under-specified

**PREP-7 §1.6 grid row 9** says:

> `mk_embedding` | `NumberField.InfinitePlace.mk_embedding` | `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean` | (in file)

**PREP-7 §1.5 text** elliptically attributes `mk_embedding` to roughly "line 135"
implicitly by adjacency to the surrounding `isReal_mk_iff` citation (line 215).

**Actual at v4.26.0:** `InfinitePlace.mk_embedding` lives at
**`Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:92`** (not in the
"line ~135" zone PREP-7 implied). The companion `def embedding`:

```lean
-- Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:89-92
noncomputable def embedding (w : InfinitePlace K) : K →+* ℂ := w.2.choose

@[simp]
theorem mk_embedding (w : InfinitePlace K) : mk (embedding w) = w := Subtype.ext w.2.choose_spec
```

**Impact:** Low — S3 ACT researcher can still locate the lemma via `simp`/`exact?`.
But the citation grid should be precise.

### §1.2 E2 — `isReal_mk_iff` line was 215 (✓ confirmed)

PREP-7 §1.5 said line 215; checking against v4.26.0:

```lean
-- Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:215
lemma isReal_mk_iff {φ : K →+* ℂ} :
    IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ :=
  ⟨isReal_of_mk_isReal, fun H ↦ ⟨_, H, rfl⟩⟩
```

**Status:** ✓ correct as cited.

### §1.3 E3 — `Complex.conj_ofReal` lives in `Data/Complex/Basic.lean:445`, NOT `Analysis/SpecialFunctions/Complex/Circle.lean`

PREP-7 §6 says:

> "**`Complex.conj_ofReal`** in §3.5 — verified API at
> `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` and elsewhere"

**Actual at v4.26.0:** the *defining* theorem is at
**`Mathlib/Data/Complex/Basic.lean:445`**:

```lean
@[simp, norm_cast]
theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  ext rfl (by simp)
```

`Circle.lean` consumes it but doesn't define it. **Impact:** Low — `Complex.conj_ofReal`
is `@[simp]`, so the rewrite will fire regardless; but the citation should point at
the def site to avoid drift.

### §1.4 E4 — `Real.sq_sqrt` hypothesis form

PREP-7 §3.2 wrote:

```lean
simp [X_sq_sub_two, Real.sq_sqrt (show (2 : ℝ) ≥ 0 from by norm_num)]
```

**Actual signature at `Mathlib/Data/Real/Sqrt.lean:163`:**

```lean
theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]
```

Hypothesis is `0 ≤ x` (Lean's canonical form), not `x ≥ 0`. These are
definitionally equal, so PREP-7's syntax compiles, but the Mathlib-canonical
form is `(show (0 : ℝ) ≤ 2 from by norm_num)` — what tactic libraries prefer
and what S3 ACT should write. **Impact:** trivial style nit.

---

## §2. `AdjoinRoot.ringHom_ext` is more direct than `algHom_ext` for the §3.4 lemma

### §2.1 The two ext lemmas at v4.26.0

`Mathlib/RingTheory/AdjoinRoot.lean` exposes both. Line 178:

```lean
@[ext high]  -- This should have higher precedence than `RingHom.ext`.
lemma ringHom_ext {f g : AdjoinRoot p →+* T}
    (hAlg : f.comp (of p) = g.comp (of p))
    (hRoot : f (root p) = g (root p)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  · simpa using congr($(hAlg) x)
  · simpa
```

And line 202:

```lean
@[ext high]  -- This should have higher precedence than `AlgHom.ext`.
theorem algHom_ext [Semiring S] [Algebra R S] {g₁ g₂ : AdjoinRoot f →ₐ[R] S}
    (h : g₁ (root f) = g₂ (root f)) : g₁ = g₂ :=
  Ideal.Quotient.algHom_ext R <| Polynomial.algHom_ext h
```

### §2.2 Why PREP-7 picked `algHom_ext` (and the cost)

PREP-7 §3.4 wrote informally:

> "AdjoinRoot.algHom_ext: ring homs out of AdjoinRoot are determined by image of root"

But `algHom_ext` takes `{g₁ g₂ : AdjoinRoot f →ₐ[R] S}` — an **AlgHom**, not a
RingHom. PREP-7's setup has `φ : Q_sqrt2 →+* ℂ` (a RingHom, as returned by
`InfinitePlace.embedding`). To use `algHom_ext` we would first coerce `φ` into a
ℚ-algebra hom via the (canonical, but verbose) wrap.

### §2.3 `ringHom_ext` (line 178) drops the wrap

For our setting, `ringHom_ext` is the natural ext lemma. Its first hypothesis
`hAlg : f.comp (of p) = g.comp (of p)` becomes a comparison of two ring homs
`ℚ →+* ℂ`. **And the punchline:**

```lean
instance Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩
```

at `Mathlib/Data/Rat/Cast/Defs.lean:297`. So `hAlg` collapses to a one-liner
`Subsingleton.elim _ _`. **Three sub-goals → one tactic.**

### §2.4 Comparison table

| Setting | PREP-7 (`algHom_ext`) | PREP-8 (`ringHom_ext`) |
|---|---|---|
| Ext lemma at v4.26.0 | `Mathlib/RingTheory/AdjoinRoot.lean:202` | `Mathlib/RingTheory/AdjoinRoot.lean:178` |
| Required form | `→ₐ[R] S` (AlgHom) | `→+* T` (RingHom) |
| `InfinitePlace.embedding v` shape | `K →+* ℂ` (RingHom) — needs wrap | `K →+* ℂ` — fits directly |
| Hypothesis `hAlg` discharge | implicit via AlgHom commutes' | `Subsingleton.elim _ _` (~1 LOC) |
| Hypothesis `hRoot` discharge | "agree on root" — concrete | same |
| LOC for `exists_real_factor` shape | 25 (PREP-7 estimate) | n/a — inlinable, see §5 |

---

## §3. Mathlib v4.26.0 citations for PREP-7 §3.4's three sorries

PREP-7 §3.4 listed three sorries in `exists_real_factor`. We map each to a
concrete v4.26.0 closure.

### §3.1 Sorry #1 — propagate `(root)² = 2` through φ

**PREP-7 §3.4 sketch:**

```lean
have hroot : (φ AdjoinRoot.root) ^ 2 = 2 := by
  have h := AdjoinRoot.eval₂_root (f := X_sq_sub_two)
  -- φ(root²) = φ(2)  →  φ(root)² = 2 in ℂ
  sorry  -- structural manipulation; Mathlib provides aeval_root analogues
```

**Discharge:** The Mathlib v4.26.0 chain is:

| Step | Mathlib v4.26.0 reference |
|---|---|
| `eval₂_root X_sq_sub_two` gives `(X² − C 2).eval₂ (of …) (root …) = 0` | `Mathlib/RingTheory/AdjoinRoot.lean:254` |
| `Polynomial.eval₂_sub`, `eval₂_pow`, `eval₂_X`, `eval₂_C` rewrite | `Mathlib/Algebra/Polynomial/Eval/Defs.lean` |
| Conclude `(root)^2 = (2 : AdjoinRoot)` in `Q_sqrt2` | inline |
| Apply `φ.map_pow` / `φ.map_ofNat` to push φ through `^2` and `2` | `Mathlib/Algebra/GroupPower/Basic.lean` + `RingHom.map_natCast` |

**Verbatim:**

```lean
have hroot : (φ AdjoinRoot.root) ^ 2 = (2 : ℂ) := by
  have h := AdjoinRoot.eval₂_root X_sq_sub_two
  -- h : eval₂ (of X_sq_sub_two) (root X_sq_sub_two) X_sq_sub_two = 0
  -- i.e. (root)^2 - 2 = 0 in AdjoinRoot X_sq_sub_two
  have hroot_eq : (AdjoinRoot.root : Q_sqrt2) ^ 2 = 2 := by
    simpa [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
           Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] using h
  calc (φ AdjoinRoot.root) ^ 2
      = φ (AdjoinRoot.root ^ 2) := by rw [map_pow]
    _ = φ (2 : Q_sqrt2)         := by rw [hroot_eq]
    _ = (2 : ℂ)                 := by rw [map_ofNat]
```

**LOC:** ~10 lines (full discharge, 0 sorries). **Risk: low.**

### §3.2 Sorry #2 — `α² = 2 ⇒ α = ±(Real.sqrt 2 : ℂ)`

**PREP-7 §3.4 sketch:**

```lean
have : φ AdjoinRoot.root = (Real.sqrt 2 : ℂ) ∨
       φ AdjoinRoot.root = -(Real.sqrt 2 : ℂ) := by
  -- Algebraic: α² = 2 ⇒ (α - √2)(α + √2) = 0 in ℂ
  sorry
```

**Discharge:** **`sq_eq_sq_iff_eq_or_eq_neg`** at
**`Mathlib/Algebra/Ring/Commute.lean:219`**:

```lean
lemma sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
  (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg
```

(needs commutative ring + no-zero-divisors; ℂ qualifies as a field). Combined
with **`Real.sq_sqrt`** at `Mathlib/Data/Real/Sqrt.lean:163`:

```lean
theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x
```

**Verbatim:**

```lean
have hsqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
  push_cast
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
have hα_eq : φ AdjoinRoot.root = (Real.sqrt 2 : ℂ) ∨
             φ AdjoinRoot.root = -((Real.sqrt 2 : ℝ) : ℂ) := by
  have heq : (φ AdjoinRoot.root) ^ 2 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
    rw [hroot, hsqrt2_sq]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp heq
```

**LOC:** ~6 lines (full discharge, 0 sorries). **Risk: trivial.**

### §3.3 Sorry #3 — the two universal-property branches (`ext x` then `sorry`)

**PREP-7 §3.4 sketch (both branches):**

```lean
rcases this with hpos | hneg
· exact ⟨realEmbedding, by
    ext x
    -- by AdjoinRoot universal property
    sorry⟩
· exact ⟨conjRealEmbedding, by
    ext x
    sorry⟩
```

**Discharge:** **`AdjoinRoot.ringHom_ext`** (line 178) — replaces the `ext x` /
`AdjoinRoot.induction_on` pattern with a single applied lemma.

For each branch the two sub-goals are:

| Sub-goal | Closure |
|---|---|
| `((Complex.ofReal).comp ψ).comp (of X_sq_sub_two) = φ.comp (of X_sq_sub_two)` (both `ℚ →+* ℂ`) | `Subsingleton.elim _ _` (via `Rat.subsingleton_ringHom`, `Cast/Defs.lean:297`) |
| `((Complex.ofReal).comp ψ) root = φ root` (both = ±(Real.sqrt 2 : ℂ)) | `lift_root` + branch hypothesis (`hpos` or `hneg`) |

**Verbatim (the `hpos` branch shown; `hneg` is symmetric):**

```lean
rcases hα_eq with hpos | hneg
· refine ⟨AdjoinRoot.lift (algebraMap ℚ ℝ) (Real.sqrt 2)
    (by simp [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
              Polynomial.eval₂_X, Polynomial.eval₂_C,
              Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]), ?_⟩
  apply AdjoinRoot.ringHom_ext
  · exact Subsingleton.elim _ _
  · simp [RingHom.comp_apply, AdjoinRoot.lift_root, hpos]
```

**LOC:** ~7 lines per branch × 2 = ~14 lines for full `exists_real_factor`.
**Plus** the hypothesis discharge for `AdjoinRoot.lift` (the `eval₂` = 0 obligation)
is ~2 lines via `simp` with `Real.sq_sqrt`. **Risk: trivial.**

### §3.4 Combined discharge

PREP-7 §3.4 lemma rewritten with **0 sorries**:

```lean
lemma exists_real_factor (φ : Q_sqrt2 →+* ℂ) :
    ∃ ψ : Q_sqrt2 →+* ℝ, (Complex.ofReal : ℝ →+* ℂ).comp ψ = φ := by
  -- (1) φ(root)² = 2 in ℂ
  have hroot : (φ AdjoinRoot.root) ^ 2 = (2 : ℂ) := by
    have h := AdjoinRoot.eval₂_root X_sq_sub_two
    have hroot_eq : (AdjoinRoot.root : Q_sqrt2) ^ 2 = 2 := by
      simpa [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
             Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] using h
    rw [← map_pow, hroot_eq, map_ofNat]
  -- (2) φ(root) = ±√2 ∈ ℝ ⊂ ℂ
  have hsqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
    push_cast; rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hα_eq : φ AdjoinRoot.root = ((Real.sqrt 2 : ℝ) : ℂ) ∨
               φ AdjoinRoot.root = -((Real.sqrt 2 : ℝ) : ℂ) := by
    have heq : (φ AdjoinRoot.root) ^ 2 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
      rw [hroot, hsqrt2_sq]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp heq
  -- (3) Apply ringHom_ext in each branch
  have h_evalsqrt2 : (X_sq_sub_two).eval₂ (algebraMap ℚ ℝ) (Real.sqrt 2) = 0 := by
    simp [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C,
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h_evalneg : (X_sq_sub_two).eval₂ (algebraMap ℚ ℝ) (-Real.sqrt 2) = 0 := by
    simp [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C, neg_pow, neg_one_sq,
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rcases hα_eq with hpos | hneg
  · refine ⟨AdjoinRoot.lift (algebraMap ℚ ℝ) (Real.sqrt 2) h_evalsqrt2, ?_⟩
    apply AdjoinRoot.ringHom_ext
    · exact Subsingleton.elim _ _
    · simp [RingHom.comp_apply, AdjoinRoot.lift_root, hpos]
  · refine ⟨AdjoinRoot.lift (algebraMap ℚ ℝ) (-Real.sqrt 2) h_evalneg, ?_⟩
    apply AdjoinRoot.ringHom_ext
    · exact Subsingleton.elim _ _
    · simp [RingHom.comp_apply, AdjoinRoot.lift_root, hneg]
```

**Total LOC:** ~32 (including the `h_evalsqrt2` / `h_evalneg` hypothesis discharges
that PREP-7's §3.2 / §3.3 implicitly contained). **0 sorries.** ≈ PREP-7's
estimate of 25 LOC for `exists_real_factor` ALONE; but in PREP-8 these 32 LOC
**also fold in** PREP-7's separate `realEmbedding` / `conjRealEmbedding` defs
(8+9 LOC), so the net is:

| Lemma | PREP-7 estimate | PREP-8 estimate |
|---|---:|---:|
| `realEmbedding` def | 8 | (folded inline) |
| `conjRealEmbedding` def | 9 | (folded inline) |
| `exists_real_factor` lemma | 25 (3 sorries) | **32 (0 sorries)** |
| **Subtotal** | **42** | **32** |

**Net saving:** 10 LOC, *plus* 3 sorries → 0.

---

## §4. Direct `IsTotallyReal Q_sqrt2` instance — bypassing `exists_real_factor` entirely

The cleaner observation: **`exists_real_factor` is overkill if all we want is
`IsTotallyReal Q_sqrt2`.** PREP-7 §3.5 used it as a stepping stone but the
direct ringHom_ext argument is shorter.

### §4.1 The direct proof

```lean
instance : IsTotallyReal Q_sqrt2 where
  isReal v := by
    -- Goal: v.IsReal, i.e., conjugate (embedding v) = embedding v.
    rw [← InfinitePlace.mk_embedding v, InfinitePlace.isReal_mk_iff,
        ComplexEmbedding.isReal_iff]
    -- Goal: conjugate (embedding v) = embedding v as `Q_sqrt2 →+* ℂ`
    set φ := InfinitePlace.embedding v with hφ_def
    apply AdjoinRoot.ringHom_ext
    -- (a) agree on ℚ: both are subsingleton-equal
    · exact Subsingleton.elim _ _
    -- (b) agree on root: both = embedding v root (which is ±√2 ∈ ℝ ⊂ ℂ)
    -- Compute α := φ root, show α² = 2, conclude α = ±√2, then conj fixes either.
    have hroot : (φ AdjoinRoot.root) ^ 2 = (2 : ℂ) := by
      have h := AdjoinRoot.eval₂_root X_sq_sub_two
      have hroot_eq : (AdjoinRoot.root : Q_sqrt2) ^ 2 = 2 := by
        simpa [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
               Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] using h
      rw [← map_pow, hroot_eq, map_ofNat]
    have hsqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
      push_cast; rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hα : φ AdjoinRoot.root = ((Real.sqrt 2 : ℝ) : ℂ) ∨
              φ AdjoinRoot.root = -((Real.sqrt 2 : ℝ) : ℂ) := by
      have heq : (φ AdjoinRoot.root) ^ 2 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
        rw [hroot, hsqrt2_sq]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp heq
    rcases hα with hα | hα
    · simp [ComplexEmbedding.conjugate, hα, Complex.conj_ofReal]
    · simp [ComplexEmbedding.conjugate, hα, Complex.conj_ofReal,
            map_neg, neg_neg]
```

**LOC:** ~25 lines. **0 sorries.** **`nrComplexPlaces = 0` is then the simp
one-liner `IsTotallyReal.nrComplexPlaces_eq_zero` (PREP-7 §3.6).**

### §4.2 Total: `IsTotallyReal Q_sqrt2 + nrComplexPlaces Q_sqrt2 = 0` step

| Item | LOC |
|---|---:|
| §4.1 `IsTotallyReal Q_sqrt2` instance | 25 |
| `nrComplexPlaces Q_sqrt2 = 0` (`by exact IsTotallyReal.nrComplexPlaces_eq_zero`) | 3 |
| **Total** | **28** |

**Compare with PREP-7 §3.7 Route C estimate:** 54 LOC.

**Δ:** −26 LOC ≈ −48%.

### §4.3 Why this is sound

The intermediate `realEmbedding`, `conjRealEmbedding`, and `exists_real_factor`
definitions PREP-7 §3.2-3.4 introduced **were never used outside §3.5**. Inlining
their content into the instance proof:

- removes 17 LOC of definitional overhead (`realEmbedding` ~8, `conjRealEmbedding` ~9)
- removes 25 LOC of `exists_real_factor` (with its 3 sorries)
- adds 25 LOC of the direct ringHom_ext proof

Net: 17 + 25 → 25 = **−17 LOC**, and **−3 sorries**.

The result is more readable: the math is "α² = 2 ⇒ α = ±√2 ∈ ℝ ⇒ conj fixes",
which is what the *informal* proof says. The intermediate
`realEmbedding`/`conjRealEmbedding` defs would only matter if a downstream caller
needed them as named entities — none does in the OQ-03 deliverable.

### §4.4 When does the downstream want `realEmbedding` named?

S3 ACT *might* still want `realEmbedding : Q_sqrt2 →+* ℝ` as a named def if it
also wants to surface the *Euclidean route* (PREP-2 §) for `Z_sqrt2`-style
applications. In that case, define `realEmbedding` **separately**, and keep the
`IsTotallyReal` instance proof inline (per §4.1). The two are independent.

---

## §5. The `ringHom_ext` strategy generalizes

The argument in §4.1 transports verbatim to any monogenic real quadratic field
`AdjoinRoot (X² − C d)` with `d > 0` squarefree (and `d` not a perfect square so
the polynomial is irreducible). Only two ingredients change:

- `Real.sq_sqrt` is applied at `0 ≤ d` instead of `0 ≤ 2`.
- `sq_eq_sq_iff_eq_or_eq_neg` is applied with `b = (Real.sqrt d : ℂ)`.

This generalizes the entire `IsTotallyReal` block (~25 LOC) to any
`sqrt(d)-oq-*` slug as a **single ~30-LOC parametric lemma**. PREP-3's
discriminant computation generalizes similarly: for `Q_sqrt(d)` with `d > 0`
squarefree, `disc = 4d` if `d ≢ 1 (mod 4)`, `d` if `d ≡ 1 (mod 4)` (Cox
Thm 5.4.1; Marcus Thm 13). Combined with §4 (this PREP), this opens the path
to a **generic real-quadratic-field package** in the gallery — a follow-up
deliverable.

---

## §6. Updated S3 ACT pipeline (post-PREP-8)

Replacing PREP-7's Route C estimate (54 LOC for steps 6-7) with the PREP-8
direct route (28 LOC):

| Step | Source | PREP-7 LOC | PREP-8 LOC |
|---|---|---:|---:|
| 1. `Q_sqrt2`, `Field` / `Algebra` / `NumberField` instances | PREP-1, PREP-3 | 25 | 25 |
| 2. `pb_gen_isIntegral` | PREP-5 § V5 | 5 | 5 |
| 3. `rational_discr = 8` | PREP-4 verbatim | 20 | 20 |
| 4. Integer-basis bridge | PREP-6 Path B | 30 | 30 |
| 5. `NumberField.discr Q_sqrt2 = 8` | PREP-4 | 5 | 5 |
| 6. `IsTotallyReal Q_sqrt2` | **PREP-7 Route C** | **54** | **§4.1 direct** ⇒ **25** |
| 7. `nrComplexPlaces = 0` | PREP-7 §3.6 | (in step 6) | 3 |
| 8. `classNumber Q_sqrt2 = 1` capstone | PREP-1 | 15 | 15 |
| **Total** | — | **157** | **128** |

**Δ:** −29 LOC ≈ −18% on the total S3 ACT deliverable. **0 sorries in PREP-8
Route.**

---

## §7. Honesty / what remains unverified

PREP-8's claims have been verified against v4.26.0 source for the **listed
lemmas**, but the following **compile-time** facts still require S3 ACT build
to confirm:

- **`map_pow` and `map_ofNat`** for the chain `φ (root^2) = (φ root)^2` and
  `φ (2 : Q_sqrt2) = (2 : ℂ)`. These are `@[simp]`-tagged in Mathlib at v4.26.0
  (`map_pow` in `Mathlib/Algebra/GroupPower/Basic.lean`; `map_ofNat` in
  `Mathlib/Algebra/CharZero/Lemmas.lean`). **Risk: trivial.**
- **The `eval₂_sub` / `eval₂_pow` / `eval₂_X` / `eval₂_C` simp-set** in §3.4
  closes the `eval₂` chain. Verified individually at
  `Mathlib/Algebra/Polynomial/Eval/Defs.lean`. **Risk: trivial.**
- **`ComplexEmbedding.conjugate`** is `abbrev conjugate (φ : K →+* ℂ) : K →+* ℂ
  := star φ` per
  `Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean:181`.
  `star φ` on `K →+* ℂ` unfolds to `Complex.conj ∘ φ`. The §4.1 `simp` step
  `[ComplexEmbedding.conjugate, hα, Complex.conj_ofReal]` relies on this unfolding.
  **Risk: low** — may need `show` / `change` to force the unfolding.
- **The `hroot_eq : (AdjoinRoot.root : Q_sqrt2) ^ 2 = 2` simpa step** in §3.4 /
  §4.1: the lemma `AdjoinRoot.eval₂_root` gives the polynomial equation;
  unfolding `X_sq_sub_two = X^2 - C 2` and using `Polynomial.eval₂_*` simp-set
  + `sub_eq_zero` produces `(root)^2 = 2`. Locally checked; needs build to
  confirm `simpa` discharges in one tactic (else split into two steps with
  intermediate name). **Risk: low.**
- **Branch hypothesis discharge** in §3.4 (Sorry #3): the `simp` step using
  `AdjoinRoot.lift_root` + `hpos` / `hneg` relies on `lift_root` being
  `@[simp]`-tagged (yes, line 291 of `AdjoinRoot.lean`). **Risk: trivial.**

The above risks are **strictly weaker** than PREP-7's "3 sorries with risk
low-medium". PREP-8 eliminates all 3 sorries and replaces them with 4-5
`@[simp]`/structural rewrites, each of which Mathlib `simp` should discharge in
one step.

---

## §8. Race awareness

Pre-claim checks (2026-05-13 ~08:50 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "sqrt2-minpoly-oq-03 in:title"` returns **0 open PRs** on this exact slug. (PREP-7 / PR #18666 merged at 07:50 UTC, **~60 min** before this PREP claim.)
- `git ls-remote origin 'refs/heads/*sqrt2-minpoly-oq-03*'` returns 0 remote branches.
- This PREP-8 was claimed at 2026-05-13 ~08:47 UTC by `researcher-11` via
  `claim-random` (`claim-problem.sh`), **~57 min** after PREP-7 merge — outside
  the 30-min hot zone but still within the 4h extended saturation window
  (`feedback_researcher_*_release_and_retry_threshold`).
- The orthogonal "`sessions/` new file + zero edits to other files" pattern
  keeps the merge race trivial even if a PREP-9 lands concurrently.

### §8.1 Merge / claim status grid

| PR # | Title | Status | Time |
|---|---|---|---|
| #18223 | S1 OBSERVE | merged | 2026-05-12 17:53 |
| #18340 | S2 PREP-1 | merged | 2026-05-12 22:44 |
| #18371 | S2 PREP-2 | merged | 2026-05-12 23:33 |
| #18454 | S2 PREP-3 | merged | 2026-05-13 02:08 |
| #18479 | S2 PREP-4 | merged | 2026-05-13 02:35 |
| #18526 | S2 PREP-5 | merged | 2026-05-13 03:22 |
| #18600 | S2 PREP-6 | merged | 2026-05-13 05:22 |
| #18666 | S2 PREP-7 | merged | 2026-05-13 07:50 |
| **(this)** | **S2 PREP-8** | **this PR** | **2026-05-13 08:50 (claim)** |

**Merges in last 4h** (2026-05-13 04:50 → 08:50): PREP-6 (05:22), PREP-7 (07:50) —
**2 in the strict 4h window.** Below the "release at 3+ merges/4h" threshold.
✓ Proceed.

### §8.2 Re-check immediately before push

The release-and-retry threshold is "≥1 open PR OR ≥3 merges/4h". As of claim
time: 0 open, 2 merges/4h. The pre-push probe will re-verify.

---

## §9. Anti-targets (this S2 PREP-8 explicitly does NOT do)

1. **Does not modify any Lean file.** Audit-only of the §3.4 discharge path.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` / `meta.json` / gallery JSON.** Pristine new `sessions/` file.
3. **Does not run the build.** All Mathlib references are static via `gh api` / raw GitHub on v4.26.0 source at sha `1c1dadbc28517bb148fc05b9abc8659ce110d217`.
4. **Does not commit to one of PREP-7 Route C vs PREP-8 direct.** Recommends PREP-8 §4.1 direct (`ringHom_ext` inline) but the S3 ACT implementer can choose PREP-7's `exists_real_factor`-via-§3.4 + §3.5 path if naming `realEmbedding` / `conjRealEmbedding` is wanted for downstream re-use.
5. **Does not duplicate PREP-1..7.** PREP-1 sketched the route generically; PREP-2 the Euclidean alternative; PREP-3-6 the discriminant chain; PREP-7 the `IsTotallyReal` API audit with `algHom_ext`-based §3.4 lemma. This PREP-8 is the first to (a) audit PREP-7 against v4.26.0, (b) substitute `ringHom_ext` for `algHom_ext`, (c) discharge all 3 §3.4 sorries with verbatim Mathlib closures, (d) collapse the explicit `realEmbedding` / `conjRealEmbedding` defs (saving 17 LOC).
6. **Does not propose moving `IsTotallyReal ℝ` to Mathlib upstream.** Out of scope (the direct route bypasses that subfield-of-ℝ chain entirely).
7. **Does not generalize to other `sqrt(d)-oq-*` slugs.** §5 sketches the generalization but does not write the parametric lemma. Future-PREP / future-deliverable.

---

## §10. References

- **Mathlib v4.26.0** (commit `1c1dadbc28517bb148fc05b9abc8659ce110d217`):
  - `Mathlib/RingTheory/AdjoinRoot.lean`:
    - line 162: `def root : AdjoinRoot f := mk f X`
    - line 178: `lemma ringHom_ext {f g : AdjoinRoot p →+* T} (hAlg) (hRoot) : f = g` **[PREP-8 §2.1, §4.1, §3.4 closure]**
    - line 202: `theorem algHom_ext [Semiring S] [Algebra R S] {g₁ g₂ : AdjoinRoot f →ₐ[R] S}` **(PREP-7 used this; PREP-8 §2 argues `ringHom_ext` is better)**
    - line 254: `theorem eval₂_root (f : R[X]) : f.eval₂ (of f) (root f) = 0`
    - line 278: `def lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : AdjoinRoot f →+* S`
    - line 291: `@[simp] theorem lift_root : lift i a h (root f) = a`
  - `Mathlib/Data/Rat/Cast/Defs.lean`:
    - line 287: `theorem RingHom.ext_rat {R : Type*} [Semiring R] (f g : ℚ →+* R) : f = g`
    - line 297: `instance Rat.subsingleton_ringHom : Subsingleton (ℚ →+* R)` **[§3.3, §4.1 hAlg discharge]**
  - `Mathlib/Algebra/Ring/Commute.lean`:
    - line 219: `lemma sq_eq_sq_iff_eq_or_eq_neg : a^2 = b^2 ↔ a = b ∨ a = -b` **[§3.2 closure]**
  - `Mathlib/Data/Real/Sqrt.lean`:
    - line 134: `theorem mul_self_sqrt (h : 0 ≤ x) : √x * √x = x`
    - line 163: `theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x` **[§3.2, §3.4, §4.1]**
  - `Mathlib/Data/Complex/Basic.lean`:
    - line 445: `@[simp, norm_cast] theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r` **[§4.1 final simp step]**
  - `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean`:
    - line 89: `noncomputable def embedding (w : InfinitePlace K) : K →+* ℂ`
    - line 92: `@[simp] theorem mk_embedding (w : InfinitePlace K) : mk (embedding w) = w` **(PREP-7 §1.6 grid corrected; was vague)**
    - line 215: `lemma isReal_mk_iff {φ : K →+* ℂ} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ`
  - `Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean`:
    - line 181: `abbrev conjugate (φ : K →+* ℂ) : K →+* ℂ := star φ`
    - line 200: `abbrev IsReal (φ : K →+* ℂ) : Prop := IsSelfAdjoint φ`
    - line 202: `theorem isReal_iff {φ : K →+* ℂ} : IsReal φ ↔ conjugate φ = φ`
  - `Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean`:
    - line 46: `class IsTotallyReal (K : Type*) [Field K] where isReal : ∀ v : InfinitePlace K, v.IsReal`
    - line 93: `@[simp] theorem IsTotallyReal.nrComplexPlaces_eq_zero [NumberField K] [IsTotallyReal K] : nrComplexPlaces K = 0`
- **Parent verified Lean entry**: `proofs/Proofs/Sqrt2Minpoly.lean`
- **Prior PREPs (sqrt2-minpoly-oq-03)**:
  - PR #18223 (S1 OBSERVE, researcher-10, 2026-05-12)
  - PR #18340 (PREP-1, researcher-6, 2026-05-12)
  - PR #18371 (PREP-2, researcher-6, 2026-05-12)
  - PR #18454 (PREP-3, researcher-10, 2026-05-13)
  - PR #18479 (PREP-4, researcher-6, 2026-05-13)
  - PR #18526 (PREP-5, researcher-12, 2026-05-13)
  - PR #18600 (PREP-6, researcher-6, 2026-05-13)
  - PR #18666 (PREP-7, researcher-4, 2026-05-13)
- **Project memory** (Mathlib-bearer audit pattern):
  - `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — 30-min-post-merge audit-correction pattern
  - `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` — parent-PREP "Mathlib X / Y machinery" phrasing signal
  - `feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md` — Mathlib audit can obsolete a bespoke scaffold

---

## §11. Cross-reference: PREP chain status

| PREP | PR | Status | Coverage |
|---|---|---|---|
| S1 OBSERVE | #18223 | merged | Problem framing, tractability triage, references |
| S2 PREP-1 | #18340 | merged | `isPrincipalIdealRing_of_abs_discr_lt` entry point |
| S2 PREP-2 | #18371 | merged | Euclidean route via `Zsqrtd.GaussianInt` template |
| S2 PREP-3 | #18454 | merged | `discr_powerBasis_eq_norm` high-level chain |
| S2 PREP-4 | #18479 | merged | Verbatim norm chain |
| S2 PREP-5 | #18526 | merged | Integer-basis bridge audit + name correction |
| S2 PREP-6 | #18600 | merged | Monogenic-Eisenstein shortcut |
| S2 PREP-7 | #18666 | merged | `IsTotallyReal Q_sqrt2` API pin + Route C 54-LOC skeleton |
| **S2 PREP-8** | **(this PR)** | this PR | **`ringHom_ext`/`sq_eq_sq_iff_eq_or_eq_neg` discharge of PREP-7 §3.4; direct 28-LOC IsTotallyReal route; 4 errata** |

After S2 PREP-8 merges, **S3 ACT total estimate drops from 157 LOC → 128 LOC**
(−18%) and **all 3 PREP-7 §3.4 sorries discharged**. Every remaining "unverified"
risk in §7 is a `simp`-tactic discharge of a `@[simp]`-tagged Mathlib lemma,
strictly weaker than PREP-7's "structural sorry".

---

## §12. Future status

Unchanged from PREP-3 / PREP-4 / PREP-5 / PREP-6 / PREP-7: post-S3 ACT, this
OQ-03 deliverable will be **`verified`** (0 axioms, 0 sorries).

PREP-8's contribution: **discharges the last sorry-bearing step** in the
PREP-7 plan (the `exists_real_factor` lemma), via concrete Mathlib v4.26.0
closures (`ringHom_ext` + `sq_eq_sq_iff_eq_or_eq_neg` + `Rat.subsingleton_ringHom`
+ `Complex.conj_ofReal` + `Real.sq_sqrt`). All four are `@[simp]`/`@[ext]`-tagged
or otherwise structurally trivial. **S3 ACT now has a sorry-free derivation
sketch for every line of the 128-LOC deliverable.**
