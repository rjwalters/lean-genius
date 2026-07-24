# Knowledge Base: chinese-remainder-non-coprime-oq-01-oq-02

Insights accumulated during research on this problem.

**Phase**: ORIENT · **Status**: surveyed (paper resolution complete; Lean build gated by infra blackout 2026-06-13)

---

## Problem Understanding

**Open question (verbatim):** *Formalize the full Garner algorithm (not just the
mixed-radix decomposition) with runtime complexity bounds.*

The parent entry `chinese-remainder-non-coprime-oq-01`
(`ChineseRemainderNonCoprimeOQ01.lean`, Part IV) formalizes only the **k = 2**
mixed-radix fact:

```lean
theorem garner_mixed_radix (m n : ℕ) (x : ℕ) (hm : 0 < m) (hx : x < m * n) :
    ∃ c₁ c₂ : ℕ, x = c₁ + c₂ * m ∧ c₁ < m ∧ c₂ < n
```

plus uniqueness (`garner_mixed_radix_unique`) and the bound
`garner_coefficients_bounded`. That is the *representation existence* for two
moduli — it does **not** give the constructive reconstruction procedure for
`k` coprime moduli, nor the operation count. The sibling
`ChineseRemainderNonCoprimeList.lean` supplies a general-`R` list CRT
(`System`, `Compatible`, `ed_crt_list_iff`, `ed_crt_list_unique`) but it is
existence/uniqueness only — **no constructive coefficient algorithm**. So the OQ
is genuinely open in this gallery.

This survey resolves the mathematics completely on paper and pins down the exact
Lean formalization path. (Build-free: Docker daemon down + Aristotle backend 404
confirmed live this session — see the project verification-blackout note.)

---

## Insights

### 1. The full k-modulus Garner algorithm (Garner 1959; Knuth TAOCP vol 2, §4.3.2 Alg. 4.3.2C)

**Setup.** Pairwise-coprime moduli `m₁,…,m_k`, residues `r_i ∈ [0,m_i)`. Goal:
the unique `x ∈ [0, M)`, `M = ∏ m_i`, with `x ≡ r_i (mod m_i)` for all `i`.

**Mixed-radix (Garner) representation.** Write

```
x = v₁ + v₂·m₁ + v₃·m₁m₂ + ⋯ + v_k·(m₁m₂⋯m_{k-1}),   0 ≤ v_i < m_i.
```

Every `x ∈ [0,M)` has a unique such form (k-fold generalization of the parent's
`garner_mixed_radix`, which is exactly the `k = 2` case `x = c₁ + c₂·m₁`,
`M = m₁m₂`). Existence+uniqueness is a clean induction on `k` using the parent
lemma as the splitting step (`x = (x mod m₁) + m₁·⌊x/m₁⌋`, recurse on
`⌊x/m₁⌋ < m₂⋯m_k`).

**Why mixed-radix is the efficient target.** Each `v_i < m_i` (single-precision /
word-sized). All arithmetic that produces the `v_i` stays bounded by the
individual moduli; only the *final* assembly of `x` touches big integers.

### 2. Triangular system → forward substitution

Reduce the representation mod `m_i`. For `j ≥ i+1`, the term
`v_j·(m₁⋯m_{j-1})` is divisible by `m_i` (since `i ≤ j-1`), so it vanishes:

```
r_i ≡ v₁ + v₂m₁ + ⋯ + v_i·(m₁⋯m_{i-1})   (mod m_i).
```

This lower-triangular system is solved top-down:

```
v₁ = r₁ mod m₁
v_i = ( r_i − (v₁ + v₂m₁ + ⋯ + v_{i-1}·m₁⋯m_{i-2}) ) · (m₁⋯m_{i-1})⁻¹  mod m_i   (i ≥ 2)
```

The inverse `(m₁⋯m_{i-1})⁻¹ mod m_i` exists because every `m_j` (`j < i`) is
coprime to `m_i`.

### 3. Garner's Horner form (the actual algorithm — avoids big partial sums)

Precompute the pairwise inverse constants (moduli-only, residue-independent):

```
C_{ij} = (m_i)⁻¹ mod m_j   for i < j.
```

Then compute, using only mod-`m_i` arithmetic:

```
v₁ = r₁ mod m₁
v₂ = (r₂ − v₁)·C_{12}                              mod m₂
v₃ = ((r₃ − v₁)·C_{13} − v₂)·C_{23}                mod m₃
⋮
v_i = (⋯((r_i − v₁)·C_{1i} − v₂)·C_{2i} − ⋯ − v_{i-1})·C_{i-1,i}  mod m_i
```

**Telescoping proof that the Horner form equals the substitution formula** (the
key correctness lemma). For `i = 3`, with `C_{13}=m₁⁻¹`, `C_{23}=m₂⁻¹ (mod m₃)`:

```
((r₃−v₁)C_{13} − v₂)C_{23}
  = (r₃−v₁)·C_{13}C_{23} − v₂·C_{23}
  = (r₃−v₁)·(m₁m₂)⁻¹ − v₂·m₂⁻¹
  = m₂⁻¹·[ (r₃−v₁)·m₁⁻¹ − v₂ ]
  = (m₁m₂)⁻¹·(r₃ − v₁ − v₂m₁)     (mod m₃)   ✓  = v₃.
```

The general telescoping is an induction: peeling the outermost `·C_{i-1,i}`
multiplies the accumulated `(m₁⋯m_{i-2})⁻¹` by `m_{i-1}⁻¹` and subtracts the
matching `v_{i-1}` term, reproducing `(r_i − S_{i-1})·(m₁⋯m_{i-1})⁻¹` where
`S_{i-1}=v₁+v₂m₁+⋯+v_{i-1}m₁⋯m_{i-2}`.

### 4. Reconstruction of x (only big-integer step)

By Horner on the radices:

```
x = v₁ + m₁(v₂ + m₂(v₃ + ⋯ + m_{k-1}·v_k)) ,   x ∈ [0, M).
```

This is `O(k)` big-integer mul-adds; skip it entirely if the mixed-radix form is
the desired output (e.g. staying in a residue number system).

### 5. Runtime complexity bound (the second half of the OQ)

Let one **single-precision modular operation** = an `add/sub/mul mod m_i` on
word-sized operands.

| Phase | Cost | Notes |
|-------|------|-------|
| Inverse precompute `C_{ij}` | `O(k²)` ext-gcd inversions, `O(log max mᵢ)` each | moduli-only ⇒ amortized free across many conversions (RNS) |
| Forward (compute `v_i`) | `Σ_{i=1}^{k}(i−1) = k(k−1)/2 = O(k²)` single-precision mod ops | each `v_i` costs `i−1` mults + `i−1` subs, all `< m_i` |
| Reconstruct `x` | `O(k)` big-integer mul-adds | optional |

**The win vs. direct (Lagrange) CRT** `x = Σ r_i·M_i·(M_i⁻¹ mod m_i) mod M`,
`M_i = M/m_i`: that needs `O(k)` operations on `O(k·log m)`-**bit** numbers (true
multi-precision). Garner replaces every inner operation with single-precision
arithmetic — the classical Garner-1959 point that residue number systems support
multi-precision arithmetic via single-precision operations (already quoted in the
parent file's header).

The closed form `k(k−1)/2` is **pure `Nat` arithmetic** — provable by
`induction`/`Finset.sum_range_id`/`omega`, *no* Mathlib gap.

---

## Lean Formalization Path

**Tractable core (extends the parent directly; build-gated only by the blackout):**

1. `def garnerCoeffs (ms rs : List ℕ) : List ℕ` — forward substitution producing
   `[v₁,…,v_k]`. Modular inverse via the parent's idiom (`Int.gcdA`/`gcdB`,
   already used in `noncoprime_crt_efficiency_summary`) or `ZMod.inv`/
   `Nat.ModEq` over `ZMod m_i`.
2. `def garnerReconstruct (ms vs : List ℕ) : ℕ` — `List.foldr` Horner assembly.
3. **Main theorem** (the deliverable):
   `Pairwise Nat.Coprime ms → garnerReconstruct ms (garnerCoeffs ms rs) ≡ rs[i] [MOD ms[i]]`
   for each `i`, **and** `garnerReconstruct … < ms.prod`. Induction on the list;
   base case is the parent `garner_mixed_radix`.
4. **Uniqueness**: lift `garner_mixed_radix_unique` to the list (each `v_i` is
   determined mod `m_i`).
5. Reuse `ChineseRemainderNonCoprimeList.System`/`moduli` for the statement shape
   and `ed_crt_list_unique` for the uniqueness wiring.

**Complexity bound (the harder half):** Mathlib has **no operation-cost model**.
The honest, build-free formalizable route is an *instrumented* counter:
`def garnerCoeffsOps (ms : List ℕ) : ℕ` returning the number of modular ops the
recursion performs, with `garnerCoeffsOps ms = ms.length*(ms.length−1)/2` proved
by induction (pure `Nat`). This makes "runtime complexity bound" a *theorem about
an explicit step-count function*, the only rigorous reading available without a
cost monad. State `O(k²)` as the closed form of that counter.

### Mathlib inventory

- Present: `Nat.Coprime`, `Nat.chineseRemainder`, `ZMod.chineseRemainder`,
  `ZMod.inv`, `Nat.ModEq`, `Int.gcdA/gcdB`, `List.foldr/foldl`,
  `Finset.sum_range_id` (for `k(k−1)/2`), `List.Pairwise`.
- **Gap**: no complexity / cost-model API. ⇒ operation counts must be a
  hand-rolled `Nat`-valued counter (no external dependency, fully tractable).

---

## Dead Ends

- **Reading "runtime complexity bounds" as a Big-O over a real cost monad.**
  Mathlib lacks a machine/cost model; chasing one turns a 1–3 day algorithm
  formalization into an open-ended infrastructure project. The tractable reading
  is an explicit counter function with a proved closed form `k(k−1)/2`.
- **Trying to get the full algorithm "for free" from `ChineseRemainderNonCoprimeList`.**
  That file is existence/uniqueness over a general Euclidean domain — it never
  constructs the coefficients, so it cannot supply the Garner recursion. It is
  useful only for the *statement shape* (`System`/`moduli`) and uniqueness glue.

---

## Status / Next

- **Math: fully resolved on paper** (algorithm, telescoping correctness,
  `O(k²)` = `k(k−1)/2` count, formalization plan). Tractability 6 confirmed for
  the algorithm+correctness core; the complexity *bound* is the genuinely harder
  add-on (build-gated, plus the cost-model judgement call above).
- **Blocked on build**: Docker down + Aristotle 404 (blackout 2026-06-13). The
  `garnerCoeffs`/`garnerReconstruct` defs and the main correctness theorem need a
  Docker build to verify; no Lean committed this session.
- **Next action when infra returns**: implement steps 1–3 above in a new
  `ChineseRemainderNonCoprimeOQ01OQ02.lean`, base the correctness induction on
  `garner_mixed_radix`, then add the `garnerCoeffsOps` counter + closed-form
  lemma for the complexity half.

---

## RESOLUTION (2026-07-24, researcher-1)

The June survey plan was executed and the problem is **closed**:
`proofs/Proofs/ChineseRemainderNonCoprimeOQ01OQ02.lean` — 515 lines,
33 theorems, 11 definitions, 0 sorries, 0 axioms, no `native_decide`.
Docker-verified (8576 jobs, exit 0, Mathlib v4.31.0).

### What shipped (vs. the survey plan)

- Survey steps 1–4 all delivered: `garner` (list forward substitution),
  correctness `garner_correct`, bound `< ∏ mᵢ`, uniqueness `garner_unique`,
  digit identification `toDigits_garner`, plus the counter `garnerOps` with
  proved closed form `k(k−1)/2` (`garnerOps_eq`).
- **Proof-technique deviation worth remembering**: the survey's telescoping
  argument (products of inverses C₁ᵢ⋯C_{i-1,i}) was NOT needed. The
  incremental invariant — carry `x < P`, `result ≡ x [MOD P]`, and per-head
  congruence through one list induction (`garnerRec_spec`) — reduces each step
  to the single congruence `x + ((r−x)·P⁻¹ mod m)·P ≡ r [MOD m]`, closed by
  casting to `ZMod m` and `linear_combination (r − x) * (inverse identity)`.
  This pattern (ModEq statement, ZMod algebra, linear_combination close) is
  reusable for any modular-recurrence correctness proof.
- Truncation-safe digit formula: `(r % m + (m − x % m)) * modInv (P % m) m % m`
  — inner sub never truncates since `x % m < m`; `ZMod.natCast_mod` +
  `Nat.cast_sub` push it to `(r − x)·P⁻¹` cleanly.
- Kernel-reduction gotcha confirmed: `Nat.gcdA` (well-founded recursion) does
  not kernel-reduce, so the concrete example `garner [(3,2),(5,3),(7,2)] = 23`
  is proved from `garner_unique` + `decide` on the spec side, not by `rfl`.
- Cost-model judgement call resolved as planned: explicit `Nat` step counter
  (`stepOps`), per-step charge grounded by the reduced Horner inner loop
  `hornerMod` (`hornerMod_lt` single-precision, `hornerMod_modEq` faithful).
  Inverse precomputation deliberately outside the counter (moduli-only,
  amortized — Knuth's accounting), documented in file header + gallery entry.

### Artifacts
- Lean: `proofs/Proofs/ChineseRemainderNonCoprimeOQ01OQ02.lean`
- Gallery: `src/data/proofs/chinese-remainder-non-coprime-oq-01-oq-02/`
  (status verified, badge original, axiomCount 0)
- Branch/PR: `research/crt-oq01-oq02-garner`
