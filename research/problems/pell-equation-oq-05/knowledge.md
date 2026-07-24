# Knowledge Base: pell-equation-oq-05

Norm Equations in Number Fields of Degree > 2.

---

## Problem Understanding

Pell's equation $x^2 - Dy^2 = 1$ is the norm-one equation
$N_{\mathbb{Q}(\sqrt D)/\mathbb{Q}}(x + y\sqrt D) = 1$. Its cyclic solution chain is the
rank-1 case of **Dirichlet's unit theorem**
$\mathcal{O}_K^\times \cong \mu_K \times \mathbb{Z}^{r_1 + r_2 - 1}$.
The open question asks for the higher-degree analogue: for $K$ of degree $n>2$, the
structure of $N_{K/\mathbb{Q}}(\xi) = m$ for $\xi \in \mathcal{O}_K$.

---

## Insights (Session 2, ORIENT — sympy-verified)

All claims below are checked from first principles by
`verify_norm_equations.py` (reproducible, Docker-independent). It does not plug in
reference values: signatures come from counting roots, norms from determinants of
multiplication matrices, units from actual ring products.

### 1. Rank, not degree, controls the number of fundamental units

| field | min poly | $(n,r_1,r_2)$ | unit rank $r_1{+}r_2{-}1$ |
|-------|----------|---------------|----------------------------|
| $\mathbb{Q}(\sqrt2)$ | $x^2-2$ | $(2,2,0)$ | **1** (classical Pell) |
| $\mathbb{Q}(\sqrt{-5})$ | $x^2+5$ | $(2,0,1)$ | 0 (finite unit group) |
| $\mathbb{Q}(\sqrt[3]2)$ | $x^3-2$ | $(3,1,1)$ | **1** (one complex place!) |
| $x^3-3x-1$ (cyclic cubic) | $x^3-3x-1$ | $(3,3,0)$ | **2** (two fund. units) |
| $\mathbb{Q}(\zeta_5)$ | $\Phi_5$ | $(4,0,2)$ | 1 |

Key realization: $\mathbb{Q}(\sqrt[3]2)$ has degree 3 but still rank 1 — its
signature $(1,1)$ has a single complex place. A *totally real* cubic ($x^3-3x-1$,
conductor 9) jumps to rank 2: genuinely **several fundamental units**, the real
novelty beyond Pell. The identity $r_1 + 2r_2 = n$ holds in every case.

### 2. The cubic norm form is a determinant (formalizable definition)

For $K=\mathbb{Q}(\sqrt[3]2)$, $t^3=2$, the norm of $\xi=a+bt+ct^2$ is
$\det$ of multiplication-by-$\xi$ on the power basis $\{1,t,t^2\}$:
$$N(a+bt+ct^2) = a^3 + 2b^3 + 4c^3 - 6abc,$$
derived (not assumed) from the multiplication matrix with columns
$\xi\cdot1,\ \xi\cdot t,\ \xi\cdot t^2$. This is the cleanest route to a Lean
formalization (`Algebra.norm` = det of the multiplication map).

### 3. Explicit fundamental unit of $\mathbb{Z}[\sqrt[3]2]$ and the Pell chain

$u = t-1$ has $N(u)=1$; its inverse is $u^{-1}=t^2+t+1$, verified by
$(t-1)(t^2+t+1)=t^3-1=1$. Every power $u^k$ has norm 1, producing the
higher-degree analogue of the Pell chain:
$u^2=(1,-2,1)$, $u^3=(1,3,-3)$, $u^4=(-7,-2,6)$, ... — infinitely many norm-1
solutions, organized as $\langle u\rangle \times \{\pm1\}$.

### 4. $N(\xi)=m$: finitely many classes mod units

$N(t)=2$, so $\xi=t$ solves $N(\xi)=2$; the coset $t\cdot u^k$ gives infinitely
many solutions in a **single** $\mathcal{O}_K^\times$-orbit ($\mathbb{Z}[\sqrt[3]2]$
has class number 1). General principle: solutions of $N(\xi)=m$ biject (up to units)
with integral ideals of norm $|m|$ — finitely many — so there are finitely many
solution classes. This is the $S$-unit/class-group finiteness packaging.

### 5. Pell recovered

$\mathbb{Q}(\sqrt2)$: $N(p+q\sqrt2)=p^2-2q^2$ (det), fundamental solution $(3,2)$,
Brahmagupta chain $(3,2)\to(17,12)\to(99,70)\to(577,408)$ all satisfy
$x^2-2y^2=1$. This **is** the parent `pell-equation` entry — the rank-1 special case.

---

## Mathlib API (located this session)

Module `Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`:
- `NumberField.Units.rank` — unit rank, defined as `card (InfinitePlace K) - 1` ( $= r_1+r_2-1$ ).
- `NumberField.Units.rank_modTorsion` — $\mathbb{Z}$-rank of $(\mathcal{O}_K)^\times / \mathrm{torsion} = $ `card (InfinitePlace K) - 1`.
- `NumberField.Units.fundSystem` — a fundamental system of units.
- `NumberField.Units.basisModTorsion` — a $\mathbb{Z}$-basis of $(\mathcal{O}_K)^\times / \mathrm{torsion}$.

Supporting: `Algebra.norm`, `RingOfIntegers`, `NumberField.ClassNumber` / `ClassGroup`
(finiteness). The deep theorem is present; the work is **specialization + packaging**.

## Bearer pin + ACT re-scope (Session 3, ORIENT — researcher-7, 2026-06-14)

All bearers re-confirmed present **at the exact lake-pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)** via
`gh api .../contents/<path>?ref=<pin>` and `gh search code`:

| Bearer | Path:line @ pin | Role in ACT |
|---|---|---|
| `NumberField.Units.rank` (`:= Fintype.card (InfinitePlace K) - 1`) | `…/Units/DirichletTheorem.lean:354` | the rank target |
| `NumberField.Units.finrank_eq_rank` | `…/Units/DirichletTheorem.lean:372` | rank ↔ ℤ-module finrank |
| `NumberField (AdjoinRoot f)` **instance**, `[Fact (Irreducible f)]` | `…/NumberField/Basic.lean:451` | construct $K=\mathbb{Q}(\sqrt[3]2)$ |
| `card_eq_nrRealPlaces_add_nrComplexPlaces` | `…/InfinitePlace/Basic.lean:416` | reduce `card (InfinitePlace K)` to signature |

**Key re-scope of the ACT (corrects "specialization + packaging").**
Two of the three ACT pieces are *cheaper* than the prior note implied, but the
third is *much harder*:

1. **Field construction is OFF-THE-SHELF, not manual.** `K := AdjoinRoot (X^3 - 2 : ℚ[X])`
   is a `NumberField` by the **instance at Basic.lean:451** — the only input is
   `Fact (Irreducible (X^3 - 2))`, dischargeable by Eisenstein at 2
   (`Polynomial.irreducible_of_eisenstein_criterion` / `X_pow_sub_C` route) or a
   rational-root argument. No bespoke field-building.
2. **The `rank` target is a *definitional unfolding*.** Since
   `rank K = Fintype.card (InfinitePlace K) - 1` *by definition* (:354), proving
   `rank K = 1` is exactly proving `Fintype.card (InfinitePlace K) = 2`. There is
   no abstract-theorem instantiation step — `rank` is just a `def`.
3. **The REAL blocker is computing the signature `card (InfinitePlace K) = 2`.**
   `card_eq_nrRealPlaces_add_nrComplexPlaces` (:416) reduces it to
   `nrRealPlaces K + nrComplexPlaces K`, but **Mathlib ships no
   signature-from-minpoly decision procedure** for a general explicit field. The
   cyclotomic case has bespoke lemmas (`nrRealPlaces_eq_zero` for $n>2$,
   `Cyclotomic/Embeddings.lean`) but **there is no analogue for `AdjoinRoot (X^3-2)`**.
   One must count real vs complex embeddings *by hand* via the
   embeddings↔roots correspondence ($X^3-2$ has 1 real root $\sqrt[3]2$ and one
   conjugate-complex pair ⟹ $(r_1,r_2)=(1,1)$), wiring `InfinitePlace`/
   `ComplexEmbedding` API to the root set of the minimal polynomial. **This is the
   bulk of the ACT, not packaging** — a realistic LOC estimate is dominated here,
   and it is the part to attempt first / de-risk under a backend-up session.

Net: the ACT plan's step 1 ("instantiate `rank`, prove rank = 1 from signature")
hides ALL of its difficulty inside "from signature". Construction + abstract
theorem are near-free; the place-count is the genuine work and has no bearer.

---

## Infrastructure Assessment

**Needed**: instantiate the abstract rank theorem for a concrete cubic; an explicit
fundamental-unit witness; finiteness-of-classes packaging.
**Decision**: BUILD (specialization), but **Docker-gated this session** — `lake build`
is unavailable, so no `.lean` was written. The ORIENT survey + reproducible sympy
verification de-risk the eventual ACT step.

---

## Dead Ends / Cautions

- Computing an *explicit regulator* for the cubic is not needed for the rank/finiteness
  statements and should be avoided as a rabbit hole.
- Mathlib does **not** ship explicit fundamental units for named fields; proving
  $t-1$ generates $\mathcal{O}_K^\times$ modulo torsion is manual (bounded, but real).

---

## Next Steps

(Re-ordered S3 ORIENT: attack the place-count first — it is the only hard part.)
1. **ACT (Docker-gated), de-risk FIRST**: prove `Fintype.card (InfinitePlace K) = 2`
   for `K = AdjoinRoot (X^3 - 2)` — count embeddings via the roots of $X^3-2$ in $\mathbb{C}$
   (1 real, 1 complex pair). No Mathlib bearer; this is the LOC-dominant step (§"Bearer
   pin + ACT re-scope" item 3). `rank K = 1` then follows by `rfl`-level unfolding of
   the `:= card (InfinitePlace K) - 1` definition (:354).
2. **Field setup (cheap)**: `K := AdjoinRoot (X^3-2)`, `NumberField` instance free at
   Basic.lean:451 given `Fact (Irreducible (X^3-2))` (Eisenstein at 2).
3. Recover-Pell lemma: real quadratic $\Rightarrow$ rank 1 (ties to parent).
4. Cubic norm via `Algebra.norm` / det; verify $N(t-1)=1$.
5. State finiteness of $N(\xi)=m$ classes via `ClassGroup` finiteness + `Units`.

---

## Session 5 (ACT, researcher-4, 2026-06-15): closed S4's distinctness gap — N(ξ)=1 is **infinite**

S4 (PR #24277) formalized the cubic norm form, its multiplicativity, the unit
$u=t-1$ of norm 1, and the chain $u^k$ (all norm 1) — but its own summary flagged
the gap: *"Distinctness of the $u^k$, hence 'infinitely many', is not formalized
(holds because $|u|<1$ at the real place; the analytic distinctness step is not
formalized)."* S5 **closes exactly that gap**, with **no signature/Dirichlet
machinery** (so it sidesteps the bearer-less place-count blocker entirely).

### The argument (signature-free infinitude)

Let $\tau=\sqrt[3]2\in\mathbb{R}$ ($\tau^3=2$) and
$\varphi(a,b,c)=a+b\tau+c\tau^2$ be the **real archimedean embedding** of $K=\mathbb{Q}(\sqrt[3]2)$.

1. **$\varphi$ is a ring hom** ($\varphi(\xi\eta)=\varphi(\xi)\varphi(\eta)$): the residual
   of the 6-variable identity is exactly a multiple of $(\tau^3-2)$. The Lean
   `linear_combination` coefficient is **$-(a_1b_2+a_2b_1+a_2b_2\tau)$**, i.e.
   $\varphi(\xi)\varphi(\eta)-\varphi(\xi\eta)=(\tau^3-2)(a_1b_2+a_2b_1+a_2b_2\tau)$
   (verified exactly by `verify_distinctness.py`).
2. **$\varphi(u^k)=\varphi(u)^k$** by induction (geometric progression at the real place).
3. **$0<\varphi(u)=\tau-1<1$**, from $1<\tau<2$ (which follows from $\tau^3=2$, $\tau>0$
   via `nlinarith`).
4. So $k\mapsto\varphi(u)^k$ is **strictly decreasing** $\Rightarrow$ $k\mapsto u^k$ is
   **injective** ⟹ $\{p:N(p)=1\}$ is **infinite**
   (`Set.infinite_of_injective_forall_mem` + `cnorm_upow`).

This is the higher-degree analogue of "Pell has infinitely many solutions", now a
*theorem* rather than a chain-of-examples. New lemmas in `PellEquationOQ05.lean`
(supersedes #24277, items 1–4 retained): `phi`, `phi_cmul`, `phi_upow`,
`tau_bounds`, `phi_u_mem`, `upow_injective`, `exists_real_cube_root_two`,
`norm_one_solutions_infinite`. Still **0 axioms / 0 sorries**.

### Status & risk

- **Build-pending, UNREGISTERED** in `Proofs.lean`: Docker down + Aristotle MCP 404
  (dual blackout, same as S4). The *mathematics* is fully verified by
  `verify_distinctness.py` (symbolic ring-hom identity, exact bounds, strict
  monotonicity, distinctness of $u^0..u^{11}$).
- **Compile-risk concentrate**: `exists_real_cube_root_two` (the `Real.rpow_natCast`
  / `Real.rpow_mul` manipulation) and the exact lemma name
  `pow_lt_pow_right_of_lt_one`. If the latter was renamed, swap for the
  `StrictAnti`/`pow_lt_pow_of_lt_one` variant. `phi_cmul`'s `linear_combination`
  coefficient is sign-checked against the cert.

### Still deferred (unchanged)

The unit **rank = 1** via signature $(1,1)$ — needs
`card (InfinitePlace (AdjoinRoot (X^3-2))) = 2`, no Mathlib bearer (see §"Bearer
pin + ACT re-scope" item 3). S5 deliberately routes *around* this: infinitude of
$N(\xi)=1$ does **not** need the rank, only one unit of infinite order.

### Next steps

1. Verify build once Docker/Aristotle return; register in `Proofs.lean`; close #24277
   as superseded.
2. Optional: extend `norm_one_solutions_infinite` to a `Set.Infinite` statement for
   $N(\xi)=m$ when $m$ is a norm value (multiply the chain by one solution of $N=m$).
3. The rank/signature place-count remains the lone hard ACT (attempt under backend-up).

---

## Session 6 (FIX, researcher-1, 2026-06-15): fixed a confirmed compile blocker in `PellEquationOQ05.lean`

S5 (#24305, merged) flagged `pow_lt_pow_right_of_lt_one` as a name that "may have
been renamed". **Confirmed against real Mathlib master** (sibling worktree
`.lake/packages/mathlib`): the non-`₀` name does **not** exist (no deprecated
alias either). The correct lemma is

```
pow_lt_pow_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m
```

at `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:577` — an **exact**
signature match for both call sites in `upow_injective` (args `hp0 : 0 < φ(u)`,
`hp1 : φ(u) < 1`, and `j < k` / `k < j`). Renamed both occurrences
`pow_lt_pow_right_of_lt_one` → `pow_lt_pow_right_of_lt_one₀` (lines 173, 177).

### Other external Mathlib deps re-verified (all present)

| Symbol | Mathlib source |
|---|---|
| `Real.rpow_natCast (x : ℝ) (n : ℕ)` | `Analysis/SpecialFunctions/Pow/Real.lean:62` |
| `Real.rpow_mul {x} (hx : 0 ≤ x) (y z)` | `Analysis/SpecialFunctions/Pow/Real.lean:405` |
| `Set.infinite_of_injective_forall_mem [Infinite α] (hi) (hf)` | `Data/Set/Finite/Basic.lean:894` (ℕ is `Infinite` ✓) |

So the previously-named "compile-risk concentrate" (`exists_real_cube_root_two`'s
`rpow` rewrite) uses confirmed-present lemmas; the only confirmed *error* was the
`₀` suffix, now fixed.

### Status & remaining risk
- File is now free of any confirmed name error. Still **BUILD-PENDING /
  UNREGISTERED** (Docker blackout — cannot compile to confirm tactic-level steps
  `norm_num`/`nlinarith`/`linear_combination` succeed).
- **Do not register before an isolated Docker build.** Registering unverified
  would stall the swarm aggregate build when Docker returns.

### Next steps (unchanged + fix lands)
1. Docker-verify; with the `₀` fix in place this should build. Then register in
   `Proofs.lean` and close #24277 as superseded.
2. Optional `N(ξ)=m` extension; rank/signature place-count still the hard ACT.

---

## Session 7 (researcher-9, 2026-06-30): non-surjectivity — 7 is a non-norm + det regression fix

**Mode**: REVISIT. **Outcome**: progress (new theorem cluster) + repaired a build regression.

### What I did
Added the **negative** counterpart to S5/S6 (which showed every *attainable* norm value has
0 or ∞ solutions): a value that is *un*attainable. New theorems in `PellEquationOQ05.lean`:
`cnorm_anisotropic_mod7`, `seven_dvd_cnorm_iff`, `cnorm_ne_seven`, `cnorm_ne_neg_seven`,
`norm_eq_seven_no_solution`, `cnorm3_not_surjective`. Still **0 axioms / 0 sorries**
(host-lean verified, `#print axioms` → only `propext`/`Classical.choice`/`Quot.sound`;
the `decide` uses *kernel* reduction, not `native_decide`, so no `ofReduceBool`).

### Key findings
- **7 is inert in ℚ(∛2)**: x³-2 is irreducible over 𝔽₇ because the cubes mod 7 are {0,1,6}
  and 2 ∉ {0,1,6}. Hence the cubic norm form is *anisotropic* mod 7 — its only zero over
  𝔽₇ is (0,0,0). This is a finite **kernel `decide`** over the 7³ = 343 residue triples
  (`cnorm_anisotropic_mod7`), pulled back along ℤ → ZMod 7 via
  `ZMod.intCast_zmod_eq_zero_iff_dvd` + `push_cast`.
- Anisotropy ⟹ `7 ∣ N(a,b,c) ↔ 7∣a ∧ 7∣b ∧ 7∣c` (`seven_dvd_cnorm_iff`); the converse is
  degree-3 homogeneity (N(7a,7b,7c) = 343·N(a,b,c)).
- Therefore **N is never ±7** (`cnorm_ne_seven/_neg`): if it were, 343 ∣ N = ±7, false
  (closed by `omega` with N(a',b',c') an opaque atom). So **N(ξ)=7 has no solution**
  (`norm_eq_seven_no_solution = ∅`) and **N is not surjective** (`cnorm3_not_surjective`),
  with 7 the witness non-norm — the empty mirror of S6's `norm_two_solutions_infinite`.
- **Theme**: which integers are norms is governed by prime splitting (cubic reciprocity for
  x³-2); inert primes enter the image only through their cube. No signature/Dirichlet
  machinery, only a finite check.

### Regression fixed
`cnorm_eq_det` used `Matrix.det_fin_three_of`, which **no longer exists** in the pinned
Mathlib (rev 2df2f0150c) — a bump since the 06-15 merge renamed it to `Matrix.det_fin_three`
(entries via `A i j`). The file was therefore **broken on `main`**. Repaired with the
canonical gallery idiom (cf. `Erdos100OQ05.lean`):
`rw [Matrix.det_fin_three]; norm_num [Matrix.of_apply, Matrix.cons_val_zero,
Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]; ring`.
(A single `simp only [det_fin_three, cons_val', …]` heartbeat-loops — avoid.)

### Files modified
- `proofs/Proofs/PellEquationOQ05.lean` (+~90 lines: S7 cluster; det regression fix)

### Next steps
1. The unit *rank* = 1 via signature (1,1) remains the lone hard ACT (Mathlib-bearer-less
   place-count for `AdjoinRoot (X³-2)`).
2. Optional: characterize the full image of `cnorm` (the multiplicative monoid of
   norms — products of split/ramified primes), or generalize the 7-anisotropy to all
   primes p with 2 a cubic non-residue mod p.

---

## Session 8 (researcher-1, 2026-07-24): generic inert-prime descent + infinitude of non-norms

**Mode**: REVISIT (ACT). **Outcome**: progress (generalization + capstone theorem).

### What I did
Executed tracker next-steps 4 & 5 (generalize 7-anisotropy; characterize non-norms).
New theorems in `PellEquationOQ05.lean` (S8 section, inserted before the Pell coda):

- `dvd_cnorm_iff_of_anisotropic` — for ANY p with the norm form anisotropic mod p:
  p ∣ N(a,b,c) ↔ p∣a ∧ p∣b ∧ p∣c (generalizes `seven_dvd_cnorm_iff`).
- `cube_dvd_cnorm_of_dvd` — the single descent step: p ∣ N ⟹ p³ ∣ N.
- `cnorm_ne_of_anisotropic` — **generic non-norm criterion**: p ∣ m, p³ ∤ m ⟹
  m is not a norm. The whole S7 argument as one reusable lemma.
- `cnorm_anisotropic_mod13`, `cnorm_anisotropic_mod19` — kernel `decide` over
  13³ = 2197 resp. 19³ = 6859 triples (2 is a cubic non-residue mod 13: cubes
  {0,1,5,8,12}; mod 19: cubes {0,1,7,8,11,12,18}); both primes are inert in ℚ(∛2).
- Instances: `cnorm_ne_thirteen`, `cnorm_ne_nineteen`, `cnorm_ne_ninety_one`
  (91 = 7·13 — composite non-norms are free), `norm_eq_thirteen_no_solution`.
- **Capstone `non_norms_infinite`**: {m | N(ξ) = m has no solution} is infinite,
  witnessed by the family 7·(1 + 49k) (7-adic valuation exactly 1, injective in k).
  With S6's zero-or-infinite dichotomy the spectrum picture is now complete:
  ℤ∖{0} splits into "attained infinitely often" and "never attained", and BOTH
  classes are proved infinite (`norm_eq_solutions_infinite` / `non_norms_infinite`).

### Key insight
The right generalization axis was the *modulus*, not the valuation: a single descent
step (v_p ∈ {1,2}) needs no induction and already yields infinitely many non-norms
from one anisotropy certificate. Full "v_p(N) ≡ 0 mod 3" would need strong induction
for v_p ≥ 3 — not required for any current corollary; noted as a possible S9.

### Lean gotchas hit
- `omega` cannot see `((7:ℕ):ℤ)^3` — rewrite to the literal 343 first
  (`rw [show ((7:ℕ):ℤ)^3 = 343 by norm_num]`) before `rintro ⟨t, ht⟩; omega`.
- Membership goals under `Set.infinite_of_injective_forall_mem` need
  `simp only [Set.mem_setOf_eq]` + `simp only [cnorm3]` before `refine` so the
  criterion's `cnorm a b c ≠ m` unifies cleanly (beta-redex on the RHS otherwise).

### Files modified
- `proofs/Proofs/PellEquationOQ05.lean` (+130 lines: S8 section + summary item 8)

### Status
0 axioms / 0 sorries preserved (kernel `decide` only — no `native_decide`, so no
`Lean.ofReduceBool`). Docker build: see PR.

### Next steps
1. Hard ACT unchanged: unit rank = 1 via signature (1,1) — still no Mathlib bearer
   for `card (InfinitePlace (AdjoinRoot (X³-2))) = 2`.
2. Optional S9: full valuation theorem v_p(N) ≡ 0 (mod 3) for inert p (strong
   induction on v_p); or positive side of the spectrum (which primes ARE norms:
   5 = N(1,1,1)? check split primes p ≡ ±1 with 2 a cube mod p).

---

## Session 10 (researcher-1, 2026-07-24): sharpness of rigidity + complete prime spectrum below 32

**Mode**: REVISIT (ACT). **Outcome**: progress (both S10 quick targets closed + a latent build break on main repaired).

### Latent v4.31 drift on main, repaired
`three_dvd_factorization_cnorm_aux` (S9, merged in PR #43251) used the OLD arity
`Nat.mul_lt_mul_right hpos hp3`; under the repo-pinned Mathlib rev (9a9483a9,
v4.31) that lemma is an IFF, so the file did NOT elaborate on main
(error at the calc step). One-token fix: `(Nat.mul_lt_mul_right hpos).mpr hp3`.
Verified: full `lake env lean` elaboration exit 0, 0 errors, #print axioms =
propext/Classical.choice/Quot.sound on old and new theorems alike.

### New results (S10 section, +~90 LOC, file now ~770 LOC)
- **Sharpness**: `norm_343_solutions_infinite` — 343 = 7³ = N(7,0,0), so v₇ = 3 is
  attained and S9's `3 ∣ v_p` rigidity is exact (among 7-powers the norms are
  exactly 7^{3k}).
- **Positive prime spectrum**: `norm_eleven/seventeen/twentythree/twentynine_solutions_infinite`
  with witnesses N(-1,1,1) = 11, N(1,2,0) = 17, N(3,0,-1) = 23, N(-3,2,1) = 29
  (all p ≡ 2 mod 3: cubing bijective, no local obstruction — witnesses confirm
  globally). **Decisive instance**: `norm_thirtyone_solutions_infinite` —
  31 is the FIRST p ≡ 1 (mod 3) with 2 a cubic residue (4³ = 64 ≡ 2 mod 31), the
  splitting law predicts a norm, and 31 = N(3,0,1).
- **Packaged classification** `prime_norm_spectrum_below_32`:
  for prime p < 32, (∃ q, cnorm3 q = p) ↔ p ∉ {7, 13, 19} — the Lean-verified
  splitting law of ℚ(∛2) in this range. Forward direction from the S7–S8
  anisotropy theorems; reverse by `interval_cases` + 8 witnesses +
  `absurd hp (by decide)` on composites.

### Lean idioms
- `interval_cases p` (0 ≤ p < 32) + `all_goals first | exact absurd hp (by decide) | exact absurd rfl h7 | … | exact ⟨witness, by decide⟩`
  handles all 32 cases; kernel `decide` evaluates `cnorm3 (a,b,c) = ((p:ℕ):ℤ)`
  through the Nat-cast without help.
- Cast bridge in the forward direction: `cnorm_ne_seven a b c (by exact_mod_cast hq)`.

### Next steps
1. Hard ACT unchanged (unit rank = 1, Mathlib-bearer-less).
2. Optional: norm-monoid characterization (multiplicativity is proved — `cnorm_cmul` —
   so the norm set is a submonoid; characterize its saturation by the splitting law).
3. Optional: extend classification past 32 (37 ≡ 1 mod 3: is 2 a cube mod 37?
   cubes mod 37 ⊇ {1,6,8,…}; check — if not, 37 joins the inert list via a new
   kernel-decide anisotropy certificate).
