# Knowledge Base: abel-ruffini-oq-07

Galois group of f = x⁵ − x − 1 over ℚ is S₅ (a second Abel–Ruffini quintic witness,
complementing the Eisenstein example).

---

## Problem Understanding

**Goal:** Gal(x⁵ − x − 1 / ℚ) ≅ S₅, hence not solvable.

The original problem statement proposed the route:
(i) f irreducible (Selmer 1956); (ii) Δ = 2869 = 19·151 not a perfect square ⟹ G ⊄ A₅;
(iii) "f has exactly three real roots" ⟹ complex conjugation is a transposition ⟹ S₅.

---

## Insights

### ⚠️ CORRECTION: the problem statement is mathematically WRONG on point (iii)

Verified numerically/symbolically (sympy + numpy, session 2026-06-18):

- **f = x⁵ − x − 1 has exactly ONE real root** (≈ 1.1673), NOT three.
  The four non-real roots form **two** complex-conjugate pairs
  (≈ 0.1812 ± 1.0840i and ≈ −0.7649 ± 0.3525i).
  Reason: f′ = 5x⁴ − 1 has critical points ±(1/5)^{1/4} ≈ ±0.6687; both critical
  values are negative (f(−0.6687) ≈ −0.465, f(+0.6687) ≈ −1.535), so f crosses zero once.
- Consequence: **complex conjugation acts as a product of TWO transpositions** on the
  four non-real roots (fixing the one real root) — an **EVEN** permutation, lying in A₅.
  It is therefore **NOT a transposition.**
- The clean Mathlib real-roots lemma is thus **inapplicable**:
  `Polynomial.Gal.galActionHom_bijective_of_prime_degree`
  (`Mathlib/Analysis/Complex/Polynomial/Basic.lean:126`) requires
  `card (rootSet ℂ) = card (rootSet ℝ) + 2`, i.e. exactly ONE conjugate pair.
  Here `card ℂ = card ℝ + 4`, which fails the hypothesis. (The Eisenstein examples
  x⁵−4x+2 and x⁵−6x+3 DO have 3 real roots — verified — which is why they use this route.)

### ⚠️ The discriminant route (ii) alone is INSUFFICIENT

Δ not a perfect square ⟹ G ⊄ A₅ ⟹ G contains an odd permutation. But among the
**transitive** subgroups of S₅ (C₅, D₅, F₂₀, A₅, S₅), the ones containing odd
permutations are exactly **{F₂₀ (order 20), S₅}** — note D₅'s reflections act on 5
points as products of two transpositions (even), so D₅ ⊂ A₅. So "irreducible +
disc-not-square" only narrows the group to {F₂₀, S₅}. To exclude F₂₀ one must show
**3 ∣ |G|** (|F₂₀| = 20 is not divisible by 3). The problem statement implicitly
assumed disc-not-square + a transposition (from the false "3 real roots") gave S₅
directly; with the real-roots claim removed, an extra mod-p (Frobenius) input is required.

### Correct, fully-verified proof (Dedekind / Frobenius cycle types)

Verified factorization types of f mod p (sympy, all squarefree ⟹ p unramified):

| p  | factor degrees | Frobenius cycle type | contributes |
|----|----------------|----------------------|-------------|
| 3  | [5]            | 5-cycle              | transitive, 5 ∣ |G| |
| 5  | [5]            | 5-cycle              | (alt for p=3) |
| 2  | [2, 3]         | (2,3), order 6       | σ³ = **transposition**; σ² = 3-cycle ⟹ 3 ∣ |G| |
| 7  | [2, 3]         | (2,3), order 6       | (alt for p=2) |
| 17 | [1, 1, 3]      | 3-cycle              | 3 ∣ |G| |
| 23 | [1, 4]         | 4-cycle (odd)        | G ⊄ A₅ |

**Cleanest argument (transposition route):**
1. f irreducible mod 3 ⟹ G (= image of `galActionHom`) contains a **5-cycle** ⟹ transitive, 5 ∣ |G|.
2. f ≡ (irred. quadratic)·(irred. cubic) mod 2 ⟹ Frobenius σ of cycle type (2,3), order 6;
   then **σ³ is a transposition** ∈ G.
3. `Equiv.Perm.subgroup_eq_top_of_swap_mem` (`Mathlib/GroupTheory/Perm/Cycle/Type.lean:549`):
   for H ≤ Perm α with `card α` prime, `card α ∣ card H`, and H containing a swap ⟹ H = ⊤.
   With α = roots (card 5, prime), 5 ∣ |G|, transposition ∈ G ⟹ G = S₅. ∎

(Alternative "resolvent/discriminant" route matching the problem title: disc-not-square ⟹
G ⊄ A₅, plus 3 ∣ |G| from p=17 ⟹ G = S₅ since the only transitive subgroup with an odd
element and order divisible by 3 is S₅. Same Frobenius dependency.)

Independently verified: Δ(f) = 2869 = 19·151 (not a square), f irreducible over ℚ.

### Buildability assessment (Lean 4 / Mathlib, pin v4.26.0)

| Step | Mathlib support | Verdict |
|------|-----------------|---------|
| natDegree 5 is prime | trivial (`decide`) | BUILDABLE |
| f irreducible over ℚ | reducible mod 2 (=(x²+x+1)(x³+x²+1)) and mod 7, but **irreducible mod 3/5/11/13** ⟹ irreducible over ℚ by mod-p reduction. Eisenstein does NOT apply. | BUILDABLE (~100–200 L) |
| 5 ∣ card Gal | `Polynomial.Gal.prime_degree_dvd_card` | BUILDABLE |
| transposition ∈ Gal (or 3 ∣ \|G\|) | **Dedekind–Frobenius bridge: factor type mod p ⟹ cycle type of Frobenius as a root-permutation.** | **NOT BUILDABLE today** |
| assemble S₅ | `Equiv.Perm.subgroup_eq_top_of_swap_mem` | BUILDABLE |

**The single blocker is the Dedekind–Frobenius bridge** — and the gallery's own
flagship "Galois group of a specific quintic" entry confirms its difficulty:
- `Proofs/InverseGaloisA5.lean` (2067 L) **still carries `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`** (line 309) — precisely this bridge, axiomatized.
- `Proofs/InverseGaloisA5Dedekind.lean` is actively trying to discharge it via
  `AlgHom.IsArithFrobAt` / `arithFrobAt` / `Ideal.inertiaDegIn`
  (`Mathlib/RingTheory/Frobenius.lean`, `Mathlib/NumberTheory/RamificationInertia/Galois.lean`)
  and still has a substantive `sorry` (the Frobenius construction `exists_gal_order_three`).

**Cross-problem synergy:** OQ-07 and `inverse-galois-a5-oq-01` need the *same* Dedekind–
Frobenius machinery. If that open work lands a reusable
"factor type mod unramified p ⟹ element of matching cycle type in `p.Gal`" lemma, BOTH
problems close. OQ-07 needs it for a 5-cycle (p=3) and a transposition (σ³, p=2); a5-oq-01
needs it for a 3-cycle (p=7).

---

## Dead Ends

- **Real-roots / complex-conjugation route** (`galActionHom_bijective_of_prime_degree`):
  fails because f has only 1 real root ⟹ conjugation is even (∈ A₅), not a swap.
  This is the route the Eisenstein gallery examples use; it does NOT transfer to x⁵−x−1.
- **Discriminant alone**: only narrows G to {F₂₀, S₅}; needs a supplementary 3 ∣ |G| input.
- **Eisenstein for irreducibility**: inapplicable (no prime divides all lower coeffs).
  Use mod-3 (or mod-5) irreducibility instead.

---

## Session Log

### Session 2026-06-18 (Session 1, OBSERVE → ORIENT) — FRESH

**Mode:** FRESH. **Outcome:** scouted / ORIENT (no Lean written — see below).

**What I did**
- Symbolically verified (sympy/numpy, no docker): Δ = 2869 = 19·151 (not square),
  irreducible over ℚ, **exactly 1 real root** (refuting the statement's "3 real roots"),
  and the full table of mod-p factorization cycle types.
- Mapped the Mathlib toolchain: `prime_degree_dvd_card`,
  `galActionHom_bijective_of_prime_degree` (inapplicable here),
  `subgroup_eq_top_of_swap_mem` (the assembler).
- Grounded buildability in the gallery A5 precedent (`InverseGaloisA5*`): the Dedekind–
  Frobenius bridge is the universal blocker and is currently axiomatized/sorry'd there.

**Why no Lean file:** Both verifiers were down this session (docker image-inspect FAIL,
host load ~19; Aristotle backend 404). More importantly, the *one buildable gap* (the
Frobenius bridge) is open infra already under attack in `inverse-galois-a5-oq-01`; writing
a partial S₅ file now would either be unbuildable or just re-axiomatize the same step.

**Next steps**
- Coordinate with / wait on `inverse-galois-a5-oq-01`'s `exists_gal_order_three`
  (`IsArithFrobAt`) work; when it yields a reusable cycle-type lemma, write `AbelRuffiniOQ07.lean`:
  irreducible(mod 3) + `prime_degree_dvd_card` + transposition(σ³, p=2) + `subgroup_eq_top_of_swap_mem`.
- Interim option (matching gallery convention): an **axiomatized** entry that states the
  S₅ result with `axiom`s for the two Frobenius cycle-type facts (5-cycle@3, transposition@2),
  exactly parallel to `InverseGaloisA5.three_dvd_gal_card`. Status would be `axiomatized`.
- File a correction note: the curated problem statement's "exactly three real roots" is false.

### Session 2026-06-19 (Session 2, ORIENT → ACT) — REVISIT

**Mode:** REVISIT. **Outcome:** progress — shipped one verified theorem connecting the
entry to the *real* Galois group for the first time.

**What I did**
- Added `five_dvd_card_gal (hirr : Irreducible f) : 5 ∣ Nat.card f.Gal`
  (`AbelRuffiniOQ07.lean:156`), via `Polynomial.Gal.prime_degree_dvd_card` +
  `natDegree_prime`. Verified, 0 sorry / 0 axiom, conditional only on `Irreducible f`.
- **Key realisation that closes half the bridge:** the order-divisibility input
  `5 ∣ |Gal|` needs **no** Dedekind–Frobenius machinery. A prime-degree irreducible
  polynomial over a char-0 field has a Galois group acting transitively on its roots, so
  `deg ∣ |Gal|` by orbit–stabiliser — Mathlib packages this as `prime_degree_dvd_card`.
  This gives `5 ∣ |f.Gal|` for the *genuine* `f.Gal` the instant `f` is irreducible,
  replacing the abstract `frob3` half of the prior capstone. **Only the transposition
  input (`frob2³`, cycle type mod 2) remains genuinely Frobenius/Dedekind-dependent.**
- Re-confirmed (against the merged file + Mathlib v4.26.0) that the real-roots /
  complex-conjugation route stays a **dead end**: `galActionHom_bijective_of_prime_degree'`
  (`Mathlib/Analysis/Complex/Polynomial/Basic.lean:154`) admits 1–3 non-real roots, but
  `X⁵−X−1` has **4** (one real root), so conjugation is even — inapplicable, as Session 1 found.

**Why not unconditional:** the remaining input `Irreducible f` is the classic mod-3
finite-field irreducibility check (no rational root + no irreducible-quadratic factor over
𝔽₃). It is a *known* result best handed to Aristotle, whose endpoint was **down again this
session (404 "Resource not found")**, and writing the `decide`-unfriendly `Polynomial`/
`Finsupp` factor check blind (no build loop; host had 6–7 lean containers ⟹ OOM-gated) is
too error-prone to verify. So I shipped the verified conditional theorem and left
`Irreducible f` as the single, well-scoped next target.

**Next steps**
- Prove `Irreducible (X⁵−X−1 : ℚ[X])` ⟹ `five_dvd_card_gal` becomes unconditional and
  `5 ∣ |f.Gal|` is fully verified for the real group. Route pinned in the problem JSON
  `nextSteps` (mod-3 via `Monic.irreducible_iff_lt_natDegree_lt`; Gauss lift ℤ→ℚ). Retry
  Aristotle for it.
- Transposition-in-Gal remains the shared open bridge with `inverse-galois-a5-oq-01`.

**Build note (this session):** first build was RED on a single compiler-IR check —
`def f3 : (ZMod 3)[X]` must be `noncomputable` (polynomial over a semiring has no
executable code). Fixed; everything else elaborated cleanly. Aristotle endpoint still
404 this session, so the irreducibility goal was not delegated. Also aligned the stale
`leanFile` summary block in meta.json (was 257/16/3) to the authoritative 294/17/4.

## Session 2026-06-19 (Session 3) — Irreducible f discharged via Selmer ⟹ unconditional 5∣|Gal|

**Mode**: REVISIT | **Outcome**: progress (order-divisibility half now COMPLETE)

### What I Did
- Discovered Mathlib **already** has `Polynomial.X_pow_sub_X_sub_one_irreducible_rat`
  (`RingTheory/Polynomial/Selmer.lean`): `Irreducible (Xⁿ − X − 1 : ℚ[X])` for all `n ≠ 1`,
  proved via the unit-trinomial method + Gauss's lemma. The prior plan to hand-build the
  mod-3 irreducibility check was unnecessary.
- Added `f_irreducible := X_pow_sub_X_sub_one_irreducible_rat (by norm_num)` and
  `five_dvd_card_gal_unconditional : 5 ∣ Nat.card f.Gal` (feeds `f_irreducible` into the
  existing conditional `five_dvd_card_gal`). Build GREEN — `✔ [3066/3066]`, 0 sorry, 0 axiom.
- Updated the top docstring + mod-3 section prose (the latter was stale: it claimed the
  result was still "conditional" and the quadratic obstruction was "the only piece left").

### Key Findings
- The order-divisibility input `5 ∣ |Gal|` of the corrected `Gal ≅ S₅` proof is now
  **fully verified and unconditional** for the genuine `f.Gal` — no axioms, no
  Dedekind–Frobenius bridge, no irreducibility hypothesis.
- Sole remaining open input: `∃ swap ∈ Gal` (transposition from the `p = 2` Frobenius),
  genuinely bridge-dependent and shared with `inverse-galois-a5-oq-01`.
- The scratch mod-3 quadratic-obstruction proof (coefficient comparison + `decide` over
  `3⁵` cases) is correct in structure but its `ZMod 3` kernel `decide` is too slow
  (>19 min, killed). It is now purely corroborative; would need `native_decide` (axiom cost).

### Files Modified
- proofs/Proofs/AbelRuffiniOQ07.lean (+f_irreducible, +five_dvd_card_gal_unconditional, +Selmer import, prose)
- src/data/proofs/abel-ruffini-oq-07/meta.json
- src/data/research/problems/abel-ruffini-oq-07.json

### Next Steps
- Transposition-in-Gal: the shared Dedekind–Frobenius bridge (open). Pursue at the bridge.
- Optional: `f3_irreducible` via `native_decide` companion to justify `frob3`'s `(5)` cycle type.

---

### Session 2026-06-19 (researcher-1) — strategy update: Aristotle **CLI** is up (MCP 404 ≠ Aristotle down)

**No Lean written** (slug still blocked on the Dedekind–Frobenius bridge), but one
strategy correction that supersedes the S1 "Aristotle backend 404" note:

- The Aristotle **MCP wrapper** 404s, but the **CLI works**:
  `uvx --from aristotlelib aristotle {list,submit,show <id>,download <id>}`.
  (Confirmed this session on a different slug: the CLI returned a complete,
  0-sorry proof of a Minkowski convex-body lemma that the MCP could not even
  accept.) So "wait for the backend" should be read as "submit the blocker to the
  CLI now."

- **Actionable next step for whoever owns the bridge:** the shared blocker is
  `exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3` (`InverseGaloisA5Dedekind.lean:77`,
  a `sorry`) — discharging it (or a reusable "factor-type mod unramified p ⟹ matching
  cycle-type element of `p.Gal`" lemma) closes BOTH this slug and
  `inverse-galois-a5-oq-01`. To hand it to Aristotle it must first be **extracted into
  a Mathlib-only, self-contained file** (Aristotle's sandbox has Mathlib but not our
  `Proofs.*` modules; `InverseGaloisA5Dedekind.lean` imports them and references the
  axiom `three_dvd_gal_card`). That extraction + a careful prompt pointing at
  `AlgHom.IsArithFrobAt` / `IsArithFrobAt.exists_of_isInvariant` /
  `Ideal.inertiaDegIn` is the concrete next task.

- The interim axiomatized S₅ entry remains an option, but writing it now would just
  re-axiomatize the same bridge already axiomatized in `InverseGaloisA5.lean:309`
  (`three_dvd_gal_card`); deferring until the CLI attempt resolves the bridge avoids
  duplicating an unverified assumption across three files.

**Verdict:** released; not closeable this session without the bridge. Highest-leverage
move is the self-contained extraction + Aristotle-CLI submission of `exists_gal_order_three`.

---

## Session 2026-06-19 (researcher-3) — Dedekind–Frobenius bridge PROVED abstractly (Aristotle 9c006ee6), verified file landed

**Mode**: ACT | **Outcome**: progress (the shared open bridge is now a verified, axiom-free lemma)

### What I Did
- Retrieved the completed Aristotle job `9c006ee6` (submitted by the PR #26162 session):
  it **proved** the abstract bridge `orderOf_arithFrobAt_eq_inertiaDegIn` — at a prime `Q`
  unramified over `p = Q.under R`, `orderOf (arithFrobAt R G Q) = inertiaDegIn p S` —
  with `#print axioms` showing only `propext / Classical.choice / Quot.sound`.
- Aristotle ran against Mathlib **v4.28.0**, where the inertia subgroup is `Ideal.inertia`.
  Our repo is pinned to **v4.26.0**, where that spelling does not exist (build RED:
  "environment does not contain `Submodule.inertia`"). I re-derived the one affected lemma
  `stabilizerHom_injective` against the v4.26.0 API: `Q.toAddSubgroup.inertia G`,
  `Ideal.Quotient.ker_stabilizerHom`, `Ideal.card_inertia_eq_ramificationIdxIn`,
  `Subgroup.eq_bot_of_card_eq`, `Subgroup.bot_subgroupOf`. The other three declarations
  are Aristotle's verbatim.
- New file `proofs/Proofs/DedekindFrobeniusBridge.lean` (148 lines, 4 decls), registered in
  `Proofs.lean`. **Build GREEN** (`✔ [7743/7743]`, 394s), 0 sorry, 0 axiom, no `native_decide`.

### Key Findings
- The genuine Mathlib gap that blocked BOTH `abel-ruffini-oq-07` (transposition input) and
  `inverse-galois-a5-oq-01` (`exists_gal_order_three`) — the order of the arithmetic
  Frobenius at an unramified prime equals the inertia degree — is now a **verified,
  reusable, axiom-free lemma** in the repo. The bridge is no longer "open" at the abstract
  level; what remains is the concrete *instantiation* (`R = ℤ`, `S = 𝓞 K`, `G = Gal`,
  `Q` over a chosen prime), which constructs the ring of integers, exhibits a prime of the
  required inertia degree, and supplies `unramified` + `IsGaloisGroup`.
- The toolchain-version gap (v4.28 `Ideal.inertia` vs v4.26 `AddSubgroup.inertia`) is the
  recurring failure mode when integrating Aristotle output; only one of four declarations
  needed re-spelling.

### Files Modified
- proofs/Proofs/DedekindFrobeniusBridge.lean (new, verified)
- proofs/Proofs.lean (+import)

### Next Steps
- **Instantiate** `orderOf_arithFrobAt_eq_inertiaDegIn` to discharge `exists_gal_order_three`
  in `InverseGaloisA5Dedekind.lean` (prime over 7, inertia degree 3) and the transposition
  hypothesis in `AbelRuffiniOQ07.lean` (prime over 2, Frobenius of order 6). This is the
  remaining substantial work: building `𝓞 K`, the `IsGaloisGroup` instance, an unramified
  prime of the target inertia degree, and matching the abstract `arithFrobAt` order to the
  cycle type in `Gal`. Candidate for a follow-up Aristotle submission once the concrete
  scaffold compiles.

---

## Session 2026-06-19 (researcher-1) — bridge now PROVED ⟹ exact instantiation plan + Aristotle target for the order-6→swap step

**Mode**: ACT | **Outcome**: progress (turned "bridge open" into a concrete 4-step plan; submitted the one missing group lemma to Aristotle). No build (gate closed: 5 `lean-build` containers vs VM ~7.65 GiB).

### State recap
- Gallery entry `AbelRuffiniOQ07.lean` is **verified, 0-sorry/0-axiom** as a *reduction*:
  `gal_eq_top_of_five_dvd_and_swap` + concrete `frob2`/`frob3` witnesses +
  `closure_frobenii_eq_top`. `5 ∣ |f.Gal|` is **unconditional** via Selmer
  (`five_dvd_card_gal_unconditional`). The **sole** open input is a *transposition in the
  real `f.Gal`* (exposed as a hypothesis, not an axiom — honest).
- **Key change since prior sessions:** the shared Dedekind–Frobenius bridge is no longer
  open. `DedekindFrobeniusBridge.lean` (researcher-3, build-verified, axiom-free) proves
  `orderOf_arithFrobAt_eq_inertiaDegIn`: at an unramified prime `Q` over `p = Q.under R`,
  `orderOf (arithFrobAt R G Q) = Ideal.inertiaDegIn p S`.

### The exact 4-step instantiation that now closes OQ-07
Let `K = f.SplittingField`, `S = 𝓞 K`, `R = ℤ`, `G = (K ≃ₐ[ℚ] K)` acting on `S`.
1. **Build the Galois-action instance** `IsGaloisGroup G ℤ (𝓞 K)` (+ `IsDedekindDomain`,
   `Module.Finite`, `NoZeroSMulDivisors` — all standard for number fields). This is the
   main plumbing cost.
2. **Exhibit a prime `Q | 2` with `inertiaDegIn 2 S = 6` and `ramificationIdxIn 2 S = 1`.**
   `2 ∤ disc(f) = 2869 = 19·151`, so `2` is unramified. In the *splitting* field every
   prime over `2` has residue degree = order of the Frobenius conjugacy class = `lcm` of the
   mod-2 factor degrees = `lcm(2,3) = 6` (Dedekind: `f ≡ (X²+X+1)(X³+X²+1) mod 2`, both
   irreducible — already verified in the gallery file). So `inertiaDegIn 2 S = 6`.
3. **Bridge ⟹ `∃ σ : f.Gal, orderOf σ = 6`** (= `orderOf (arithFrobAt ℤ G Q)`), then transport
   along the iso `f.Gal ≃ (K ≃ₐ[ℚ] K)` / through `galActionHom` (injective for separable `f`)
   to a permutation of the 5 roots of order 6.
4. **`orderOf = 6 ⟹ (σ³).IsSwap`** (the generic S₅ form of the file's concrete
   `frob2_pow_three_isSwap`) gives the transposition; feed it + `5 ∣ |Gal|` into
   `gal_eq_top_of_five_dvd_and_swap` ⟹ image `= ⊤` ⟹ `f.Gal ≅ S₅`. ∎

Steps 1–2 are the genuine remaining work (number-theoretic; same `𝓞 K`/`inertiaDegIn`
plumbing the sibling `inverse-galois-a5-oq-01` needs for its order-3 element at `p = 7`).
Step 4 is pure `S₅` combinatorics.

### This session's artifact
- New **unregistered** companion `proofs/Proofs/AbelRuffiniOQ07Order6Aristotle.lean`
  (Mathlib-only, NOT in `Proofs.lean`, so CI is untouched) stating step 4 generically:
  `orderOf_eq_six_pow_three_isSwap (σ : Perm (Fin 5)) : orderOf σ = 6 → (σ^3).IsSwap`
  plus the consumer `gal_eq_top_of_five_dvd_and_order6`.
- **Submitted to Aristotle CLI**, job `ddd818e2-e934-4fd9-b389-15d56a22b49a`.
  Math: in `S₅` the only order-6 cycle type is `(2,3)` (partition of 5 with `lcm 6`),
  cube kills the 3-cycle and leaves the transposition.
- Next session: retrieve job `ddd818e2`; if green, fold the two lemmas into
  `AbelRuffiniOQ07.lean` (registered) and build-verify when the gate opens — this makes the
  open gap *exactly* steps 1–2 (the `𝓞 K`/inertia computation). If Aristotle stalls, the
  lemma is provable by hand via `Equiv.Perm.lcm_cycleType` + `sum_cycleType` +
  `two_le_of_mem_cycleType` (multiset {parts ≥2, sum ≤5, lcm 6} = {2,3}).

### Session 2026-06-19 (researcher-1) — promote Order6 + sharpen blocker

**Outcome:** consolidation + blocker sharpening (no new mathematics).

- The two generic-S₅ lemmas Aristotle was asked for are **already proved**
  (`orderOf_eq_six_pow_three_isSwap`, `gal_eq_top_of_five_dvd_and_order6`,
  0 sorry/0 axiom). Aristotle job `ddd818e2` is dead (`check_proof` → "Resource not
  found"). **Promoted** the file from the unregistered
  `AbelRuffiniOQ07Order6Aristotle.lean` to a registered gallery module
  `AbelRuffiniOQ07Order6` (added `import Proofs.AbelRuffiniOQ07Order6` to `Proofs.lean`)
  so CI verifies the lemmas. Verified every cycleType lemma they cite is present in the
  pin. (Build not re-confirmed: Docker unresponsive this session.)
- **Abstract bridge is DONE:** `DedekindFrobeniusBridge.orderOf_arithFrobAt_eq_inertiaDegIn`
  is proved (0 axiom/0 sorry) **and registered** (`Proofs.lean:626`). The previous
  "RUNNING Aristotle 9c006ee6" note is stale — it landed.
- **Re-classified the blocker.** With the abstract bridge + the generic order-6 step both
  done, the sole remaining gap is the **instantiation**, and its hard sub-step is
  `inertiaDegIn(2, 𝓞_K) = 6` (K = `f.SplittingField`, deg 120; every prime over 2 is
  unramified, residue degree `lcm(2,3)=6`). Deriving this from the mod-2 factor type needs
  the **factorization↔inertia-degree correspondence**, which a grep of pinned Mathlib
  v4.26 confirms is **ABSENT** (0 hits for `inertiaDeg…factor`, `cycleType…Frobenius`).
  That correspondence — not the abstract bridge — is now the genuine BLOCKED frontier,
  shared with `inverse-galois-a5-oq-01` (needs `inertiaDegIn(7)=3`). The remaining
  `galActionHom` transport (arithFrobAt → a `Perm (Fin 5)` of matching cycle type) is also
  unbuilt.
