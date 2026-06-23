# elementary-quadratic-reciprocity-oq-01-oq-03-…-oq-02 — Zolotarev shuffle → QR

**Problem.** Follow-up #1 of the "Zolotarev–Frobenius for every odd modulus"
capstone (`…-oq-01`): derive the quadratic reciprocity law
`(q/p)(p/q) = (-1)^((p-1)/2·(q-1)/2)` *directly* from the verified general-odd
sign identity `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd`
(`sign(x ↦ a·x on ℤ/n) = J(A|n)`) via the sign of the rectangular
transpose / perfect-shuffle permutation, as in Zolotarev 1872 / Frobenius 1914.

**File.** `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
(**registered in `Proofs.lean`, 0 `sorry`, kernel-verified**).

## Status

| Component | State |
|-----------|-------|
| `gridTranspose m n` (perfect-shuffle perm of `Fin (m*n)`) | proved (def) |
| `gridTranspose_apply` (row-major `n·i+j` ↦ col-major `m·j+i`) | proved |
| encoding helpers `fpe_val/symm/divNat/modNat`, `gridTranspose_val`, `finCongr_lt`, `encode_lt`, `card_strict_pairs` | **proved, 0 sorry** |
| `neg_one_pow_choose_two_mul_odd` (parity bridge `(-1)^(C(m,2)C(n,2))=(-1)^((m-1)/2·(n-1)/2)`) | **proved, 0 sorry** |
| `sign_gridTranspose = (-1)^(C(m,2)·C(n,2))` | **PROVED, 0 sorry, kernel-verified** (axioms `[propext, Classical.choice, Quot.sound]`) |
| `sign_gridTranspose_odd` (classical-form corollary) | **proved, 0 sorry** |
| `rowOrder`/`colOrder`/`gridTranspose_eq`/`transRC`/`sign_transRC` | **proved, 0 sorry, kernel-verified** (S5) |
| `quadratic_reciprocity_of_transition_signs` (Shurman 3-transition skeleton → QR, conditional on the two per-line Zolotarev signs) | **proved, 0 sorry, kernel-verified** (S5; axioms `[propext, Classical.choice, Quot.sound]`) |
| Discharge per-line signs `sign τ_cd=(p/q)`, `sign τ_rd=(q/p)` for the concrete CRT `D` | not formalized (next step) |

## Session 2026-06-23 (S5, researcher-9) — QR ASSEMBLY SKELETON FORMALIZED & VERIFIED

**Mode**: REVISIT (continuation of own S4). **Outcome**: progress — the QR
assembly is now a kernel-verified 0-sorry *conditional* theorem, and the
previously *incorrect* assembly plan was replaced with the literature-verified one.

### Key correction (mathematical)
The S1–S4 file-header plan ("α = β∘γ, identify α,β with `ringMulPerm` on ℤ/pq via
the CRT isomorphism") was **wrong**: a direct coordinate computation shows the
transpose mixes the two CRT coordinates and does **not** decompose as a CRT
product. The correct argument is J. Shurman's "proof from the book" (after
Zolotarev 1872 / Baker 2013, https://people.reed.edu/~jerry/361/lectures/qrz.pdf):
**three order-transition permutations** of the `p×q` array,
`τ_rd = D⁻¹∘R`, `τ_cd = D⁻¹∘C`, `τ_rc = C⁻¹∘R` (R/C/D = row/col/diagonal-CRT
orders `Fin p × Fin q ≃ Fin(pq)`), with the **tautology** `τ_cd⁻¹∘τ_rd = τ_rc`.
Signs: `sign τ_cd=(p/q)`, `sign τ_rd=(q/p)` (Zolotarev's lemma on the per-line
multiplication maps `y↦py+x mod q`); `sign τ_rc=(-1)^((p-1)/2·(q-1)/2)` — which
is exactly the proven `sign_gridTranspose`, since `τ_rc` IS `gridTranspose p q`
transported across `R`. QR `=` the relation `sign τ_cd·sign τ_rd = sign τ_rc`.

### What I Did
- Web-researched + fetched Shurman's PDF; extracted the exact three-transition
  identity and per-line signs (§3).
- Added (0 sorry, **kernel-verified**): `rowOrder`, `colOrder`, `gridTranspose_eq`
  (`gridTranspose = R⁻¹∘C`, by `rfl`), `transRC`, `sign_transRC` (`sign τ_rc =
  sign gridTranspose` via `Equiv.Perm.sign_eq_sign_of_equiv` conjugation by `R` +
  `Int.units_eq_one_or`), and the headline
  `quadratic_reciprocity_of_transition_signs`: for odd primes `p,q` and any
  diagonal order `D`, IF `sign(R.trans D⁻¹)=(q/p)` and `sign(C.trans D⁻¹)=(p/q)`
  THEN `legendreSym q p · legendreSym p q = (-1)^((p-1)/2·(q-1)/2)`.
- Proof skeleton = `τ_cd⁻¹*τ_rd = τ_rc` (tautology; `D⁻¹`s cancel via
  `Equiv.symm_trans_self`) + sign-product (ℤˣ exponent 2) + `sign_transRC` +
  `sign_gridTranspose_odd` + cast to ℤ.
- Rewrote the header plan docstring with the correct Shurman blueprint; added the
  Shurman reference.

### Verification (kernel-checked)
- Docker wedged + concurrent docker builds (researchers 1/5/10/12) churning the
  shared Mathlib build cache → first `lake env lean` raced a mid-write `.ir`.
- **GOTCHA (cost ~1 cycle): my first edits went to the MAIN-repo path
  `/…/lean-genius/proofs/…` instead of the worktree → a concurrent process on
  `main` reverted them, and the "passing" build only tested the OLD file.** The
  worktree's `proofs/.lake` is a **symlink** to the main `.lake`, so edit+build
  must both happen in the worktree (`.loom/worktrees/researcher-9/proofs`).
- Re-applied in the worktree; `./bin/lake env lean <file>` exit 0, zero
  errors/warnings/sorries; `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` for both
  `quadratic_reciprocity_of_transition_signs` and `sign_transRC` (no `sorryAx`,
  no `Lean.ofReduceBool`).

### Files Modified
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
  (header plan rewritten; new `Assembly` section, +5 decls, kernel-verified).
- this knowledge.md; problem JSON.

### Next Steps
1. Build the concrete CRT order `D : Fin p × Fin q ≃ Fin(pq)` (`ZMod.chineseRemainder`
   + `ZMod n ≃ Fin n`).
2. Prove `sign(C.trans D⁻¹)=(p/q)`: `D⁻¹∘C` fixes each row and acts on row `x` by
   `y↦py+x mod q` = (mult-by-`p` on ℤ/q)∘(translation by `x`); use
   `Equiv.Perm.sign_prodCongrRight`, translation = odd-length cycle (sign +1 for
   odd q), `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd` (= legendre at a
   prime). Symmetric for `sign(R.trans D⁻¹)=(q/p)`.
3. Discharge both hypotheses → unconditional QR without Mathlib's black-box
   `legendreSym.quadratic_reciprocity`.

## Session 2026-06-23 (S4, researcher-9) — BLOCKER PROVED & VERIFIED

**Outcome:** the shared Zolotarev inversion-count blocker `sign_gridTranspose` is
now **kernel-verified** (0 sorry, axiom-clean) and is the live definition in the
gallery file, now registered in `Proofs.lean`.

**How verification was finally achieved.** Both backends were down (Docker daemon
wedged — `docker version`/`image inspect` time out; Aristotle MCP still 404).
*Pivot:* Mathlib oleans were already built locally (`proofs/.lake/packages/mathlib`),
and `lake env` is whitelisted by the `proofs/bin/lake` safety wrapper, so the single
file was compiled directly with `lake env lean Proofs/<file>.lean` over the cached
oleans — no Docker, no Mathlib rebuild. Gotchas: (1) the cache lacked the **root
aggregators** `Qq.olean`/`Batteries.olean` (only `import Mathlib`'s top module needs
them) — built with `lake env lean -Dexperimental.module=true -R . <Pkg>.lean -o …`;
(2) `lake exe cache get` ("exe", allowed) restored ~7727 partially-missing Mathlib
oleans. Ran everything under a `ulimit -v` cap as a memory safety net.

**Two fixes vs. the S2/S3 candidate draft.** (1) `Finset.sum_product'` failed (HO
pattern `?f x.1 x.2` won't unify with the `if x.1 < x.2 …` summand) → first-order
`Finset.sum_product` + `dsimp only` (2 sites). (2) `Finset.card_Iio` → `Fin.card_Iio`;
reworked `hsum` inner step with `Finset.sum_filter` + `by_cases hh : i < J <;> simp [hh]`.
Also `Fin.lt_iff_val_lt_val`/`le_iff_val_le_val` → `Fin.lt_def`/`le_def` (deprecation-clean).

**Next step.** Formalize the QR assembly: `α = β ∘ γ`, `sign α = sign β · sign γ`,
identify `sign α`,`sign β` with per-line Zolotarev signs `(q/p)`,`(p/q)` through the CRT
isomorphism and `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd`, then combine with
`sign_gridTranspose_odd` to get `(q/p)(p/q) = (-1)^((p-1)/2·(q-1)/2)`.

## Session 2026-06-23 (S2, researcher-9) — BLOCKER ROUTE DE-RISKED via Mathlib bridge

**Mode:** continue WIP on branch `research/zolotarev-quadratic-reciprocity-oq010302`.
**Outcome:** the prior 3-session "no Mathlib lemma" assessment of the blocker is
**out of date**; a clean route now exists and a full candidate proof is written.

### Key finding (overturns S1 + sibling-thread assessment)
Prior sessions (here + algorithm-M2 S8/S18/S21) all concluded "NO Mathlib lemma
gives `sign = (-1)^(#inversions)` for a general permutation; only route is ~100
LOC of `signAux`/`finPairsLT` surgery." **This is false as of current Mathlib.**

    `Equiv.Perm.sign_eq_prod_prod_Iio` (Mathlib/GroupTheory/Perm/Fin.lean, §Sign)
      : σ.sign = ∏ j, ∏ i ∈ Finset.Iio j, (if σ i < σ j then 1 else -1)

Each factor is `-1` exactly on an inversion `i<j ∧ σ i>σ j`, so
`sign σ = (-1)^(#inversions)` directly — no `signAux` surgery. The blocker
reduces to the **elementary** count `#{(I,J): I<J ∧ T I>T J} = C(m,2)·C(n,2)`.

### The reduction (fully worked out)
1. `rw [Equiv.Perm.sign_eq_prod_prod_Iio]`.
2. Inner `∏ i ∈ Iio j, ite (T i < T j) 1 (-1) = (-1)^(card of inversions ≤ j)`
   via `Finset.prod_ite` + `Finset.prod_const`.
3. `Finset.prod_pow_eq_pow_sum` ⇒ `(-1)^(∑ j, …)` = `(-1)^(#Inv)` where
   `Inv = univ.filter (p.1<p.2 ∧ ¬ T p.1<T p.2)`.
4. Bijection `Inv ≃ strictPairs(Fin m) ×ˢ strictPairs(Fin n)`,
   `(I,J) ↦ ((I.divNat,J.divNat),(J.modNat,I.modNat))`, via `Finset.card_bij'`.
   Well-definedness uses the **mixed-radix lemma** `encode_lt` (proved):
   `finProdFinEquiv (a,c) < finProdFinEquiv (b,d) ↔ a<b ∨ (a=b ∧ c<d)` (omega
   after feeding `Nat.mul_le_mul_left`), and `gridTranspose_val`
   (`T(finProdFinEquiv (a,d)).val = a + m*d`).
5. `#strictPairs(Fin k) = C(k,2)` via group-by-2nd-coord ⇒ `∑ b, #(Iio b)`
   ⇒ `∑ b:Fin k, ↑b` ⇒ `Finset.sum_range_id` (Gauss) ⇒ `Nat.choose_two_right`.

### Deliverable
`sign_gridTranspose_candidate.lean` (this dir) — a COMPLETE candidate proof
(def + `encode_lt`, `gridTranspose_val`, `card_strict_pairs`, the bijection).
**NOT kernel-verified**: Docker daemon wedged this session (`docker ps`/`images`
empty, no container ever spawns; ≥6 sibling builds stuck 1.7h, `docker stop`
processes piled up) and Aristotle MCP still returns "Resource not found".
A few API names (`Fin.coe_cast`, `finCongr_apply`, `not_lt`, `Finset.univ_product_univ`)
are best-effort and may need a one-pass fixup when a build backend recovers.
Registered file's `sign_gridTranspose` docstring updated to cite the bridge.

### Next steps (priority order)
1. When Docker/Aristotle recover: build/verify `sign_gridTranspose_candidate.lean`;
   fix any API-name slips; then port the proof body into BOTH registered files
   (this one + `QuadraticReciprocityAlgorithmOQ03M2`) replacing the shared `sorry`.
2. Then this file becomes 0-sorry up to the QR assembly; promote toward verified.
3. Higher-value remaining novel work: the QR assembly (`α=β∘γ`, identify `α,β`
   with `ringMulPerm` via CRT) — neither thread has formalized it.

## Session 2026-06-23 (S1, researcher-9) — parity bridge proven; CROSS-THREAD DUPLICATION found

**Mode:** continue WIP on branch `research/zolotarev-quadratic-reciprocity-oq010302`.
**Outcome:** progress (1 verified lemma added) + significant non-novelty finding.

### What I did
- Proved `neg_one_pow_choose_two_mul_odd` (parity bridge) and the corollary
  `sign_gridTranspose_odd`, making the file self-contained up to the single
  combinatorial `sorry`. Proof of the bridge: `n=2a+1` ⇒ `C(n,2)=(2a+1)a≡a (mod 2)`
  via `Nat.choose_two_right` + `omega`; the `(-1:ℤˣ)` power-mod-2 helper is built
  from `Int.units_sq` (`(-1:ℤˣ)^2=1`, monoid-level), `pow_add`/`pow_mul`.
- **Avoided the documented `ℤˣ` gotcha:** Mathlib's `neg_one_pow_eq_pow_mod_two`
  is `section Ring` (`[Ring R]`); `ℤˣ` is not a ring, so it does NOT apply.

### Key finding — this file duplicates merged sibling work
`neg_one_pow_choose_two_mul_odd` reproduces the **already-verified**
`QuadraticReciprocityAlgorithmOQ03M2.neg_one_pow_choose_two` (merged #25053).
The two files share an identical `gridTranspose` def and the **identical sole
blocker**: `sign_gridTranspose = (-1)^(C(m,2)·C(n,2))`
(= sibling's `sign_gridTranspose_eq_choose`). So the elementary half of this
follow-up is *not novel* — it was solved in the algorithm lineage.

### The blocker (assessed identically by ≥3 sibling sessions, S18/S21 there)
No Mathlib lemma gives `sign = (-1)^(#inversions)` for a general permutation:
`Sign.lean` exposes only `signAux`/`signBijAux`/`finPairsLT`; `IsCycle.sign` is
cycle-specific; `sign_prodCongrLeft/Right`/`sign_sumCongr` need block-diagonal
structure, but the transpose is a *coordinate swap*, not block-diagonal. The only
route is the explicit `Finset.card_bij`
`inversions(gridTranspose m n) ↔ {i<i' : Fin m} × {j>j' : Fin n}`, card `C(m,2)·C(n,2)`,
unfolded from `signAux = ∏_{finPairsLT}`. ~100 intricate LOC. The numerical
bijection is certified in the sibling's `verify_grid_inversions.py` /
`verify_inversion_bijection.py`.

### Why no Lean proof of the blocker this session
Double blackout reconfirmed live: Docker daemon hung (`docker version` → exit 124);
Aristotle MCP `prove` → `"Resource not found"`. With zero build/search feedback,
blind-writing ~100 LOC of `signAux`/`card_bij` would very likely not compile and
would be mislabeled progress — the standing sibling-thread prohibition. Deferred.

### Recommendation (convergence, not a 3rd scaffold)
The program now has TWO parallel gridTranspose scaffolds (this file + algorithm
M2) blocked on the same lemma. Future work should either (a) finish the single
inversion-count lemma once Docker/Aristotle recover and share it, or (b) have
this elementary-lineage file *import/cite* the algorithm result and instead
formalize its genuinely distinct part — the **QR assembly** (`α=β∘γ`, identifying
`α,β` with `ringMulPerm` through CRT), which NEITHER thread has done.

### Next steps
1. When Aristotle recovers: submit `sign_gridTranspose` (self-contained, KNOWN/HARD).
2. When Docker recovers: build this file (`docker-build.sh Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02`); the parity-bridge edits are high-confidence (mirror verified sibling code).
3. Higher-value than re-deriving the blocker: formalize the QR assembly using
   `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd` + `sign_gridTranspose_odd`.

### Files modified
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-03-…-oq-02/knowledge.md` (new)

---

## Session 2026-06-23 (Session 3) — Candidate API audit (de-risk, no kernel check)

**Mode**: REVISIT
**Outcome**: progress (verification infra still down; mathematical/API risk reduced)

### What I Did
- Session preamble: both verifiers still down — Docker daemon wedged (`docker version`
  shows Client only, no Server; `docker ps`/`images` empty), Aristotle MCP
  `prove_file` returns "Resource not found" (connected but backend resource 404).
  So no kernel verification was possible this session either.
- Highest-value reachable action: full **API audit** of the complete candidate proof
  `sign_gridTranspose_candidate.lean` against the pinned Mathlib source on disk
  (rev 2df2f0150c, Lean v4.26.0, `proofs/.lake/packages/mathlib`).

### Key Findings
- EVERY lemma name in the candidate is present with a compatible signature:
  - `Equiv.Perm.sign_eq_prod_prod_Iio` (Perm/Fin.lean:478) — factor form
    `if σ i < σ j then 1 else -1` matches `inner` exactly.
  - `Finset.prod_pow_eq_pow_sum` (BigOperators/.../Basic.lean:656) — exact form.
  - `finProdFinEquiv` (Logic/Equiv/Fin/Basic.lean:329): `toFun ⟨x.2 + n*x.1,_⟩`,
    `invFun (x.divNat,x.modNat)` ⟹ `fpe_val` (val = c+q*a) and `fpe_symm` hold by `rfl`.
  - `Fin.divNat`/`Fin.modNat` (Batteries Data/Fin/Basic.lean:133/137), correct types.
  - `Fin.coe_cast` (alias of `val_cast`), `finCongr_apply` (@[simp]) — present.
  - `Finset.card_bij'` (Data/Finset/Card.lean:366) — arg order
    `(i,j,hi,hj,left_inv,right_inv)` matches the four `?_` obligations IN ORDER.
  - All supporting Finset/Nat lemmas confirmed (sum_filter via to_additive prod_filter).
- The two names the prior draft flagged "best-effort" (`finProdFinEquiv_symm_apply`,
  `Fintype.sum_prod_type`) are NOT used in the proof body — dropped from caveats.
- NET: remaining risk reduced from "do these lemmas exist / right names?" (now: YES,
  all confirmed) to purely term-level "do the rw/simp steps fire?" — mechanical,
  build-only. Honest status unchanged: still UNVERIFIED, not registered/verified.

### Files Modified
- `sign_gridTranspose_candidate.lean` — header STATUS block rewritten with the audit.
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03…OQ02.lean` — cross-ref note
  updated (API audited; only rw/simp firing remains).
- this knowledge.md.

### Next Steps (unchanged priority)
1. When EITHER verifier recovers: build/submit the candidate; expect ≤ a couple of
   `simp`/`rw` adjustments at most, since all names are confirmed.
2. Integrate the verified proof into the registered file, discharging the lone sorry.
3. Then formalize the genuinely-missing QR assembly (`α=β∘γ` via CRT) — higher value
   than the blocker, untouched by either gridTranspose thread.

## Session 2026-06-23 (researcher-9, S6) — Per-line affine→Legendre Zolotarev sign PROVED

**Mode**: REVISIT (continuing the assembly skeleton thread)
**Outcome**: progress — the per-residue-line number-theoretic step is now a
kernel-verified lemma (0 sorry, axioms `[propext, Classical.choice, Quot.sound]`).

### What I Did
- Added to the registered file `…OQ02.lean` (now 588L, builds clean) three new
  theorems discharging the *per-line* content of the two transition-sign
  hypotheses of `quadratic_reciprocity_of_transition_signs`:
  - `sign_addLeft_odd {n}[NeZero n] (Odd n) (b) : sign (Equiv.addLeft b) = 1` —
    **translation is an even permutation on an odd-order group** (absent from
    Mathlib). Proof: `(addLeft b)^n = addLeft (n•b) = addLeft 0 = 1` (since
    `n•b=0` in `ZMod n`); `sign` lands in order-2 `ℤˣ`, so an odd power of it
    equals it, and that power is `sign 1 = 1`. Uses `pow_addLeft`, `addLeft_zero`,
    parent `ZolotarevCRT.units_pow_odd`.
  - `sign_addLeft_mul (Odd n)(b)(P) : sign (addLeft b * P) = sign P` — corollary,
    `map_mul` + the above.
  - `sign_affineLine_eq_legendreSym {p}[Fact p.Prime](p≠2)(a)(b)(A)(A≡a) :
    (sign (addLeft b * ringMulPerm a) : ℤ) = legendreSym p A` — **the per-line
    Zolotarev sign**: affine `x ↦ a·x+b` on `ℤ/p` has sign `(A/p)`. Combines the
    translation-parity lemma with the parent's Zolotarev–Frobenius identity
    `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd` and `jacobiSym.legendreSym.to_jacobiSym`.

### Key Findings
- The correct per-line model is **affine**, not pure multiplication: `D⁻¹∘rowOrder`
  acts per column `j` by `i ↦ q·i + j (mod p)` (a translation by `j` after
  mult-by-`q`). The translation is exactly the part that needed the new even-perm
  lemma; mult-by-`q` is the parent's already-proven Zolotarev sign.
- Mathlib has NO translation-sign lemma; the odd-order/odd-power argument is clean
  (`pow_addLeft` + `units_pow_odd`).
- `legendreSym.to_jacobiSym` is declared INSIDE `namespace jacobiSym`, so its real
  name is `jacobiSym.legendreSym.to_jacobiSym` (the bare name is unknown-constant).

### Files Modified
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
  (added per-line section + imports parent `…OQ01OQ01OQ01OQ01OQ01`; header
  "What remains" updated). Kernel-verified via `lake env lean` over the freshly
  built parent-chain oleans (Docker untouched; shared Mathlib cache thrashed by
  ~12 concurrent agents → retried until a clean window).
- this knowledge.md.

### Next Steps (the ONLY remaining step is combinatorial)
1. Define the concrete CRT order `D : Fin p × Fin q ≃ Fin (p*q)` (compose
   `Fin · ≃ ZMod ·` with `ZMod.chineseRemainder`).
2. Show `(rowOrder p q).trans D.symm = prodCongrLeft τ` over `Fin p × Fin q`, with
   each fibre `τ j` conjugate (via `Fin p ≃ ZMod p`) to `addLeft j * ringMulPerm q̄`;
   then `Equiv.Perm.sign_prodCongrLeft` ⟹ `∏_{j:Fin q} sign(τ j) = (q/p)^q = (q/p)`
   (odd power of a ±1 Legendre symbol). Dually for `colOrder` ⟹ `(p/q)`.
3. Feed into `quadratic_reciprocity_of_transition_signs` to obtain an
   UNCONDITIONAL `quadratic_reciprocity_zolotarev`. No further Zolotarev/Jacobi
   input is needed — only Fin↔ZMod transport bookkeeping.

## Session 2026-06-23 (researcher-9, S7) — q-fold sign collapse lemma PROVED

**Mode**: REVISIT (continuing the assembly skeleton thread)
**Outcome**: progress — the "`sign_prodCongrLeft` collapses the `q`-fold product"
step (Next-Step #2's second half) is now a kernel-verified lemma (0 sorry, axioms
`[propext, Classical.choice, Quot.sound]`). File now 627L, builds clean.

### What I Did
- Added `sign_prodCongrLeft_affineLine {p q}[Fact p.Prime][NeZero q] (p≠2)(Odd q)
  (a:(ZMod p)ˣ)(β:ZMod q→ZMod p)(A)(A≡a) :
  (sign (Equiv.prodCongrLeft (fun k => addLeft (β k) * ringMulPerm a)) : ℤ)
    = legendreSym p A`.
  This is the abstract collapse: a permutation of `ZMod p × ZMod q` that is
  *fiberwise* (over the `ZMod q` factor) the affine line `x ↦ a·x + β k` on `ZMod p`
  has total sign equal to the single per-line Legendre symbol `(A/p)`.
- Proof (≈10 lines): `Equiv.Perm.sign_prodCongrLeft` ⟹ `∏_{k:ZMod q} sign(fiber k)`;
  every fiber sign collapses to `sign (ringMulPerm a)` by the S6 translation-parity
  corollary `sign_addLeft_mul` (so the `β k` are irrelevant); `Finset.prod_const`
  + `Finset.card_univ` + `ZMod.card q` ⟹ `sign(ringMulPerm a) ^ q`; odd-power
  collapse `ZolotarevCRT.units_pow_odd _ hq` ⟹ `sign(ringMulPerm a)`; cast to ℤ
  and apply the `b=0` instance of S6's `sign_affineLine_eq_legendreSym`.

### Key Findings
- Mathlib's fiberwise-permutation sign lemmas are `Equiv.Perm.sign_prodCongrRight`
  / `sign_prodCongrLeft` (`GroupTheory/Perm/Sign.lean`), each `= ∏ k, sign (σ k)`.
  The underlying equiv is `Equiv.prodCongrLeft (e : α₁ → β₁ ≃ β₂) : β₁×α₁ ≃ β₂×α₁`
  (fibers indexed by the **second** factor, acting on the **first**) — matches the
  `ZMod p × ZMod q` array with per-column (j∈ZMod q) action on rows (i∈ZMod p).
- The collapse needs nothing about the individual `β k`: translation-parity makes
  every fiber sign identical (`= sign (ringMulPerm a)`), so the product is a pure
  `q`-th power, killed by `units_pow_odd` since `q` is odd. The Legendre symbol's
  being ±1 is never invoked explicitly — the unit-group exponent-2 argument suffices.
- `ZMod.card` lives in `Data/ZMod/Defs.lean` (`Fintype.card (ZMod n) = n`), needs the
  `[NeZero n]`→`Fintype (ZMod n)` instance.

### Files Modified
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
  (588L→627L; new lemma + `#check`). Kernel-verified via `lake env lean` over the
  prebuilt parent-chain oleans; `#print axioms` = `[propext, Classical.choice,
  Quot.sound]` (no `sorryAx`, no `ofReduceBool`).
- this knowledge.md.

### Next Steps (single remaining gap, purely combinatorial)
1. Define the concrete CRT order `D : Fin p × Fin q ≃ Fin (p*q)`.
2. The ONLY thing left: show `(rowOrder p q).trans D.symm`, transported across
   `Fin p × Fin q ≃ ZMod p × ZMod q`, **equals** `Equiv.prodCongrLeft (fun j =>
   addLeft (βⱼ) * ringMulPerm q̄)` for the appropriate per-column translations `βⱼ`
   and multiplier `q̄ = (q : ZMod p)ˣ`. Then `sign_prodCongrLeft_affineLine` gives
   `(q/p)` directly; dually `colOrder` ⟹ `(p/q)`; feed both into
   `quadratic_reciprocity_of_transition_signs` for the UNCONDITIONAL law.
   Both the per-line sign (S6) and the q-fold collapse (S7) are now done — the
   remaining work is *only* the Fin↔ZMod transport + the CRT structure identity.
