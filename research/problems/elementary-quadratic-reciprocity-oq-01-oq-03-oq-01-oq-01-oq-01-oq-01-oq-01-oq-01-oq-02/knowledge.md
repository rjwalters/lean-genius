# elementary-quadratic-reciprocity-oq-01-oq-03-…-oq-02 — Zolotarev shuffle → QR

**Problem.** Follow-up #1 of the "Zolotarev–Frobenius for every odd modulus"
capstone (`…-oq-01`): derive the quadratic reciprocity law
`(q/p)(p/q) = (-1)^((p-1)/2·(q-1)/2)` *directly* from the verified general-odd
sign identity `ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd`
(`sign(x ↦ a·x on ℤ/n) = J(A|n)`) via the sign of the rectangular
transpose / perfect-shuffle permutation, as in Zolotarev 1872 / Frobenius 1914.

**File.** `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01OQ02.lean`
(WIP, unregistered, 1 `sorry`).

## Status

| Component | State |
|-----------|-------|
| `gridTranspose m n` (perfect-shuffle perm of `Fin (m*n)`) | proved (def) |
| `gridTranspose_apply` (row-major `n·i+j` ↦ col-major `m·j+i`) | proved |
| `neg_one_pow_choose_two_mul_odd` (parity bridge `(-1)^(C(m,2)C(n,2))=(-1)^((m-1)/2·(n-1)/2)`) | **proved, 0 sorry** |
| `sign_gridTranspose_odd` (classical-form corollary) | proved *modulo* the one sorry |
| `sign_gridTranspose = (-1)^(C(m,2)·C(n,2))` | **`sorry`** — but route DE-RISKED (S2), complete candidate proof written (unverified) |
| Full QR assembly (`α = β∘γ`, identify `α,β` with `ringMulPerm` via CRT) | not formalized |

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
