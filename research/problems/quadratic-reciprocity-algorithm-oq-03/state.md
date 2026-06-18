# Research State: quadratic-reciprocity-algorithm-oq-03

## Current State
**Phase**: ACT — M1 + headline MERGED (0 sorry/0 axiom). M2 now in Lean: parity reduction + assembly VERIFIED; single isolated sorry = the grid-transpose inversion count.
**Path**: full
**Since**: 2026-06-16 (S20 — M2 file built green, one isolated sorry)
**Iteration**: 23

## Session 23 (2026-06-17, researcher-8) — both backends re-confirmed down; **entire `sign` product API ruled out** for the lone sorry
No verifiable discharge possible this session; **both backends down for `sign_gridTranspose_eq_choose`**:
- **Aristotle**: `prove` live-probed **404 "Resource not found"** (single-lemma async submit with the
  pinned `signAux/finPairsLT` hint) — continues the S10–S22 blackout, unchanged.
- **Docker**: daemon **up** but **8 `lean-build` containers running, host load avg 25.6** on the VM —
  far over the ≤2-container good-citizen threshold (OOM risk). No build started (would starve ~6 peers).
  (NB: this worktree's `proofs/.lake` is a symlink to the **main** repo `.lake`, not circular this
  time — but still no local mathlib `.lean` under `packages/`, so audits use the standalone checkout.)

**Genuinely-new audit result (beyond S18/S22):** walked the *complete* `Equiv.Perm.sign` product API at
the pin (`Mathlib/GroupTheory/Perm/Sign.lean`, rev `2df2f0150c`) and **explicitly ruled out every
block-permutation sign lemma** as inapplicable to the coordinate-swap grid-transpose shuffle:
- `sign_prodCongrRight` (Sign.lean:535) `= ∏ k, sign (σ k)` and `sign_prodCongrLeft` (:545) — these are
  **fibre-wise block** perms `(a,b) ↦ (a, σ a b)`; gridTranspose mixes both coordinates → N/A.
- `sign_prodExtendRight` (:528), `sign_sumCongr` (:555) `= sign σa * sign σb`, `sign_subtypeCongr` (:571)
  — all **block-diagonal / disjoint-support**; gridTranspose has no such block structure → N/A.
- `sign_permCongr` (:551), `sign_eq_sign_of_equiv` (:467) — only **transport** sign across a conjugating
  equiv; conjugating gridTranspose by `finProdFinEquiv` yields the map
  `(i,j) ↦ decode_rowmajor(encode_colmajor(j,i))` on `Fin p × Fin q` — **still the inversion shuffle**,
  not `prodComm` (the two encodings differ), so the conjugate is no easier. Confirmed not a one-liner.
**Conclusion (hardened):** the ONLY honest closed-form path remains the low-level inversion count
`sign = signAux3 _ mem_univ = ∏_{finPairsLT(pq)} (±1)` (Sign.lean:174,357) reduced via
`signAux_eq_signAux2` (:290) + a `card_bij` identifying inversions with {row-pairs i<i′}×{col-pairs
j>j′} ⟹ `C(p,2)·C(q,2)`. ~100 LOC of delicate Lean — **must be build-verified, not blind-written**
(file + role + S18–S22 all warn). **Next live-backend session:** Aristotle non-404 one-shot, OR Docker
≤2 containers → build-iterate the `card_bij` route. Claim released no-churn; headline M2 still open.

## Session 22 (2026-06-17, researcher-11) — offline-mathlib bearer audit for the lone sorry (closes the S21 source gap)
Backends still down for a verified discharge (Aristotle `prove` live-probed **404 "Resource not
found"**; this worktree's `proofs/.lake` is a **circular self-symlink** → 0 oleans, no safe build).
But the S21 blocker — *"no local Mathlib source to check the `signAux=∏finPairsLT → card_bij` route"* —
is now **resolved**: the standalone checkout `/Users/rwalters/GitHub/mathlib4` is at the exact build
pin (`2df2f0150c` = v4.26.0). Audited it for `sign_gridTranspose_eq_choose` and pinned every bearer
for the inversion-count route at `Mathlib/GroupTheory/Perm/Sign.lean` (build pin):

**Inversion-count route (the only honest closed-form path — confirmed no upstream closed form):**
- `Equiv.Perm.sign` def `= signAux3 f mem_univ` — Sign.lean:357 (general fintype entry point).
- `Equiv.Perm.signAux {n} (a : Perm (Fin n)) : ℤˣ := ∏ x ∈ finPairsLT n, if a x.1 ≤ a x.2 then -1 else 1`
  — Sign.lean:174 — **this is the inversion product** the `card_bij` plan targets.
- `Equiv.Perm.finPairsLT n` — Sign.lean:165; `mem_finPairsLT : a ∈ finPairsLT n ↔ a.2 < a.1` — Sign.lean:168.
- `Equiv.Perm.signBijAux` — Sign.lean:184 (the perm action on ordered pairs used by `card_bij`).
- **GAP found (key audit result):** there is **no public lemma `sign (f : Perm (Fin n)) = signAux f`**
  at the pin. The reduction must be reconstructed via `signAux3 → signAux2` (`signAux_eq_signAux2`,
  Sign.lean:290) — so the inversion route is workable but **low-level, not a one-liner**. This is the
  concrete reason the lemma is "genuinely new content" beyond a name-discovery gap.

**Conjugation/assembly bearers (already used by the VERIFIED parts of the M2 file):**
- `sign_eq_sign_of_equiv (f : Perm α)(g : Perm β)(e : α ≃ β)(∀ x, e (f x) = g (e x)) : sign f = sign g` — Sign.lean:467.
- `sign_permCongr (e : α ≃ β)(p : Perm α) : sign (e.permCongr p) = sign p` — Sign.lean:551; `sign_symm_trans_trans` — Sign.lean:402.

**Alternative route (possibly the better Aristotle target):** factor `gridTranspose` into transpositions
and use `sign_prod_list_swap {l}(∀ g ∈ l, IsSwap g) : sign l.prod = (-1)^l.length` — Sign.lean:~411.
Discharges to controlling the *count* `l.length ≡ C(p,2)·C(q,2) [2]` rather than a raw inversion bijection.

**Negative results pinned (de-risk: nothing slicker exists at pin):** Mathlib has **no** commutation /
Kronecker-swap matrix (`kroneckerComm` absent; only CategoryTheory `commShift`, irrelevant), **no**
`finProdFinEquiv` sign lemma, and **no** closed-form sign for any p×q transpose/shuffle. Confirms S8/S18.

No Lean written (role + file both warn against blind-writing this finicky lemma, and no build is
available to verify). **Next live-backend session:** submit `sign_gridTranspose_eq_choose` to Aristotle
(non-404) with the pinned bearers, or build-iterate the `card_bij`-over-`finPairsLT` route (Sign.lean:174
+ 184) under Docker (≤2 containers). Claim released; headline M2 still open.

## Session 21 (2026-06-16, researcher-7) — backend re-probe; no safe path to the lone sorry this session
Re-confirmed the M2 status is unchanged: the sole remaining obligation is `sign_gridTranspose_eq_choose`
(inversion count `C(p,2)·C(q,2)`), with the four surrounding pieces (`choose_two_mod_two`,
`neg_one_units_pow_mod_two`, `neg_one_pow_choose_two`, assembly `sign_gridTranspose`) all VERIFIED at
S20 and **unchanged on current main** since. Backend reality this session:
- **Aristotle**: `prove` live-probed **404 ("Resource not found")** twice — the designated single-lemma
  tool for this exact sorry is down (matches S10–S20).
- **Docker**: daemon up but **heavily contended** (~19 `lean-build` containers, ~6 concurrent agent
  builds on the host). A scaffold re-verify build was started but ran >30 min under contention with no
  result; **stopped to relieve the host** (good-citizen ≤2-container guidance) rather than starve peers.
- **No local Mathlib source** in the worktree (`proofs/.lake/packages/mathlib` ships oleans only, 0
  `.lean`), so lemma names for the `signAux=∏finPairsLT` → `card_bij` route cannot be cheaply checked —
  blind-write under a 7.5-min/iter contended host is not justified (and the file/role both warn against
  blind-writing this finicky permutation-sign lemma).
- **Active competing claim**: researcher-22283 holds an active claim on this same problem (no PR/branch
  output yet) — another reason not to burn the contended host racing the same hard lemma.
No Lean written, no result fabricated. **Next live-backend session** (Aristotle non-404 OR Docker ≤2
containers): submit `sign_gridTranspose_eq_choose` to Aristotle as a one-shot, or discharge via the S20
`card_bij` plan (inversions ↔ {row-pairs i<i′}×{col-pairs j>j′}, exactly one inversion per 2-rows×2-cols
choice ⟹ `C(p,2)·C(q,2)`).

## Session 20 (2026-06-16, researcher-8) — M2 materialized; parity reduction VERIFIED, one isolated sorry
Aristotle `prove` still 404 (live-probed). Docker drained 7→2 containers → built
`Proofs.QuadraticReciprocityAlgorithmOQ03M2` GREEN (`[7743/7743]`, 453s, exit 0; only warning = the
intended sorry). New UNREGISTERED file splits `sign_gridTranspose` into: `gridTranspose` (def),
`choose_two_mod_two` + `neg_one_units_pow_mod_two` + `neg_one_pow_choose_two` (all VERIFIED parity
reduction), `sign_gridTranspose_eq_choose` (THE one sorry = inversion count `C(p,2)·C(q,2)`), and
`sign_gridTranspose` (VERIFIED assembly). Supersedes CONFLICTING scaffold PR #24990. Gotcha pinned:
Mathlib's `neg_one_pow_eq_pow_mod_two` needs `[Ring R]` (ℤˣ is not a ring) — used `neg_one_sq` route.
**Next**: discharge `sign_gridTranspose_eq_choose` via `card_bij` over `finPairsLT` (inversions ↔
{rows i<i′}×{cols j>j′}), or submit to Aristotle when non-404. See knowledge.md S20.

## Session 18 (2026-06-16, researcher-1) — M2 bearer re-audit; both backends down for the safe path
Aristotle `prove` still 404 (live-probed); Docker at 4 `lean-build` containers (over the ≤2 safety
threshold on a 7.65 GiB VM) — no build attempted (OOM risk). Merged spine confirmed intact on
`origin/main` (5 theorems, 0 sorry / 0 axiom). **New:** re-audited Mathlib @ pin — **no commutation/
transpose permutation-sign bearer exists** (Kronecker.lean has the matrix, not the sign), and the
`prodCongr`/`sumCongr` sign family is block-diagonal-only, so it does NOT apply to the coordinate-swap
transpose. The S8 inversion route (`inv(σ)=C(p,2)·C(q,2)` via `signAux=∏finPairsLT`, transported by
`sign_permCongr` `Sign.lean:551`) is confirmed as the path — no shortcut. See knowledge.md S18.

## Session 16 sync (2026-06-16, researcher-1) — crux + headline are MERGED, not build-pending
The S15 block below is now STALE. **PR #24903 merged 2026-06-16T07:42Z**, landing the S15 crux
and the Zolotarev headline on `main`, both Docker-verified. Repo reality on `main`:

- `proofs/Proofs/QuadraticReciprocityAlgorithmOQ03.lean` — 0 sorry / 0 axiom, registered
  (`Proofs.lean:2776`), gallery meta **verified/original**. Contains all five theorems:
  `isCycle_mulLeft_of_generator`, `sign_mulLeft_generator`, `sign_mulLeft_eq_neg_one_zpow`,
  `primitiveRoot_pow_half_eq_neg_one` (the S15 crux — DISCHARGED, not build-pending), and
  `legendreSym_eq_sign_mulLeft` (the **Zolotarev headline** `legendreSym p a = sign (mulLeft a)`,
  PROVEN — the Euler tie + field/units sign bridge are done, no longer prose/Aristotle-target).
- The old "Next Action: build-verify the S15 crux on branch `research/qra-oq03-crux`" is obsolete:
  the crux compiled and merged. The branch `research/qra-oq03-crux` is superseded.

**Sole remaining Lean work = Milestone 2** (the file docstring also notes "reciprocity from the
grid-transpose permutation sign is not yet in Lean"): formalize the S6-certified grid-transpose
sign lemma `sign(σ)=(-1)^((p-1)/2·(q-1)/2)` (`σ=c∘r⁻¹`, `verify_reciprocity_m2.py`) and assemble it
with the verified Zolotarev signs to recover full QR. Finicky permutation-sign NT — Docker/Aristotle
target, not blind-write. Docker was 5-container-saturated this session, so M2 was not attempted.
Doc-only sync, no machine verification this session.

## Session 15 sync (2026-06-16, researcher-3) — state corrected to match repo reality
Earlier session blocks (S10–S13) and the old "Next Action" below are STALE: they framed M1 as
build-pending and proposed creating a NEW file `QuadraticReciprocityZolotarev.lean`. Repo reality:

- **M1 is VERIFIED and REGISTERED on main.** File `proofs/Proofs/QuadraticReciprocityAlgorithmOQ03.lean`
  (NOT a `...Zolotarev.lean`) holds all three M1 lemmas — `isCycle_mulLeft_of_generator`,
  `sign_mulLeft_generator`, `sign_mulLeft_eq_neg_one_zpow` — 0 sorry / 0 axiom, Docker-green
  (S14, researcher-6), registered at `Proofs.lean:2771`. **Do NOT redo M1 or create a duplicate file.**
- **S15 headline crux is written, build-pending, on branch `research/qra-oq03-crux` (no PR yet):**
  `primitiveRoot_pow_half_eq_neg_one` — for a generator `g` of `(ZMod p)ˣ`, `(g:ZMod p)^((p-1)/2) = -1`
  (Euler tie crux, stated in the field to dodge the units `Neg`-instance question). Never compiled
  (dual blackout: Aristotle 404 live-probed, Docker 7-container saturated + circular `proofs/.lake`
  self-symlink → 0 oleans). Build-verify it the moment Docker is at ≤2 containers and `.lake` is sane.
- **Remaining for the headline `legendreSym p a = sign (mulLeft a)`:** the field/units sign bridge
  to lift the crux + `sign_mulLeft_eq_neg_one_zpow` onto `(ZMod p)ˣ`, assembled with Euler's
  criterion. Finicky NT — submit to Aristotle when non-404 rather than blind-writing.

No machine verification this session (dual blackout reconfirmed live). Doc-only sync.

## Session 13 (2026-06-15, researcher-5) — added arbitrary-element Zolotarev sign lemma (build-pending)
Dual blackout reconfirmed live (`docker info` times out; Aristotle `prove` returns `Resource not
found` on a trivial ping). No machine verification. Added `sign_mulLeft_eq_neg_one_zpow` to the
UNREGISTERED `QuadraticReciprocityAlgorithmOQ03.lean`: for `a = g^k` (g generator, even order),
`sign (mulLeft a) = (-1)^k` — the Zolotarev sign computation for an arbitrary element (the file
previously only handled a generator). Reuses the S12-pinned `map_zpow` + inline `G →* Perm G`
wiring, so no new bearer-name risk. Remaining for the headline `legendreSym p a = sign (mulLeft a)`:
Euler-criterion tie + field/units sign bridge (both still prose in knowledge.md). Problem remains
infrastructure-BLOCKED; first live-backend session should docker-build, repair, register.

## Session 10 (2026-06-15, researcher-3) — M1 producer lemma transcribed to a build-pending Lean file
Dual blackout **reconfirmed live this session**: `docker info` times out (Docker down) and the
Aristotle MCP `prove` tool — now loaded — returns `"Resource not found"` on a submitted M1 snippet
(backend unreachable). So still no machine verification possible.

After 9 sessions of "paste-ready, deferred to first live backend" with the backend never returning,
transcribed S9's fully-pinned, numerically-certified Milestone-1 core into actual Lean:
`proofs/Proofs/QuadraticReciprocityAlgorithmOQ03.lean` (UNREGISTERED, build-pending — not added to
`Proofs.lean` so it cannot break auto-merge). Contents:

- `isCycle_mulLeft_of_generator` — the single producer lemma S9 proved Mathlib lacks (left-mult by a
  generator of a finite group is a single cycle). Discharges the `IsCycle` constructor with witness
  `x = 1`, using `Equiv.mulLeft_zpow` for the `(mulLeft g)^i = mulLeft (g^i)` glue and
  `Subgroup.mem_zpowers_iff` for the SameCycle witness.
- `sign_mulLeft_generator` — corollary: for a generated group of **even** order, `sign (mulLeft g) = -1`
  (support = univ since `mulLeft g` is fixed-point-free; `IsCycle.sign` + even-power collapse).

**Honest status:** UNVERIFIED. Several tactic forms (`Equiv.mulLeft_zpow`, `Subgroup.zpowers_one_eq_bot`,
`Subgroup.card_bot`, the support computation) are pinned-by-reasoning but not compiled; the next
live-backend session should `docker-build` / Aristotle-check and repair. Deliberately scoped to the two
genuinely-new lemmas; the Euler-criterion tie (Zolotarev headline) and M2 grid-sign remain prose in
knowledge.md. Invariants: still 1 parent axiom upstream, this file adds 0 axioms / 0 `sorry`.

## Session 6 (2026-06-14, researcher-2) — Milestone 2 certified, honesty flag discharged
Build-free (Docker down). Added `verify_reciprocity_m2.py` (all asserts pass, 240 odd-prime
pairs). Pinned the M2 reciprocity bridge with verify-before-assert: the **grid-transpose
permutation** `σ=c∘r⁻¹` (`r(i,j)=i·q+j`, `c(i,j)=j·p+i`) has `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`
— a self-contained, M1-independent combinatorial identity — and assembles with the M1 Zolotarev
signs to recover QR. **Refuted** the naive CRT-listing permutation `ρ(k)=(k mod p)·q+(k mod q)`
as the bridge (its sign is neither the reciprocity factor nor the Legendre product). M2 is no

## Session 6 (2026-06-14, researcher-2) — Milestone 2 certified, honesty flag discharged
Build-free (Docker down). Added `verify_reciprocity_m2.py` (all asserts pass, 240 odd-prime
pairs). Pinned the M2 reciprocity bridge with verify-before-assert: the **grid-transpose
permutation** `σ=c∘r⁻¹` (`r(i,j)=i·q+j`, `c(i,j)=j·p+i`) has `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`
— a self-contained, M1-independent combinatorial identity — and assembles with the M1 Zolotarev
signs to recover QR. **Refuted** the naive CRT-listing permutation `ρ(k)=(k mod p)·q+(k mod q)`
as the bridge (its sign is neither the reciprocity factor nor the Legendre product). M2 is no
longer "second proof in name only" — its new content (lemma B) is now explicit and certified.
Next build-free step: pin M2 `Equiv.Perm.sign` bearers to file:line. See knowledge.md.

## Current Focus
Zolotarev's lemma as the formalization spine: `legendreSym p a = Perm.sign (mulLeft a)` on
`ZMod p`. OQ resolved on paper (researcher-8 S1); Milestone-1 statement + key cycle-structure
step numerically verified (researcher-4 S2); committed as a reproducible script
(`verify_zolotarev.py`, researcher-5 S3, asserts all four steps for every odd prime 3≤p<80).
researcher-4 S4 **pinned every M1 Mathlib bearer to an exact `file:line` at the build version**
(v4.26.0, mathlib rev `2df2f01`) and re-confirmed Zolotarev's lemma is still absent upstream — so
M1 is now paste-ready (numerically certified AND name-discovery-free), awaiting only Docker.

## Active Approach
Permutation-sign (Zolotarev) proof. Milestone 1 = the Zolotarev lemma itself (cyclic units +
cycle-sign + Euler's criterion), ~80–120 LOC, oq-01-independent. Milestone 2 (reciprocity) =
the grid-transpose sign lemma (B, `sign(σ)=(-1)^((p-1)/2·(q-1)/2)`, S6-certified) assembled with
M1; the exact statement is now pinned and numerically de-risked (was "gated/assess after M1").

## Attempt Count
- Total attempts: 1 (M1 Docker-built green S14; crux S15 still build-pending)
- Current approach attempts: 1
- Approaches tried: 1 surveyed (Zolotarev direct), 1 deprioritized (algorithm-confluence)

## Blockers
- Dual blackout (reconfirmed live S15): Aristotle `prove` 404; Docker 7-container saturated on an
  8 GB VM + circular `proofs/.lake` self-symlink (0 oleans) — no safe/successful build possible.
- Headline assembly (Euler tie + field/units sign bridge) is finicky NT; Aristotle target, not blind-write.

## Next Action
**M1, the crux, and the Zolotarev headline are all DONE, verified, and merged (#24903) — do not redo them.**
Sole remaining Lean target = **Milestone 2 (full reciprocity)**: formalize the S6-certified
grid-transpose permutation-sign lemma `sign(σ)=(-1)^((p-1)/2·(q-1)/2)` for `σ=c∘r⁻¹`
(`r(i,j)=i·q+j`, `c(i,j)=j·p+i`; oracle `verify_reciprocity_m2.py`, 240 prime pairs), then assemble
it with the verified `legendreSym_eq_sign_mulLeft` Zolotarev signs to recover quadratic reciprocity.
This is finicky permutation-sign number theory — build-iterate under Docker (≤2 containers) or submit
to Aristotle when non-404; do NOT blind-write. The gallery entry is already a complete verified
artifact for the Zolotarev spine; M2 extends it to the full reciprocity statement in Lean.

See knowledge.md (S4 bearer table, S14/S15 notes) for the full survey and the honesty flag on Milestone 2.
