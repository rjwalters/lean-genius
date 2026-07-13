# Current State

> **S27 — order UPPER BOUND corollary added (researcher-6, 2026-07-09).**
> Slug remains COMPLETE/build-verified on main; nothing was broken. Added one
> safe capstone corollary `primitive_solvable_subgroup_card_le`: |H| ≤ p(p-1)
> (numeric-ceiling form of Galois 1832), a two-line `Nat.le_of_dvd` composition
> of the existing `primitive_solvable_subgroup_card_dvd`. Completes the corollary
> trio (dvd / =p·m / ≤). No new sorry/axiom. PR #36901. UNVERIFIED — Docker infra
> down (containerd content-store I/O errors); pattern is verbatim-identical to
> verified uses elsewhere in repo. Released claim.
>
> ---
>

> **S26 — FULL-CHAIN DOCKER BUILD-VERIFIED + redundant Aristotle companion removed (researcher-3, 2026-07-08) — READ FIRST.**
> The problem was re-served as `available` (phantom re-serve of an already-complete
> slug). Confirmed the 5 registered GaloisDirection files match `origin/main`
> (`5749f3a4414`) byte-for-byte and carry **zero proof-term `sorry`, zero `axiom`,
> zero `native_decide`**. Closed the gap S25 left open — completion had rested only
> on PR-review + Aristotle report, never on a local build — by running
> `docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection` here:
> **Build succeeded, 7746 jobs, 0 errors, 0 `sorry` warnings** (LEAN_MEMORY_LIMIT
> 18GB). The whole `primitive_solvable_subgroup_embeds_AGL1Z` chain (Steps 1–5 +
> Step 4 via the `…Step4` module) is genuinely machine-checked. Also deleted the
> now-dead `…GaloisDirectionStep4Aristotle.lean` companion: it was unimported by
> anything, its `normalizer_iso_AGL1Z_companion` was a leftover `sorry`, and the
> obligation is already discharged sorry-free in `…Step4.lean` (used by the main
> file). Removing it drops the last `sorry` string associated with the slug.
> Re-marked the problem **completed** and released the claim. NOTHING ACTIONABLE
> REMAINS.
>
> ---
>
> **S25 — PROBLEM COMPLETE; LAST SORRY DISCHARGED ON `main` (researcher-1, 2026-06-19) — READ FIRST.**
> The GaloisDirection theorem chain is now **`sorry`-free and build-verified on
> `origin/main` (3fa20e27b601)**. The last genuine code `sorry` —
> `normalizer_iso_AGL1Z` (Step 4) — was discharged by **PR #26791**
> ("discharge Step 4 normalizer_iso_AGL1Z (last GaloisDirection sorry)",
> researcher-11), via the build-verified companion
> `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep4`
> (`normalizer_eq_range` + conjugacy transport `σ ∼ τ₀`). All three registered
> files — `…GaloisDirection`, `…Step1`, `…Step4` — carry **zero proof-term
> `sorry`** (every remaining "sorry" string is docstring prose). Steps 1/2/3/5
> and the file-level composition `primitive_solvable_subgroup_embeds_AGL1Z`
> were already `sorry`-free; #26791 closed the frontier **1 → 0**.
>
> **The S24 Aristotle job is RESOLVED, not pending.** Project
> `160cb8f8-3ac1-4a7b-be36-7ad88a3a3cc0` (Step 4 submission) returned
> **COMPLETE / PROVED**: it independently filled `normalizer_iso_AGL1Z_companion`
> in `…Step4Aristotle.lean` and confirmed dependence only on the standard axioms
> `propext`/`Classical.choice`/`Quot.sound` (no `sorry`, no `Lean.ofReduceBool`).
> This is a *second*, independent confirmation of the same result — but it is
> **redundant** since #26791 already landed a working discharge, so there is
> nothing to integrate. Do NOT re-poll 160cb8f8 or reopen Step 4.
>
> **NOTHING ACTIONABLE REMAINS** for the galois-direction sub-problem: it is
> mathematically complete, sorry-free, build-verified, axiom-clean. Build gate
> was CLOSED this session (host load ~16.8, threshold <6) so no independent
> local rebuild was run; completion rests on #26791's verification +
> the Aristotle COMPLETE/PROVED + axiom report. Marked the problem **completed**
> and released the claim.
>
> ---
>
> **S24 — WHOLE THEOREM REDUCED TO ONE SORRY; Step 4 submitted to Aristotle (researcher-1, 2026-06-19) — READ FIRST.**
> Audited the registered `AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`:
> the ONLY genuine code `sorry` is `normalizer_iso_AGL1Z` (line 471, Step 4).
> Steps 1 (`sylow_p_unique` — the once-"circular" socle step, now discharged
> via the abelian-characteristic-subgroup route, `sorry`-free), 2, 3
> (`sylow_p_is_pcycle`), 5 (`H_le_normalizer`), and the file-level composition
> `primitive_solvable_subgroup_embeds_AGL1Z` are ALL `sorry`-free on `main`.
> So discharging Step 4 completes the entire theorem.
>
> Local Docker build gate was CLOSED this session (host load ~12, 3 lean-build
> containers), so the build-pending orphan
> `…GaloisDirectionStep4.lean` (hand-drafted, `sorry`-free, via
> `normalizer_eq_range` + conjugation transport) could not be verified locally.
> Instead submitted Step 4 to **Aristotle** (remote, bypasses the local gate)
> via a clean companion `…GaloisDirectionStep4Aristotle.lean`:
>
>   **Aristotle project_id = 160cb8f8-3ac1-4a7b-be36-7ad88a3a3cc0** (RUNNING)
>
> **NEXT (on wake / build-up):**
>   1. `uvx --from aristotlelib aristotle result 160cb8f8-... --destination FILE.zip`;
>      PROVED ⇒ paste the proof body over `normalizer_iso_AGL1Z`@471 of the
>      registered file (drop the `_companion` suffix), delete the companion +
>      orphan, then `docker-build Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`
>      when the gate opens (load<6, ≤2 containers) and graduate.
>   2. If Aristotle fails: fall back to build-verifying the hand-drafted orphan
>      `…GaloisDirectionStep4.lean` (its `normalizer_eq_range` is the crux), then
>      fold into the registered file.
> Either path closes the last sorry — no new math is needed.

---

> **S23 ACT — STEP 4 FULLY DRAFTED (`normalizer_iso_AGL1Z`, `sorry`-free), build-pending (researcher-2, 2026-06-18) — READ FIRST.**
> Wrote the complete formal discharge of Step 4 in a self-contained orphan file
> `Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep4.lean` (~250 LOC,
> 0 `sorry`/0 `axiom`). Architecture mirrors the numerically-certified plan in
> `verify_step4_normalizer.py`: prove the affine characterization for the
> *standard* translation `τ₀ : x↦x+1` first — `(zpowers τ₀).normalizer =
> (AGL1Z.toPerm p).range` (`normalizer_eq_range`, both inclusions: affine maps
> normalise the translation group, and any normalising `h` satisfies the
> functional equation `h(y+1)=h(y)+k` with `k` a unit, so `h(x)=h(0)+k·x` is
> affine) — giving `isoStd : AGL1Z p ≃* N(⟨τ₀⟩)`; then a generic `p`-cycle `σ`
> is conjugate to `τ₀` (equal cycle type `{p}`), and `MulAut.conj c` transports
> `N(⟨σ⟩) ≃* N(⟨τ₀⟩)` via `Subgroup.map_equiv_normalizer_eq`, composing to
> `φ : N(⟨σ⟩) →* AGL1Z p` injective + surjective — exactly the registered
> `…GaloisDirection.lean:425` stub signature.
>
> **NOT yet build-verified.** A Docker build this session compiled the parent
> `.olean` and reached `lean … Step4.lean` elaboration with NO errors, but the
> host was badly oversaturated (~18 concurrent build containers, load ~13; lean
> accrued only ~40 s CPU in 25 min) and the 60-min cap fired before green; the
> Docker daemon then hard-faulted (`input/output error` on the containerd blob
> store — even trivial `docker run` fails). Kept the file an UNREGISTERED orphan
> (absent from `Proofs.lean`, registered `sorry` left intact) so the gated build
> is untouched — same staging Steps 1/3 used before folding.
>
> **NEXT (build-capable session):** `docker-build.sh
> Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep4`; once green,
> register in `Proofs.lean` + replace the `…GaloisDirection.lean:429` `sorry`
> with `exact …GaloisDirectionStep4.normalizer_iso_AGL1Z σ _hσ _hσ_card`,
> dropping the sorry frontier **2 → 1** (only Step 1 `sylow_p_unique` remains).
>
> **S22 ACT — MAIN ASSEMBLY DISCHARGED, Docker-verified GREEN (researcher-11, 2026-06-18) — READ FIRST.**
> Wired up the file-level theorem `primitive_solvable_subgroup_embeds_AGL1Z` as the
> pure composition of the five step lemmas (pick a Sylow `P` from `Nonempty (Sylow p ↥H)`;
> Step 2 normality; extract the `p`-cycle `σ` + data from Step 3; `H ≤ N(⟨σ⟩)` from
> Step 5; injective `ψ : N(⟨σ⟩) →* AGL(1,p)` from Step 4; embedding `= ψ ∘ inclusion`,
> injective via `Subgroup.inclusion_injective`). The assembly body carries **no `sorry`
> of its own** — rebuilt `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`
> → **Build completed successfully (7745 jobs)**, 0 axioms. **Sorry frontier 3 → 2**:
> ONLY Step 1 `sylow_p_unique` (L121) and Step 4 `normalizer_iso_AGL1Z` (L272) remain;
> the whole classification now closes automatically once those two land. Next: Step 4
> (numerically certified, ~80–150 LOC) or Step 1 (hardest, ~70–110 LOC).
>
> **S21 ACT — STEP 3 DISCHARGED, Docker-verified GREEN (researcher-11, 2026-06-18) — READ FIRST.**
> Built the turnkey Step3 orphan in isolation; it surfaced 2 real elaboration bugs
> (`Nat.pow_le_pow_right` wants `0 < p` not `0 ≤ p`; `MulAction.orbit_eq_univ` takes the
> acting group as an explicit arg). Fixed both, **folded the corrected proof + the
> `padicValNat_factorial_self` helper into the registered file** (now `import Mathlib`),
> deleted the redundant orphan, and rebuilt `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`
> → **Build completed successfully (7745 jobs)**. **Sorry frontier 4 → 3**: Step 1
> `sylow_p_unique`, Step 4 `normalizer_iso_AGL1Z`, main remain; **Steps 2, 3, 5 now proved**,
> 0 axioms. Next: Step 1 (hardest, ~70–110 LOC; Lemma A already drafted in the Step1 orphan —
> remaining Lemma B/C + Sylow transport), then Step 4, then the main glue. Stale PR #25110
> ("not yet green") is superseded by the fold. Full record:
> `sessions/2026-06-18-s21-act-fold-step3-green.md`.
>
> **S18 MAIN-ASSEMBLY DRAFT + Step-3 `σ∈H` export (researcher-1, 2026-06-16) — READ FIRST.**
> Dual blackout STILL on (re-probed live this cycle: `docker run --rm alpine
> echo` hangs >25s, exit 124; Aristotle MCP `prove` → 404 "Resource not
> found"). No verifiable build possible. Made three build-SAFE changes:
> 1. **Registered file** (`…GaloisDirection.lean`): strengthened the Step-3 stub
>    `sylow_p_is_pcycle` conclusion with a 4th conjunct `∧ σ ∈ H` (still
>    `sorry`; statement is well-typed and has NO callers in the gated build, so
>    the green 1900-job build is unaffected — `sorry` proves any well-formed
>    Prop). Frontier still **4 sorries** (Steps 1/3/4 + main).
> 2. **Step-3 orphan** (`…GaloisDirectionStep3.lean`): proved the new `σ ∈ H`
>    conjunct (FREE: `σ = ι a = ↑((P:Subgroup H).subtype a)`, `SetLike.coe_mem`).
> 3. **NEW main-assembly orphan** (`…GaloisDirectionMainAssembly.lean`): drafts
>    the end-to-end composition `sylow_p_unique → sylow_p_normal →
>    sylow_p_is_pcycle → H_le_normalizer → normalizer_iso_AGL1Z`, then
>    `H ↪ N(⟨σ⟩) →* AGL(1,p)`. Introduces **no new sorry** — bottoms out only in
>    the existing step lemmas. This is the file-level glue that was never written
>    in Lean (S12's capstone python cert checked the math, not the Lean
>    signatures). **Key gap it resolves:** Step 5 needs `hσH : σ ∈ H`, which
>    Step 3's old output did NOT supply (would have cost ~25 LOC of `ι(P)=⟨σ⟩`
>    cardinality re-derivation in the assembly); exporting `σ∈H` from Step 3
>    threads it straight through. **Next Docker-up session:** build the two
>    orphans; if green, fold Step-3 orphan body into the registered Step-3 stub
>    AND fold the main-assembly body into the registered main theorem (drops the
>    main `sorry`, leaving exactly Steps 1/3/4). Orphans are OUTSIDE `Proofs.lean`
>    (verified) — zero gallery-build risk. Claim released.
>
> **S16 TURNKEY-DRAFT (researcher-5, 2026-06-16) — READ FIRST.**
> Dual blackout persists (re-probed live): Aristotle `prove` 404; host
> `proofs/.lake` is the self-referential symlink, so Mathlib oleans are
> inaccessible host-wide and `docker-build.sh` would force a multi-GB
> Mathlib re-clone (git-128) — local build UNAVAILABLE. No `.lean` change to
> the registered (GREEN, 4-sorry) file. **Produced a turnkey ORPHAN companion**
> `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep3.lean`
> (NOT in `Proofs.lean`, outside the build gate) that discharges Step 3
> `sylow_p_is_pcycle` — UNVERIFIED, fold into the registered stub after one
> green build. Reduces Step 3 to the single number-theory lemma
> `(p!).factorization p = 1` (proved in-file as `padicValNat_factorial_self`).
> **KEY:** that same fact is the kernel of Step 1's hardest sub-step too —
> extract a shared `Nat.card ↥P = p` lemma to collapse both. Full discharge
> plan + lemma-name confidence table in knowledge.md §"S15 Step-3 discharge
> plan". Frontier unchanged: 4 sorries (Steps 1/3/4 + main). Claim released.
>
> **DOCKER-REGRESSION RE-PROBE (researcher-1, 2026-06-16, S15) — READ FIRST.**
> The S14 record below says "Docker recovered this session." That is now STALE:
> Docker has regressed to DOWN. Re-probed live this cycle — `docker run --rm
> alpine echo` times out (exit 124, hung daemon); Aristotle MCP `prove` still
> returns "Resource not found" (404). **DUAL BLACKOUT.** Frontier re-confirmed
> unchanged from S14: registered file is GREEN with **4 `sorry` stubs** — Step 1
> `sylow_p_unique` (line 100, the true blocker, ~70–110 LOC), Step 3
> `sylow_p_is_pcycle` (line 130), Step 4 `normalizer_iso_AGL1Z` (line 155), and
> the main theorem (line 316). Step 5 `H_le_normalizer` remains discharged. All
> remaining discharge is build-gated; no verifiable progress is possible without
> a build backend. No `.lean` change this cycle (blind-writing into the green
> file is unverifiable and risks the 1900-job build). Claim released.
>
> **STATE-SYNC (researcher-9, 2026-06-15) — this file was frozen at S12; main has
> merged two later PRs that the header below does NOT reflect. Read this first.**
>
> - **S13 / #24699 (merged 2026-06-15 18:09Z) — file is Docker-VERIFIED GREEN, NOT
>   "build-pending".** S13 threaded `_hσ_cycle : σ.IsCycle` into `H_le_normalizer`
>   (needed because the discharge plan uses `orderOf σ = p` via `IsCycle.orderOf`;
>   `#support = p` alone is insufficient for a non-cycle). `docker-build.sh
>   Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection` → **Build completed
>   successfully (1900 jobs), 5 `sorry` warnings**. The S12 header's "Docker times
>   out / build-pending" framing is STALE — the registered file compiles. S13 also
>   rewrote the Step-5 docstring with the corrected 5-item discharge plan
>   (orderOf→Sylow card via Legendre `padicValNat p p! = 1`→`ι(P)=⟨σ⟩` by card→
>   normality transport→`Subgroup.le_normalizer_of_normal_subgroupOf`).
> - **R4 / #24634 (merged 2026-06-15 18:27Z) — Step-4 char-in-normal is a 0-LOC
>   instance, and the enabling import is now in the file.** An S15 "Correction 2"
>   (not in this state.md) wrongly claimed `normal_of_characteristic_of_normal` is
>   absent in v4.26.0; R4 rescinded it — the lemma is
>   `ConjAct.normal_of_characteristic_of_normal` (`Mathlib/GroupTheory/GroupAction/
>   ConjAct.lean:260`, an `instance`, so the `ConjAct.` prefix is irrelevant to TC
>   resolution). R4 added `import Mathlib.GroupTheory.GroupAction.ConjAct` + fixed
>   two `Subgroup.…`→`ConjAct.…` references, so the cited instance is now in scope.
> - **S14 / 2026-06-16 (researcher-4) — Step 5 `H_le_normalizer` is now DISCHARGED.**
>   Docker recovered; built the Step5 companion proof GREEN (1901 jobs), folded the
>   verified body into the registered `H_le_normalizer`, rebuilt the registered file
>   GREEN (1900 jobs). **Frontier is now 4 `sorry` stubs** (Steps 1, 3, 4 + main).
>   The redundant standalone Step5 companion file was deleted. **Cheapest next ACT:**
>   Step 4 (0-LOC instance, import in scope), then Step 3, then Step 1 (~70–110 LOC,
>   the true blocker). Aristotle MCP `prove` still 404 (live-probed 2026-06-16).

**Phase**: S14 ACT (Step 5 `H_le_normalizer` **DISCHARGED** — verified body folded into the registered file; Docker-verified GREEN, 1900 jobs, sorry count **5 → 4**. Redundant Step5 companion deleted. Remaining: Steps 1/3/4 + main. Aristotle 404; Docker recovered this session.)
**Since**: 2026-06-16 (S14 ACT Step-5 discharge + Docker verify; was 2026-06-15 S12/S13 ACT)
**Iteration**: 14 (S1 scaffold merged via #22031 on 2026-06-02; S2 ORIENT 2026-06-04; S3 STATE-SYNC 2026-06-10; S4 ACT 2026-06-12; S5 OBSERVE 2026-06-13; S6 ORIENT 2026-06-14; S7 ORIENT 2026-06-14; S8 ORIENT 2026-06-14; S9 ORIENT 2026-06-14; S10 ORIENT 2026-06-14; S11 ACT-prep 2026-06-14; S12 ACT 2026-06-15; S13 ACT 2026-06-15; S14 ACT this iteration)
**Owner**: researcher-4 (S14 ACT, 2026-06-16); prior researcher-4 (S12/S13 ACT), researcher-2 (S11 ACT-prep), researcher-7 (S10 ORIENT), researcher-5 (S9 ORIENT), researcher-2 (S8 ORIENT), researcher-3 (S7 ORIENT), researcher-1 (S6 ORIENT), researcher-5 (S5 OBSERVE), researcher-2 (S4 ACT), researcher-1 (S1–S3)

## Iteration 14 (researcher-4, 2026-06-16) — S14 ACT: Step 5 discharged, Docker-verified, folded into registered file

**Outcome**: real verified progress. Docker recovered (1 container, warm cache).
Built the Step5 companion (`H_le_normalizer_decomposed`) → GREEN 1901 jobs, body
sorry-free/axiom-free — confirming the prior session's *premature* "Docker-verified"
docstring claim was in fact correct. Folded the verified body into the registered
`H_le_normalizer` (signatures matched), rebuilt the registered file → GREEN 1900
jobs, **sorry 5 → 4** (line 237 stub eliminated). Deleted the redundant companion.
Remaining stubs: Step 1 `sylow_p_unique` (~70–110 LOC, the true blocker), Step 3
`sylow_p_is_pcycle`, Step 4 `normalizer_iso_AGL1Z`, main theorem. See knowledge.md
for the realised proof route. Aristotle `prove` 404 (live-probed).

## Iteration 12 (researcher-4, 2026-06-15) — S12 ACT: replace Step 5's UNSOUND signature with the sound corrected form

**Outcome**: progress / correctness fix to the REGISTERED `.lean` file (no
build — Docker daemon times out, Aristotle MCP returns "Resource not found",
both re-tested live this session). For 6 sessions (S5–S11) the file carried
`H_le_normalizer` with the **mathematically false** signature
`(H) (_hPrim) (_hSolv) (σ) (_hσ_in_H : σ ∈ H) ⊢ H ≤ (zpowers σ).normalizer`
— flagged unsound at S5 OBSERVE (counterexample p=5: `σ = x↦2x`, `h = x↦x+1`,
`hσh⁻¹ ∉ ⟨σ⟩`), every later session deferring the fix to "a Docker-up session".
The fix needs no build: it is a signature + docstring edit.

**What I did.** Replaced the signature with the documented SOUND corrected
form, threading the normal Sylow-p `P`, the generator inclusion `hgen`
(the exact output of Step 3 `sylow_p_is_pcycle`), and the `p`-cycle data
`hσ_card`:

```lean
theorem H_le_normalizer
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (P : Sylow p H)
    (_hPnorm : (P : Subgroup H).Normal)
    (σ : Equiv.Perm (ZMod p))
    (_hσ_card : σ.support.card = p)
    (_hgen : ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈
      Subgroup.zpowers σ)
    (_hσH : σ ∈ H) :
    H ≤ (Subgroup.zpowers σ).normalizer := by
  sorry
```

The docstring was rewritten: the S5 counterexample is preserved (as the
rationale for why the OLD signature was wrong) and the "DO NOT DISCHARGE AS
WRITTEN" warning is replaced by a note that the signature is now the sound
corrected form, body pending a backend-up discharge.

**Why this is safe under no-build.** Every subterm of the corrected
signature already appears verbatim in the currently-building file:
`(P : Sylow p H)` and `(P : Subgroup H).Normal` from Step 2
(`sylow_p_normal`), and the `hgen` expression + `σ.support.card = p` from
Step 3 (`sylow_p_is_pcycle`). So the new signature typechecks. No other
declaration references `H_le_normalizer` (the main theorem is its own
independent `sorry`), so the change is isolated.

**Why the body stays `sorry`.** A blind tactic discharge (the planned
hPnorm-conjugation + `ι(P)=⟨σ⟩` cardinality upgrade + `Subgroup.le_normalizer`,
~5–15 LOC) cannot be build- or solver-verified under the dual blackout, and
getting the normalizer/`Subgroup.map`/cardinality API exactly right blind
would risk breaking the registered gallery build. The statement is
numerically certified sound by `verify_step5_normalizer.py` (S9) for all odd
primes `3 ≤ p ≤ 29`; discharging it is the cheapest next ACT once a backend
returns.

**Net effect.** The registered file moves from "contains a FALSE lemma stub
(a soundness landmine — a future assembler could cite it, or an accidental
`sorry`-free 'proof' could slip through)" to "contains only TRUE `sorry`
stubs". 5 sorries unchanged; build-pending but low-risk.

### Files touched

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean` —
  Step 5 signature + docstring (only the `H_le_normalizer` declaration).
- `research/problems/.../state.md` — this block + header.
- `research/problems/.../knowledge.md` — Risk R2 status note.
- `src/data/research/problems/...json` — `currentState`, `completedThisIter`,
  `open`, top-level `phase`.

## Iteration 11 (researcher-2, 2026-06-14) — S11 ACT-prep: Step 4 isomorphism numerically certified (surjective half)

**Outcome**: ACT-prep / durable verify (no build — Docker DOWN, Aristotle
`prove` returns "Resource not found"; both backends still in blackout).
`verify_step4_normalizer.py` added beside `knowledge.md`; in-source
`normalizer_iso_AGL1Z` docstring gains a cert pointer; `knowledge.md` gains a
Step-4-cert section. **0 Lean proof changes, 5 sorries intact.**

**What I did.** The S7 `verify_step5_normalizer.py` certified only the EASY
inclusion `AGL image ⊆ N_{S_p}(⟨σ⟩)` (every affine map normalises the
translation subgroup). It never certified Step 4's `normalizer_iso_AGL1Z`,
whose `φ` must be **surjective** — i.e. the normalizer contains NOTHING beyond
the affine maps, `|N| = p(p−1)` exactly. I brute-forced the full `S_p` for
p∈{3,5,7} with `σ = (x↦x+1)` and confirmed: (A) `N_{S_p}(⟨σ⟩)` equals exactly
the affine image (set equality both directions) ⟹ φ injective AND surjective;
(B) `|N|=p(p−1)`, `n_p=|S_p|/|N|=(p−2)!≡1 [MOD p]` (Sylow III); (C) the
recovered map `h↦(a,u)` is multiplicative ⟹ a group hom, not just a bijection.

**Net effect.** Step 4 (the structural core of the embedding) is now certified
sound in both iso directions on a finite model before a Docker-up ACT discharges
its ~80–150 LOC. The harder surjective half is no longer merely asserted.

## Iteration 10 (researcher-7, 2026-06-14) — S10 ORIENT: char-in-normal bridge bearer FOUND (corrects S8)

**Outcome**: ORIENT/knowledge (no build — Docker DOWN, Aristotle `prove`
returns "Resource not found"; both backends in blackout). Doc-only: the
in-source Step 1 docstring + `knowledge.md` R4 were corrected; **0 Lean proof
changes, 5 sorries intact**.

**What I did.** S8 named the "char-in-char composition" (`Q` char in `↥A`,
`A` char in `↥H` ⟹ `Q.map A.subtype` normal in `↥H`) as Step 1's *single
hardest residual* — "no direct bearer", budget ~10–30 LOC for an ad-hoc bridge,
with an abelian-primary-component reroute offered as fallback. That verdict is
**wrong**. The step needs only `Q.map A.subtype` **normal** (not characteristic)
in `↥H`, and Mathlib supplies exactly that as an *instance*:

`Subgroup.normal_of_characteristic_of_normal`
(`Mathlib/GroupTheory/GroupAction/ConjAct.lean:260`, namespace `ConjAct`):
`{H : Subgroup G} [H.Normal] {K : Subgroup H} [K.Characteristic] :`
`(K.map H.subtype).Normal`

Verified present at the exact lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0) via `gh api .../contents/Mathlib/GroupTheory/GroupAction/ConjAct.lean?ref=<pin>`
(file is 293 lines; instance at 260; `gh search code` also surfaced it). Being
an `instance`, it fires by typeclass resolution — instantiate `G := ↥H`,
lemma-`H := A` (= abelian, characteristic ⟹ normal `derivedSeries ↥H (d-1)`),
lemma-`K := Q` (Sylow-p of `↥A`, characteristic via `Sylow.characteristic_of_normal`),
and `(Q.map A.subtype).Normal` holds with **0 LOC**.

**Net effect.** Step 1's hardest sub-step collapses from "build a bridge" to
"the instance is already there". The abelian-primary-component reroute is
unnecessary. Step 1 wiring budget revised ~100–150 → ~70–110 LOC; Risk R4 stays
MEDIUM, now dominated by the `v_p(|H|)=1` Legendre arithmetic + `Sylow.ofCard`
transport rather than a missing-infrastructure concern. No new soundness defect.

## Iteration 9 (researcher-5, 2026-06-14) — S9 ORIENT: numerical certification of the corrected Step 5

**Outcome**: ORIENT/knowledge (no build — Docker DOWN). Complements the
Step-1-focused S6/S7/S8 by de-risking the *other* recommended cheap ACT — fixing
Step 5. Committed `verify_step5_normalizer.py`, a reproducible sympy script that
models `H = (AGL1Z.toPerm p).range = AGL(1,p)` as permutations of `ZMod p` and
certifies, for every odd prime `3 ≤ p ≤ 29`:

- **(A) the corrected Step 5 is SOUND.** With `σ = (x↦x+1)` — a genuine
  order-`p` `p`-cycle generating the translation subgroup `P` (satisfying both
  `hgen` and the S6-refined `σ.support.card = p`) — every `h ∈ H` normalises
  `⟨σ⟩`, so `H ≤ N(⟨σ⟩)`; the closed form `h·τ_c·h⁻¹ = τ_{u·c}` is checked
  element-by-element.
- **(B) the original Step 5 is FALSE** (regression guard reproducing S5's
  counterexample): for `σ' = (x↦g·x)`, `h = (x↦x+1)` gives `h·σ'·h⁻¹ ∉ ⟨σ'⟩`.

Confirms the corrected target statement is true before a Docker-up session is
spent discharging it (S6 ACT item 1, ~5–15 LOC). No `.lean` change, no sorry
count change. Detail in `knowledge.md` Risk R2 numerical-certification note.

## Iteration 8 (researcher-2, 2026-06-14) — S8 ORIENT: independent bearer audit of the Step 1 route + char-transitivity sub-risk

**Outcome**: ORIENT/knowledge (no build — Docker DOWN *and* the Aristotle
MCP returned `Resource not found`; both verification backends are in a
blackout, so no Lean change could be build- or solver-verified this
session). Doc-only: 0 Lean files touched, 5 sorries intact.

**What I did.** Independently re-fetched the five Mathlib source files
backing the S7 derived-series + block route via `gh api .../contents/...?ref=<pin>`
at the lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (a real
mathlib4 commit dated 2025-12-13) and confirmed **every primary bearer
exists at the exact cited line**, with signatures:
- `derivedSeries_succ` Solvable.lean:49, `derivedSeries_normal` :53,
  `derivedSeries_characteristic` (instance) :65 — all present.
- `IsBlock.orbit_of_normal {N : Subgroup G} [N.Normal] (a : X) : IsBlock G (orbit N a)`
  Blocks.lean:475; `IsBlock.subsingleton_or_eq_univ [IsPreprimitive G X]`
  Primitive.lean:115; `isPretransitive_iff_orbit_eq_univ` Transitive.lean:54.
- `Sylow.characteristic_of_normal` Sylow.lean:728; `Sylow.unique_of_normal`
  :710; `Sylow.normal_of_subsingleton` :724.
- `Sylow.ofCard (H : Subgroup G) (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : Sylow p G`
  :102 — note it consumes a `Subgroup G` (here `G = ↥H`) at card `p^(v_p|H|)`.
- Legendre: `padicValNat_factorial` Padics/PadicVal/Basic.lean:578 (present;
  the S7-cited `Nat.Prime.factorization_factorial` is the equivalent form).

So the S7 route is **not** built on phantom bearers — the prior author's
file:line citations are accurate, and a careful re-walk of the math finds
**no new soundness defect** (unlike S5's Step-5 / S6's Sylow-count findings).

**New finding — the char-in-char step is a small BUILD, not wiring.**
The R4 residual lumped "char-in-char composition" in with the ~100–150 LOC
of *wiring of present bearers*. But the composition it needs —
`Q` characteristic in `↥A`, `A` characteristic in `↥H` ⟹ `Q.map A.subtype`
characteristic (hence normal) in `↥H` — has **no direct Mathlib bearer**.
`Subgroup.Characteristic` is defined in `Algebra/Group/Subgroup/Basic.lean:235`
and ships only the `characteristic_iff_{map,comap}_{eq,le}` equivalences and
the `bot`/`top` instances; there is **no `Characteristic.trans` and no
transitivity-through-subtype lemma**, and no standalone `Subgroup/Characteristic.lean`
exists at the pin. The ACT session must therefore either (a) build a small
ad-hoc bridge (~10–30 LOC: restrict each `φ : ↥H ≃* ↥H` to `↥A` using
`A` characteristic, push it through `Q` characteristic, transport back), or
(b) reroute the transport entirely via an abelian primary-component
construction on `A` viewed directly as `Subgroup ↥H` (sidestepping the
`Sylow p ↥A` subtype). This is the single hardest residual sub-step and was
previously mis-scoped as free wiring.

**Net effect on the picture.** Step 1's route is real and bearer-confirmed;
the residual splits into (i) genuine wiring of present bearers (`ofCard`/
`unique_of_normal` transport of `Q` to `↥H`, `v_p` arithmetic) and (ii) one
**~10–30 LOC characteristic-transitivity bridge with no upstream bearer**.
Risk R4 stays MEDIUM (no *blocking* infrastructure gap — the bridge is small
and self-contained), but the ACT picker should budget for the bridge rather
than expect a one-shot composition. 5 sorries unchanged.

**Next action** (unchanged target, sharper estimate): when a backend is up,
discharge Step 1 via the derived-series + block route, building the
char-transitivity bridge (ii) first as a named helper lemma, then the
`ofCard`/`unique_of_normal` transport (i). Then Step 5's corrected+`p`-cycle
signature (R2) and Steps 3/4. Nothing shippable until Docker or Aristotle
returns.

## Iteration 7 (researcher-3, 2026-06-14) — S7 ORIENT: Step 1 bearer-complete route

**Outcome**: ORIENT/knowledge (no build — Docker DOWN, verification
blackout; comment-only Lean docstring edit, build-safe). Resolved the
open next-action R1 left at S6: scope mitigation (b) for Step 1. Audited
the actual `MulAction.IsBlock` / `Primitive` / `Solvable` / `Sylow` API at
the lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api` and
**found a fully bearer-backed sound route for Step 1** — the file's true
blocker — that sidesteps the socle/`MinimalNormal`/`IsElementaryAbelian`
gap R1 had marked HIGH.

**The route (derived-series + block).** Let `A` be the last nontrivial
term of `derivedSeries ↥H` (abelian, normal/characteristic, nontrivial).
`A ⊴ H` ⟹ its `ZMod p`-orbits are blocks (`IsBlock.orbit_of_normal`); by
primitivity each is subsingleton or univ (`IsBlock.subsingleton_or_eq_univ`);
`A` nontrivial + faithful ⟹ some orbit is univ ⟹ `A` transitive ⟹ `p ∣ |A|`.
`A` abelian ⟹ its Sylow-`p` `Q` is normal hence characteristic in `A`
(`Sylow.characteristic_of_normal`), char-in-char ⟹ `Q ⊴ H`. Legendre
`v_p(p!) = 1` ⟹ `|Q| = p` ⟹ `Q` is a Sylow-`p` of `H` (`Sylow.ofCard`),
normal ⟹ unique (`Sylow.unique_of_normal`) ⟹ `Subsingleton (Sylow p H)`. ∎

**Bearer citations** (all present, file:line at pin): `derivedSeries_normal`
Solvable.lean:53, `derivedSeries_characteristic` :65, `derivedSeries_succ` :49;
`IsBlock.orbit_of_normal` Blocks.lean:475; `IsBlock.subsingleton_or_eq_univ`
Primitive.lean:115; `isPretransitive_iff_orbit_eq_univ` Transitive.lean:54;
`Sylow.characteristic_of_normal` Sylow.lean:728; `Sylow.ofCard` :102;
`Sylow.unique_of_normal` :710; `Nat.Prime.factorization_factorial`
Choose/Factorization.lean:42; `padicValNat_factorial` PadicVal/Basic.lean.

**Net effect**: Risk R4 downgraded HIGH→MEDIUM (no missing infrastructure;
residual is ~100–150 LOC of wiring — transport `Q` along `A ↪ H`, char-in-char
composition, `v_p` arithmetic). Step 1 reclassified from "needs Mathlib
upstreaming" to "discharge task, Docker-up ACT". 5 sorries unchanged.

**Next action** (Docker-up ACT): discharge Step 1 via the route above
(~100–150 LOC), then the already-corrected Step 5 signature (~5–15 LOC),
then Step 3/4. Docker required to build-verify any of these — none shippable
during the blackout.

## Iteration 6 (researcher-1, 2026-06-14) — S6 ORIENT: Step 1 route bearer audit

**Outcome**: ORIENT/knowledge (no build — Docker DOWN, verification
blackout). Re-verified the 7 core bearers at the lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (ecosystem intact, no drift
since 2026-06-01) and bearer-audited **Step 1 (`sylow_p_unique`)** — the
hard remaining step — for the first time. Two additive findings.

**Finding A — the "`m < p`" Sylow-count framing is CIRCULAR.** The plan's
item 1 ("Sylow uniqueness on `H` at `|H| = p · m, m < p`") presupposes
its own conclusion. Sylow facts give `n_p ≡ 1 [MOD p]` and `n_p ∣ |H|/p`,
which force `n_p = 1` *only when* `|H|/p < p`; but `H ≤ S_p` only yields
`|H| ∣ p!`, so `|H|/p` can be as large as `(p−1)!`. The bound `|H|/p < p`
is equivalent to `H ≤ AGL(1,p)` — the file-level theorem itself. So Step 1
**cannot** be a self-contained Sylow count. (What *is* cheap and
non-circular: `v_p(|H|) = 1` from Legendre `v_p(p!) = 1`, giving a Sylow-p
of order exactly `p` — this is the honest, Step-1-independent source of
Step 3, but order-`p` ⇏ unique without a normality argument.)

**Finding B — Step 1's sound route has NO Mathlib bearer.** The textbook
(Galois / Rotman 9.11) route is via the socle: a minimal normal subgroup
of a solvable primitive group is elementary abelian and regular, so has
order `= degree = p`, hence is the unique normal Sylow-p. Mathlib at the
pin has **none** of the needed API — searches for `MinimalNormal`, group
`socle`, and `IsElementaryAbelian` all return 0 hits. Step 1 is therefore
**blocked on absent Mathlib infrastructure**, not merely on session time;
it requires building a minimal-normal/regular-action layer, or finding an
alternative prime-degree route via the `MulAction.IsBlock` block-system
API that *is* present in `Primitive.lean`.

**Recommended next ACT (Docker-up):** (1) cheapest real progress is to
fix Step 5's signature to the already-specified corrected form and
discharge it (~5–15 LOC, all bearers present, math settled); (2) prototype
the bearer-complete order-`p` Sylow fact (`v_p(|H|)=1 ⟹ |Sylow|=p`);
(3) do NOT attempt Step 1 uniqueness as a Sylow count (Finding A).

Full bearer table and method in
`sessions/2026-06-14-s6-orient-step1-bearer-audit.md`.

## Iteration 5 (researcher-5, 2026-06-13) — S5 OBSERVE: Step 5 statement is unsound

**Outcome**: correctness finding (no build). Audited the intermediate
lemma statements against the parent file's `AGL1Z`/`toPerm` definitions
and found that **Step 5 (`H_le_normalizer`) is mathematically false as
written**. Its hypothesis `σ ∈ H` does not entail `H ≤ N_{S_p}(⟨σ⟩)`:
that conclusion needs `⟨σ⟩` to equal the image of the *normal* Sylow-p
`P` (Steps 2 + 3), not to be generated by an arbitrary element of `H`.
The statement does not even require `σ` to be a `p`-cycle.

**Counterexample** (`p = 5`): `H = (AGL1Z.toPerm 5).range` (primitive +
solvable, from the parent file), `σ = (x ↦ 2x) = (1 2 4 3) ∈ H`,
`h = (x ↦ x + 1) = (0 1 2 3 4) ∈ H`. Then `h σ h⁻¹ : y ↦ 2y − 1` sends
`0 ↦ 4`, so it does not fix `0`; every element of `⟨σ⟩` fixes `0`, hence
`h σ h⁻¹ ∉ ⟨σ⟩`, so `h ∉ N(⟨σ⟩)` and `H ⊄ N(⟨σ⟩)`. ∎

**Actions taken** (all build-free — Docker is DOWN this session, a
verification blackout): added a `⚠ UNSOUND STATEMENT` block to the Step 5
docstring in the `.lean` (inert doc edit, no signature change → cannot
affect the build), with the counterexample and the corrected signature;
upgraded Risk **R2** in `knowledge.md` from a "low wiring risk" to a
realised defect; updated the JSON tracker `currentState`. **No false
proof exists**: Step 5 and the main theorem are still `sorry`, so this is
a latent trap to fix before assembly, not a soundness break.

**Corrected signature** (defer to a Docker-up session): thread the normal
Sylow `P` and a generator hypothesis through, e.g.
`(P : Sylow p H) (hPnorm : (P : Subgroup H).Normal)`
`(hgen : ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈ zpowers σ)`
`(hσH : σ ∈ H) ⊢ H ≤ (Subgroup.zpowers σ).normalizer`, matching the
outputs of Steps 2 (`sylow_p_normal`) and 3 (`sylow_p_is_pcycle`), then
discharge with a `Subgroup.le_normalizer`-style argument (~5–15 LOC).

**Also corrected a doc over-claim**: older notes call Step 3
(`sylow_p_is_pcycle`) a "~1-LOC / 10-20 LOC bearer application". It is
not trivial: the `p`-cycle structure needs `|P| = p`, which requires
`p ∣ |H|` (from transitivity of the primitive action) plus
`v_p(|H|) ≤ v_p(p!) = 1`. The 1-LOC bearer
(`Equiv.Perm.isCycle_of_prime_order''`) only fires after that order fact
is established.

## Iteration 4 (researcher-2, 2026-06-12) — S4 ACT: discharge Step 2 `sylow_p_normal`

**Outcome**: progress — discharged **Step 2 (`sylow_p_normal`)**, reducing
the file from 6 sorries to **5** (Docker build reports `sorry` at lines
50/77/93/103/119 only). Note: prior docs said "7 sorries", but the
build-verified count before this iteration was 6; the "7" was a
long-standing over-count. The proof composes Step 1's uniqueness statement
with a Mathlib bearer:

```lean
haveI : Subsingleton (Sylow p H) := sylow_p_unique H hPrim hSolv
exact P.normal_of_subsingleton
```

`Sylow.normal_of_subsingleton` (`Mathlib/GroupTheory/Sylow.lean:724`,
re-verified at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) has
signature `[Subsingleton (Sylow p G)] (P : Sylow p G) : P.Normal`. The
only input it needs is the `Subsingleton` instance, supplied by Step 1
(`sylow_p_unique`, still a `sorry`). So Step 2 now carries **no sorry of
its own** — it is fully proved, conditional only on Step 1. The two
previously-unused binders `_hPrim`/`_hSolv` were renamed to `hPrim`/`hSolv`
since they now feed `sylow_p_unique`.

### Honesty / significance

This is a **small, honest** reduction. The mathematical content of Step 2
(unique Sylow ⟹ normal) is one Mathlib lemma application; the genuine work
was confirming the bearer signature and wiring Step 1's output into it.
The hard step remains **Step 1 (`sylow_p_unique`)**: showing the Sylow-p
of a primitive solvable `H ≤ S_p` is unique. The clean route is via
minimal-normal-subgroup / socle theory (a minimal normal subgroup of a
solvable primitive group is elementary abelian and transitive, hence
regular of order p, hence the unique normal Sylow-p) — that needs sustained
multi-session work and Mathlib socle API, not a single tail.

### Files touched

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean` —
  Step 2 body discharged (+ docstring note); 119 → 126 LOC; 6 → 5 sorries.
- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md` — this block.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` — `currentState`.

### Verification

Docker build (`./proofs/scripts/docker-build.sh
Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`) — **completed
successfully, 1900 jobs**, 2026-06-12. Only 5 `sorry` warnings remain
(lines 50/77/93/103/119); 0 errors, 0 axioms.

## Iteration 3 (researcher-1, 2026-06-10) — S3 STATE-SYNC: G9 reclassification

**Outcome**: knowledge — clarification that the "G9 lake self-loop" blocker
flagged in S2 ORIENT is a **researcher-side grep-convenience issue**, NOT
a Docker-build blocker. The next ACT picker should not defer Docker on
G9 grounds.

### Evidence: Docker works on this worktree at HEAD `98d1689ec26`

Verified this session by researcher-1 in `.loom/worktrees/researcher-1/`:
- Ran `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG6`
  on a sibling file (new file under the same project root) on 2026-06-10.
- Result: **7743 jobs clean**, ~158 s for the new module, total ~5–6 min
  including Mathlib cache fetch. (Shipped as PR #22751 / S21 ACT on
  slug `lagrange-four-squares-waring-g2-oq-01`.)
- Host disk: 77 Gi free (`df -h /System/Volumes/Data` reports 92% used).
- Docker daemon: healthy.

The host-side `proofs/.lake` symlink in this worktree is indeed
self-referencing (`ls proofs/.lake/packages/` errors with "Too many
levels of symbolic links"). This means a researcher cannot
`grep -r '<symbol>' proofs/.lake/packages/mathlib/` from the host
shell to audit Mathlib bearer signatures. However, Docker uses **its
own .lake** inside the container; the host symlink does not enter the
container, so `docker-build.sh` is unaffected.

### Implications for S3 ACT picker

- **Docker build is fully available**. The S2 ORIENT framing
  "build pending — G9 lake self-loop" should not be read as
  "Docker is blocked"; it's "I can't grep Mathlib locally from the
  host." The S3 ACT picker can attempt the full 119-LOC file build
  immediately.
- **Bearer audits should use `gh api`** instead of host-side grep.
  Demonstrated this session on the laws-of-large-numbers-oq-01-oq-02
  S4 PREP (PR #22753): `gh api search/code` + `gh api repos/.../contents/...`
  reaches Mathlib v4.26.0 surface without local `.lake` access.
  Bearer pin (`2df2f015…`) is the same one the S2 ORIENT bearer
  pre-flight verified; no re-pin needed.
- **The 7 sorries are the real blocker**, not infrastructure. S3 ACT
  should plan a focused per-sorry discharge cycle. Step 2 (`sylow_p_normal`)
  is the cheapest (any unique Sylow is normal via
  `Sylow.normal_of_subsingleton`) — make it the warm-up.

### What this STATE-SYNC does NOT do

- Does not modify
  `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`.
  The 7 sorries are intact.
- Does not run a Docker build verification. The S21 ACT verification
  on a sibling file is sufficient evidence for Docker availability;
  re-running just to "prove the obvious" wastes ~5 min for no signal.
- Does not discharge any of the 7 sorries. Real S3 ACT work is
  reserved for a dedicated session — the Galois 1832 / Rotman 9.11
  proof recipe needs sustained engagement, not a 25-minute tail.

### Files touched (2 total)

- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md` — this block + phase line refreshed.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` — `currentState.{phase, since, iteration, focus, nextAction}`, `lastUpdate`.

### Honesty

This STATE-SYNC is doc-only:
- 0 Lean files touched, 0 sorry / axiom changes
- 0 new bearer verifications (S2 ORIENT bearer pre-flight inherited)
- 0 Docker build attempts (S21 ACT sibling-file verification reused)

The contribution is a single-paragraph reclassification of an
inherited blocker label, removing an unjustified deferral excuse from
the next picker's path.

---

## Iteration 2 (researcher-1, 2026-06-04) — S2 ORIENT Lean stub

**Outcome**: scaffold — created
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
(119 LOC, 7 sorries, 0 axioms, 6 theorems) plus the auto-generated
`proofs/Proofs.lean` import refresh (`+1 line` after running
`./.lean/scripts/generate-proofs-imports.sh`).

### What I added

- **`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`**
  (NEW, 119 LOC, 7 sorries):
  - imports `Proofs.AbelRuffiniGaloisExtensionsOQ06`,
    `Mathlib.GroupTheory.Sylow`,
    `Mathlib.GroupTheory.Perm.Cycle.Type`
  - opens parent namespace `AbelRuffiniGaloisExtensionsOQ06`
  - 5 step-lemma stubs (one per S1 OBSERVE step):
    - `sylow_p_unique` — `Subsingleton (Sylow p H)` for primitive
      solvable `H ≤ S_p`
    - `sylow_p_normal` — `(P : Subgroup H).Normal` for the unique
      Sylow-p
    - `sylow_p_is_pcycle` — existence of a `p`-cycle `σ ∈ S_p` with
      `P ≤ ⟨σ⟩`
    - `normalizer_iso_AGL1Z` — `(zpowers σ).normalizer ≅ AGL1Z p` via
      conjugation
    - `H_le_normalizer` — `H ≤ (zpowers σ).normalizer` since `P ⊴ H`
  - file-level main stub
    `primitive_solvable_subgroup_embeds_AGL1Z` returning
    `∃ φ : H →* AGL1Z p, Function.Injective φ`
  - 7 sorries total (one per step + main)
- **`proofs/Proofs.lean`** auto-regenerated via
  `./.lean/scripts/generate-proofs-imports.sh` to add the new import
  line at the correct alphabetic insertion point.

### What I did NOT do (deferred to S3+)

- Discharge any of the 7 sorries.
- Run Docker build (G9 lake self-loop blocker; consistent with sibling
  build-pending PRs #21477 #21475 #21506 #22088).
- Author gallery files (`src/data/proofs/.../{meta.json, index.ts,
  annotations.json}`) — deferred until at least one sorry is discharged
  (S5+) so that gallery `status` can claim `formalized` or `verified`
  honestly per Axiom Integrity Policy.

### Bearer pre-flight (re-verified at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Sylow.exists`: ✓ intact
- `Sylow.normal_of_subsingleton` (`Mathlib/GroupTheory/Sylow.lean:724`): ✓ intact
- `Equiv.Perm.isCycle_of_prime_order''`
  (`Mathlib/GroupTheory/Perm/Cycle/Type.lean:412`): ✓ intact
- `Subgroup.normalizer`: ✓ intact
- `Subgroup.zpowers`: ✓ intact
- Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective`
  (`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`): ✓ intact

No Mathlib drift since S1 OBSERVE (2026-06-01, 3 days elapsed; SHA unchanged).

### Race-safety note (S2)

- Pre-claim probe (2026-06-04 ~17:00 UTC): 0 open PRs on the sub-OQ
  slug since S1 merge (#22031, 2026-06-02). Branch
  `research/abel-ruffini-galois-extensions-oq-06-galois-direction-s2-orient`
  is new (per `git branch -r | grep galois-direction` → 0 matches).
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`:
  explicit `-R rjwalters/lean-genius` on all `gh pr` calls.

## Origin

Spun off from parent slug `abel-ruffini-galois-extensions-oq-06` per
the SPLIT recommendation in S6 PREP (PR #18926, merged
2026-05-13T22:22:39Z, researcher-4) and the sub-OQ scaffold draft
in S8 PREP (PR #19216, merged 2026-05-15T~02:15Z, researcher-8).
The parent S8 PREP §6 recommended **Option B "researcher-side
initiate"** if the curator/seeker SPLIT decision exceeded 48 hours
of latency. As of S1 (2026-06-01), the latency budget exceeded by
~16 days (S8 PREP merged 2026-05-15, no curator action through
2026-06-01).

The parent slug owns the **forward direction** (AGL(1, p) is
solvable, primitive, faithful, of order p(p-1)) — formalised as
530 LOC, 0 sorries, 0 axioms,
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`. Build-verified
by parent's S7 ACT (PR #19071, 2026-05-14, Docker `1884/1884` jobs
clean).

This sub-OQ owns the **Galois direction**: every primitive solvable
subgroup of S_p embeds into AGL(1, p).

## Iteration 1 (researcher-1, 2026-06-01) — S1 OBSERVE scaffold (merged via #22031, 2026-06-02)

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md` (this file), and `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`.
No Lean changes. Doc-only PR.

### What I added

Four scaffold files materialising the S8 PREP §5 drop-in template
(reproduced verbatim with minor formatting alignment):

- `problem.md` — Galois-direction problem statement, 5-step proof
  plan (Sylow uniqueness → P normal → P-is-p-cycle →
  N_{S_p}(P) ≅ AGL(1, p) → H ≤ N_{S_p}(P)), Mathlib v4.26.0 bearer
  audit table, references (Galois 1832, Rotman 9.11, Cameron §4.7,
  Wielandt ch. 11), tractability triage (LOC budget 250-450), and
  acceptance criteria.
- `knowledge.md` — sub-OQ-specific knowledge surface: inherited
  bearers, refresh of bearer audit at lake-pinned SHA, risk register
  (R1: conjugation-action wiring; R2: `Subgroup.le_normalizer_of_normal`
  may need ad-hoc; R3: build-pending cascade), cross-slug reuse
  patterns (OQ-07 Sylow pattern; parent's `AGL1Z.toPerm_injective`
  technique), API-gap inventory, estimated LOC profile, and S2+
  topical questions.
- `state.md` — this file. Iteration 1 SCAFFOLD.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` —
  tier B, significance 7, tractability 3, parent linkage,
  bootstrapped `currentState` / `knowledge.progressSummary`.

### Why not S2 ORIENT in this session

S2 ORIENT would author
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
with the import block and the file-level `theorem
primitive_solvable_subgroup_embeds_AGL1Z` stub (sorry), plus the
S3-S5 proof skeletons. That's a focused S2 PR distinct from this S1
SCAFFOLD; it requires verifying the parent's exported symbols
(`AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective`) are accessible
as a namespace import. Per the parent's S2 ACT pattern (PR #18205,
researcher-10), the file should be ~80 lines with 1 file-level
sorry on the main theorem and 0 sorries elsewhere.

### Bearer audit refresh

Re-verified the S8 PREP bearer chain at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Status |
|---|---|
| `Sylow.exists` | ✓ intact |
| `Sylow.card_eq_multiplicity` | ✓ intact |
| `Sylow.normal_of_subsingleton` | ✓ intact (`Sylow.lean:724`) |
| `Equiv.Perm.isCycle_of_prime_order''` | ✓ intact (`Cycle/Type.lean:412`) |
| `Subgroup.normalizer` | ✓ intact |
| `MonoidHom.ofInjective` | ✓ intact |
| Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective` | ✓ intact |

No Mathlib drift since 2026-05-15. Bearer ecosystem ready for S2 ACT.

### Race-safety note (S1)

- Pre-claim probe (2026-06-01 ~20:00 UTC): 0 open PRs on the new
  sub-OQ slug (it did not exist before this PR). Parent slug
  `abel-ruffini-galois-extensions-oq-06` has 0 open PRs as of the
  same probe.
- Stale-branch list (`git branch -r | grep galois-direction`): 0
  matches.
- Slug claim: this PR creates the slug; no prior claim.
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`
  memory: explicit `-R rjwalters/lean-genius` on all `gh pr` calls.

## Next action (S3 ACT — discharge Step 1 `sylow_p_unique`)

The S2 ORIENT scaffold this iteration exposes 7 sorries. S3 ACT should
discharge **Step 1 (`sylow_p_unique`)** first because:

1. It has the cleanest bearer surface: `Sylow.exists` + `Sylow`
   API + `Nat.card H` divisibility arithmetic, all in
   `Mathlib.GroupTheory.Sylow`.
2. It is a prerequisite for Step 2 (`sylow_p_normal` needs a unique
   Sylow to extract `Sylow.normal_of_subsingleton`).
3. The argument follows Galois 1832 / Rotman 9.11 verbatim:
   - `|H| = p · m` where `m < p` (from primitivity + solvability +
     the fact that `H ≤ S_p`; this needs the parent's
     `IsPreprimitive.transitive` + a divisor-count argument).
   - Number of Sylow-p subgroups `s_p ∣ m, s_p ≡ 1 (mod p)`, so
     `s_p = 1` (since `m < p`).

Estimated S3 ACT size: ~40-60 LOC additional content (one theorem
fully discharged; 6 sorries remaining).

Subsequent iterations:

- S4 ACT — Step 2 (`sylow_p_normal`) via `Sylow.normal_of_subsingleton`,
  ~5-10 LOC.
- S5 ACT — Step 3 (`sylow_p_is_pcycle`) via `isCycle_of_prime_order''`,
  ~20-30 LOC.
- S6 ACT — Step 4 (`normalizer_iso_AGL1Z`), the hardest step;
  ~80-150 LOC.
- S7 ACT — Step 5 (`H_le_normalizer`) + main theorem composition,
  ~30 LOC.
- S8 BUILD-VERIFY — Docker build verification once G9 clears.
- S∞ — gallery integration.

## Blockers

None for the structure-theorem direction; bearer ecosystem is intact
at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (re-verified
2026-06-01).

## Iteration 16 (researcher-2, 2026-06-16) — Step 3 drafted turnkey (build-blocked)

**Phase:** S16 ACT. **Outcome:** Step 3 `sylow_p_is_pcycle` fully proved on paper,
parked as a self-contained turnkey draft (`step3-sylow-p-is-pcycle-draft.lean`);
registered file untouched (TRUE `sorry` intact). NOT machine-checked — Aristotle 404
and this worktree's `proofs/.lake` is the self-referential symlink (build aborts at
Mathlib clone, `git 128`). Did not touch the shared `.lake` (policy). See knowledge.md
S16 note for the full proof architecture, the verified bearer list, and the
`Nat.Prime.dvd_factorial`/`pow_dvd_iff_le_factorization` arg-type correction
(pass `Fact.out`, not `Fact.out.prime`).

**Remaining open sorries:** Step 1 (`sylow_p_unique`, hardest), Step 3 (drafted,
awaiting build), Step 4 (`normalizer_iso_AGL1Z`), main theorem. Step 2 & Step 5
discharged.

**Next action:** from any worktree with a healthy `.lake` (or when Aristotle clears),
`docker-build.sh Proofs.Step3SylowPIsPCycleDraft` to verify the draft, then transcribe
into `sylow_p_is_pcycle` (replace `sorry`, rename `_hPrim`→`hPrim`). Low-iteration
expected: bearer surface de-risked, `|P|=p` core reuses Step 5's verified pattern.

## Iteration 17 (researcher-4, 2026-06-17) — Step 3 orphan: 3 real build bugs fixed, build-verifying

**Phase:** S17 ACT. **Backend:** Docker build-CAPABLE this session (rc=0; built
KeithNumberOQ01 + repunit elsewhere). Aristotle still 404. Build pool SEVERELY
contended (10 concurrent lean-build containers from other agents → each cache-get
of 7727 oleans is IO-starved, ~20-40 min/build).

Built `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep3` (the up-to-date
S18-strengthened orphan with the `σ ∈ H` conjunct, signature VERBATIM-identical to
the registered `sylow_p_is_pcycle` stub). First build surfaced the `?`-flagged
bearer bugs the author predicted; fixed THREE against the offline pin `2df2f0150c`:

1. **Step C `hcardP_ft` (Fintype synth fail @139)**: `orderOf_eq_card_of_forall_mem_zpowers`
   returns `Nat.card α` (Cyclic.lean:218), NOT `Fintype.card`. Deleted the
   `Fintype.card (P:Subgroup H)=p` helper; `horda` now `rw [..., hcardP]` (Nat.card).
2. **Step C `hprime` (type mismatch @155)**: `hords ▸ hp` rewrote the wrong way
   (`Nat.Prime p` stayed `Nat.Prime p`, wanted `Nat.Prime (orderOf (ι a))`). Fixed to
   `hords.symm ▸ hp`.
3. **Step A `hpH` (Fintype synth fail on orbit/stabilizer)**:
   `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` needs Fintype instances
   that don't synthesize for `↥H`. Replaced with the **Nat.card/index** route from the
   older `step3-sylow-p-is-pcycle-draft.lean`: `orbitEquivQuotientStabilizer` +
   `Subgroup.index_eq_card` (Index.lean:390) + `Subgroup.index_dvd_card` (Index.lean:398),
   giving `p ∣ Nat.card H` with no Fintype. Also added `have hp1 : 0 < p := hp.pos`
   to feed the `hsupp_lt` omega.

**Next:** once the (slow, contended) build returns GREEN, register the orphan
(`import Proofs.…Step3` in Proofs.lean) and discharge the registered
`sylow_p_is_pcycle` `sorry` by one-line delegation
`exact …Step3.sylow_p_is_pcycle H hPrim hSolv P` (rename the registered binders
`_hPrim _hSolv`→`hPrim hSolv`). That drops the registered file's open sorries 9→8.
Remaining: Step 1 `sylow_p_unique` (hardest), Step 4 `normalizer_iso_AGL1Z`, main thm.
