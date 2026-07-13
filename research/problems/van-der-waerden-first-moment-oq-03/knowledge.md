# Knowledge Base: van-der-waerden-first-moment-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: connect the **verified, axiom-free** first-moment bound `vdw_lower_bound`
(in `VanDerWaerdenFirstMoment.lean`, namespace `ProbMethod.VanDerWaerden`) to the
**axiom-heavy** `Erdos138Problem.lean` (namespace `Erdos138`), producing a
machine-checked lower bound on `W k` and honestly documenting the strength gap to
the axiomatized bounds.

Key object reconciliation:
- erdos-138 `W k = monoAPNumber 2 k = sInf (monoAP_guarantee_set 2 k)`, where
  `monoAP_guarantee_set 2 k = { N | ∀ coloring : Finset.Icc 1 N → Fin 2,
  ContainsMonoAPofLength coloring k }`. APs are the *set*-theoretic
  `Set.IsAPOfLength` over the subtype `Finset.Icc 1 N`.
- first-moment file works with `Fin n → Bool` colorings, `Mono` (monochromatic
  Finset), and `vdwAP n a d k = (range k).image (i ↦ ((a + i·d : ℕ) : Fin n))`.

## Insights

- **The bridge machinery already exists inside erdos-138** — this was the crux
  discovery. Two existing lemmas do the heavy lifting:
  - `contains_mono_ap_imp (N k) (hk : k>0) (c : Finset.Icc 1 N → Fin 2) :
    ContainsMonoAPofLength c k → HasMonoAP (extend_coloring N c) N k`
    (set/subtype form ⇒ function form over ℕ). Its **contrapositive** turns
    "no function-form mono AP" into "no set-form mono AP".
  - `not_in_guarantee_lt_sInf (k N) : N ∉ monoAP_guarantee_set 2 k → N < W k`
    (directly yields the `W` lower bound; internally uses `W_is_nonempty` +
    `guarantee_upward_closed`).
  So the whole task reduces to: produce a `Finset.Icc 1 N → Fin 2` coloring with
  no function-form monochromatic AP, which is exactly what the first-moment
  coloring gives after an index shift.

- **The index shift is the only real "definitional friction".** erdos-138 uses
  1-based `{1,…,N}` (`HasMonoAP` requires `a ≥ 1`); the first-moment file uses
  0-based `Fin n`. Bridge: `shiftColoring N c v = boolToFin2 (c ((v-1 : ℕ) : Fin N))`.
  A ℕ-AP `a + m·d` (a≥1, a+(k-1)d ≤ N) maps to `vdwAP N (a-1) d k` since
  `(a + m·d) - 1 = (a-1) + m·d`, and the first-moment hypothesis
  `(a-1) + (k-1)d < N` follows from `a + (k-1)d ≤ N` with `a ≥ 1`, `N > 0`.
  Monochromaticity transfers via injectivity of `boolToFin2 : Bool → Fin 2`.

- **Result delivered** (`Erdos138FirstMomentBridge.lean`, namespace `Erdos138`):
  - `firstMoment_W_lower_bound : k ≥ 2 → N² < 2^(k-1) → N < W k`  — the first
    *verified* (no new axioms) lower bound on `W` in the erdos-138 development.
  - `firstMoment_W_pow_lower : k ≥ 2 → 2^((k-2)/2) < W k`  (clean corollary).
  - `firstMoment_bound_negligible : Tendsto (k ↦ 2^(k-1)/4^k) atTop (𝓝 0)` —
    the formal strength gap.

- **No axiom is eliminated (honest).** The elementary bound `W(k) ≳ 2^((k-1)/2)`
  is asymptotically dominated by the axiomatized `kozik_shabanov_lower_bound`
  (`W(k) ≳ c·2^k`) and `berlekamp_lower_bound`. Comparing squares,
  `2^(k-1)/(2^k)² = 2^(k-1)/4^k → 0`. So the contribution **supplements** the
  axioms (adds a proven bound for the elementary regime) but cannot replace them.
  This is the "approach B" outcome anticipated in problem.md, with the gap proved
  rather than merely asserted.

## Dead Ends

- Attempting to reconcile `Set.IsAPOfLength` (with `ENat.card`, set images) with
  `vdwAP` directly would be painful. **Do not** re-derive it: route through the
  function-form `HasMonoAP` using `contains_mono_ap_imp`, which already contains
  that reconciliation.

## Verification Status (IMPORTANT — honest)

- The Lean file `Erdos138FirstMomentBridge.lean` is written and has been
  carefully reviewed by hand, but **was NOT machine-verified this session**:
  the Docker build environment was unavailable — the host disk had filled to 100%
  and Docker Desktop's containerd content store became corrupted (a referenced
  blob went missing; `docker images`/`docker system df`/`prune` all fail with an
  input/output error). `lake build` must never be run directly (memory blowup),
  so Docker is the only sanctioned build path.
- **Next action for whoever picks this up:** once Docker Desktop is restarted /
  repaired, run `./proofs/scripts/docker-build.sh Proofs.Erdos138FirstMomentBridge`
  and fix any lemma-name drift. Lower-risk core: `firstMoment_W_lower_bound`
  (standard tactics + the source file's own idioms). Higher-risk: the analytic
  `firstMoment_bound_negligible` (depends on names `pow_le_pow_right₀`,
  `div_le_iff₀`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `squeeze_zero`).
- The file is intentionally **NOT** registered in `Proofs.lean` until it builds
  (keeps the safe aggregate build green).
