# Knowledge Base: halls-theorem-oq-01-oq-02

## Problem Understanding

Target: the **Finset formulation of Hall's theorem connecting to Hall.Basic and König.**
The Hall gallery family already has: the bipartite graph biconditional (`HallsTheoremOQ01`),
the qualitative Ore defect form (`HallsTheoremOQ01OQ01`, `HallsTheoremOQ02OQ01`), the
regular-bipartite ⟹ perfect-matching corollary (`HallsTheoremOQ01OQ03`), and balanced
one-sided Hall (`HallsTheoremOQ02`). What was missing — and explicitly listed as the open
question of `halls-theorem-oq-01-oq-01` — is the **exact König–Ore deficiency equality**:
the maximum partial-SDR size equals `|ι| − maxₛ(|s| − |N(s)|)`.

## Result (this session)

New entry `HallsTheoremOQ01OQ02.lean` (VERIFIED, 0 sorries, 0 axioms, 277L, Mathlib-only import):

- `deficiency t := (univ : Finset (Finset ι)).sup (fun s => #s − #(s.biUnion t))` — the exact
  maximum deficiency of a finite set system.
- `konig_ore_exists` — a partial SDR missing ≤ `deficiency t` indices exists (defect theorem at
  the single optimal slack `d = deficiency t`).
- `konig_ore_min` — every partial SDR misses ≥ `deficiency t` indices (any SDR is a slack
  witness, so `deficiency t ≤ #rejected`).
- `konig_ore_isLeast` — the minimum unmatched count is exactly `deficiency t` (IsLeast).
- `konig_matching_number` — the matching number is exactly `Fintype.card ι − deficiency t`
  (IsGreatest); the set-system form of König's "max matching = min vertex cover".
- `deficiency_eq_zero_iff` / `deficiency_eq_zero_iff_exists_sdr` — zero deficiency ⟺ Hall's
  condition ⟺ a full SDR (via Mathlib's packaged `all_card_le_biUnion_card_iff_exists_injective`),
  recovering classical Hall.

## Insights

- The optimal slack does not need to be searched for: it is *named* as `deficiency t`, and the
  relaxed Hall condition holds there tautologically by `Finset.le_sup`. Optimality is then a
  one-line duality — any partial SDR is itself a witness that Hall holds with slack `#rejected`.
- Making `deficiency` a `Finset.sup` over the finite powerset reduces both directions to pure
  order theory (`le_sup` up, `sup_le` down). `apply Finset.sup_le` unfolds the `def`
  automatically; the term-mode `le_sup` needed the function passed explicitly (`f := …`).
- `defect_hall` was reproduced verbatim from the verified `HallsTheoremOQ01OQ01` to keep the
  file self-contained (Mathlib-only import), since sibling `Proofs.*` oleans were not built on
  the host and Docker was saturated.

## Verification note

Verified on the host via `lake env lean` against the prebuilt Mathlib oleans (no Docker: the
fleet was saturated, disk ~100%, and concurrent builds were churning shared package oleans).
Iterating through transient `.olean.private` races required a retry loop to hit a clean window.

## Dead Ends / Deferred

- A full bipartite-`SimpleGraph` König (max matching size = min vertex cover size) is a larger
  undertaking and is NOT in Mathlib; deferred as the follow-up open question.
- Making the deficiency-attaining subset an explicit minimum vertex cover (constructive duality)
  is deferred.
