#!/usr/bin/env python3
"""
Triage of the 91 blocked candidate-pool problems (issue #43007, epic #43004).

The candidate pool served to Researchers (.lean/state/candidate-pool.json) is
regenerated every Seeker cycle by research/db/sync_pool.py from
research/db/knowledge.db (gitignored runtime state, the source of truth for
pool status). A 2026-06-13/14 host verification blackout (Docker daemon hung +
Aristotle backend 404) caused dozens of problems to be flagged `blocked`; the
blackout ended weeks ago but nothing ever unblocked them. Several other rows
were blocked with a literal unfilled template ("[Explain what we're trying to
prove in accessible terms]") as their pool-visible reason, or with no reason
at all.

This script applies a reviewed, per-slug disposition table (see issue #43007
and research/notes/blocked-pool-triage-2026-07-23.md for the rationale):

  * available  — the recorded blocker is gone (Docker is back, .lake symlink
                 loop fixed, parent files repaired/migrated in #37676/#39062)
                 or none ever existed. Row returns to the servable pool.
  * blocked    — a genuine blocker exists (Mathlib gap, open mathematics,
                 human-only step, ungrounded stub). current_blockers is
                 rewritten to a concrete, specific reason.
  * graduated  — the git-tracked registry already records the problem as
                 graduated; the DB row is reconciled to the terminal status
                 (sync-db-status-from-registry.py only reconciles *servable*
                 rows, so blocked->graduated needs this one-time fix).
  * skipped    — duplicate of completed sibling slugs; never serve.

Placeholder / corrupted statement_plain values are replaced with real
statements sourced from each problem's research/problems/<slug>/problem.md.

The script also flips registry.json entries from `blocked` to `active` for
rows returned to `available`: launch-seeker.sh runs
scripts/research/sync-db-status-from-registry.py before every pool regen,
which would otherwise copy the stale registry `blocked` right back onto the
freshly unblocked (servable) DB row.

Idempotent and safe to re-run: status changes only apply to rows still in the
source status ('blocked'), statement replacements only fire while the current
statement is empty/placeholder/corrupted, and the DB is backed up alongside
itself once (knowledge.db.pre-triage-issue43007).

Usage:
    python3 scripts/research/triage-blocked-pool.py --dry-run   # report only
    python3 scripts/research/triage-blocked-pool.py --apply     # write DB + registry
    # then regenerate the pool:
    python3 research/db/sync_pool.py
"""

import json
import shutil
import sqlite3
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DB_PATH = REPO_ROOT / "research" / "db" / "knowledge.db"
REGISTRY_PATH = REPO_ROOT / "research" / "registry.json"
BACKUP_PATH = REPO_ROOT / "research" / "db" / "knowledge.db.pre-triage-issue43007"

TRIAGE_TAG = "(triage #43007, 2026-07-23)"

# Statement placeholders that may be overwritten by a real statement.
PLACEHOLDER_STATEMENTS = {
    "",
    "[Explain what we're trying to prove in accessible terms]",
    "AVAILABLE",
    "BLOCKED: BLOCKED: AVAILABLE: AVAILABLE",
}

# ---------------------------------------------------------------------------
# Disposition table. Keys: every slug with status='blocked' in knowledge.db at
# triage time (91 rows, 2026-07-23). Values:
#   action:    'available' | 'blocked' | 'graduated' | 'skipped'
#   reasons:   list[str] — new current_blockers (only for action='blocked'/'skipped')
#   statement: replacement statement_plain (applied only over placeholders)
#   next:      next_action to set
# ---------------------------------------------------------------------------
D = {
    # ------------------------------------------------------------------ sig 9
    "amgm-inequality-oq-04-oq-03": {
        "action": "available",
        "statement": (
            "Prove Gauss's AGM theorem M(a,b) = a*pi/(2K(k')) with "
            "k' = sqrt(1-k^2), k = b/a, via the hypergeometric identity "
            "K(k) = (pi/2) * 2F1(1/2,1/2;1;k^2)."
        ),
        # Blocked 2026-06-13 solely by the Docker/Aristotle verification
        # blackout; every discharge leg was build-gated. Docker is back.
    },
    "szemeredi-full-oq-01": {
        "action": "available",
        "next": (
            "Verify parent build first: the recorded 28-error regression in "
            "Proofs.FurstenbergCorrespondenceOQ01 predates the v4.26->v4.31 "
            "toolchain migration (#39062) which touched the file; run "
            "./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01 "
            "and resume the S13 roadmap if green " + TRIAGE_TAG
        ),
    },
    "euler-polyhedral-formula-oq-02-oq-01-oq-01": {
        "action": "blocked",
        "statement": (
            "Full smooth Gauss-Bonnet from first principles: for a compact "
            "Riemannian 2-manifold M with boundary, "
            "integral_M K dA + integral_dM k_g ds = 2*pi*chi(M)."
        ),
        "reasons": [
            "Mathlib gap: no Gaussian curvature, geodesic curvature, Riemannian "
            "area form, manifold integration, or Stokes for "
            "manifolds-with-boundary; re-survey when these land in Mathlib "
            + TRIAGE_TAG
        ],
    },
    # ------------------------------------------------------------------ sig 8
    "algebraic-numbers-countable-oq-03": {
        "action": "blocked",
        "reasons": [
            "Gelfond-Schneider transcendence requires machinery absent from "
            "Mathlib (even Hermite-Lindemann is gated on upstream Mathlib PR "
            "#28013, cf. nth-root-irrational-oq-03); also no problem.md "
            "grounding under research/problems/ " + TRIAGE_TAG
        ],
    },
    "ballot-problem-oq-03-oq-01-oq-02-incomplete-01": {
        "action": "available",
        "next": (
            "Discharge the multi-corner GNW-exchange sorry (~150-200 LOC): "
            "prove the cross-product identity "
            "F(mu,c1)*F(mu\\c1,c2) = F(mu,c2)*F(mu\\c2,c1) by induction on "
            "|mu| (GNW 1979), then alpha determination; verify PR #15599 "
            "single-corner build first " + TRIAGE_TAG
        ),
    },
    "bertrands-postulate-oq-02": {"action": "available"},
    "euler-polyhedral-formula-oq-02-oq-01-wip-01": {
        "action": "available",
        "statement": (
            "WIP completion of the smooth Gauss-Bonnet gallery proof "
            "(euler-polyhedral-formula-oq-02-oq-01): derive "
            "gauss_bonnet_polygon from gauss_bonnet_boundary via a "
            "GeodesicPolygon.toBoundary coercion (~10 LOC S4 ACT)."
        ),
    },
    "fundamental-theorem-calculus-oq-02-incomplete-01": {
        "action": "available",
        "statement": (
            "Generalized Stokes theorem companion (fundamental-theorem-calculus"
            "-oq-02): create IteratedFDerivSymmetric.lean supporting lemmas "
            "toward the exterior-derivative machinery."
        ),
    },
    "sperner-ndim-oq-05": {
        "action": "blocked",
        "reasons": [
            "Human-only step: refresh rjwalters/mathlib4:sperner-abstract-parity "
            "with current SpernerMathlib4.lean and submit the upstream Mathlib "
            "PR (ref mathlib4#25231); no research-agent action possible until "
            "then " + TRIAGE_TAG
        ],
    },
    # ------------------------------------------------------------------ sig 7
    "ballot-problem-oq-02-oq-05": {"action": "available"},
    "basel-problem-oq-01-oq-01-oq-02-oq-02": {"action": "available"},
    "bertrands-postulate-oq-01": {
        "action": "blocked",
        "reasons": [
            "Cramer's conjecture is open mathematics (1936; provable under RH "
            "only) — removing axiom cramer_conjecture is infeasible for any "
            "agent; Mathlib also lacks PNT-strength analytic number theory "
            + TRIAGE_TAG
        ],
    },
    "birthday-problem-oq-03-oq-01-oq-02-oq-01": {"action": "available"},
    "cauchy-interlacing-theorem-oq-01-oq-01-oq-01-oq-01-oq-01": {
        "action": "available",
        "next": "Begin problem exploration (state.md: phase NEW, no blockers) "
        + TRIAGE_TAG,
    },
    "cevas-theorem-oq-01-oq-01": {"action": "graduated"},
    "cevas-theorem-oq-01-oq-02": {
        "action": "blocked",
        "reasons": [
            "Ungrounded stub: no research/problems/cevas-theorem-oq-01-oq-02/ "
            "directory (no problem.md or state.md); needs seeker re-grounding "
            "before serving " + TRIAGE_TAG
        ],
    },
    "erdos-1151-oq-04": {"action": "available"},
    "erdos-1168-oq-04": {
        "action": "blocked",
        "statement": "",
        "reasons": [
            "Ungrounded seeker stub: no research/problems/erdos-1168-oq-04/"
            "problem.md; demoted by seeker 2026-06-16; needs re-grounding "
            + TRIAGE_TAG
        ],
    },
    "erdos-1210": {"action": "available"},
    "erdos-166-oq-04": {
        "action": "blocked",
        "statement": "",
        "reasons": [
            "Ungrounded seeker stub: no research/problems/erdos-166-oq-04/"
            "problem.md; demoted by seeker 2026-06-16; needs re-grounding "
            + TRIAGE_TAG
        ],
    },
    "erdos-476-oq-05-incomplete-01": {
        "action": "blocked",
        "reasons": [
            "Ungrounded seeker stub: no research/problems/erdos-476-oq-05-"
            "incomplete-01/problem.md; demoted by seeker 2026-06-16; needs "
            "re-grounding " + TRIAGE_TAG
        ],
    },
    "erdos-604-incomplete-01": {
        "action": "blocked",
        "reasons": [
            "Mathlib gap: Landau-Ramanujan density theorem absent; workable "
            "fallback per state.md is axiomatizing it as a named hypothesis "
            "(status: axiomatized, blocker disclosed) " + TRIAGE_TAG
        ],
    },
    "erdos-998-oq-02": {
        "action": "blocked",
        "statement": "",
        "reasons": [
            "Ungrounded seeker stub: no research/problems/erdos-998-oq-02/"
            "problem.md; demoted by seeker 2026-06-16; needs re-grounding "
            + TRIAGE_TAG
        ],
    },
    "erdos-szekeres-oq-03": {"action": "available"},
    "four-square-distribution-oq-01": {
        "action": "blocked",
        "reasons": [
            "Mathlib gap: no q-expansion/Fourier-coefficient machinery for "
            "jacobiTheta and no Eisenstein-coefficient identification "
            "(theta^4 vs E2(tau) - 4*E2(4tau)) " + TRIAGE_TAG
        ],
    },
    "greens-theorem-oq-02-oq-02": {"action": "graduated"},
    "hilbert-11-oq-02": {
        "action": "blocked",
        "reasons": [
            "Mathlib gap: Hasse-Weil bound for genus-1 curves over F_p absent — "
            "the unconditional Case-B universal theorem is multi-session "
            "Mathlib-scale work " + TRIAGE_TAG
        ],
    },
    "hurwitz-theorem-wip-01": {
        "action": "blocked",
        "reasons": [
            "Mathlib gap: no classical Frobenius theorem for real division "
            "algebras (finite-dim associative division algebra over R has "
            "finrank in {1,2,4}); verified absent 2026-05-08 " + TRIAGE_TAG
        ],
    },
    "inclusion-exclusion-oq-01-oq-02": {
        "action": "blocked",
        "statement": "",
        "reasons": [
            "Ungrounded: no research/problems/inclusion-exclusion-oq-01-oq-02/ "
            "directory and corrupted statement metadata; needs seeker "
            "re-grounding " + TRIAGE_TAG
        ],
    },
    "konigsberg-oq-03-wip-01": {
        "action": "available",
        "statement": (
            "Complete the WIP proof 'Eulerian Paths in Hypergraphs and Infinite "
            "Graphs' (konigsberg-oq-03): file is 0-sorry/0-axiom; pursue the S8 "
            "candidate-menu extensions."
        ),
    },
    "minkowski-fundamental-theorem-oq-06": {"action": "available"},
    "nth-root-irrational-oq-03": {
        "action": "blocked",
        "reasons": [
            "Hermite-Lindemann discharge gated on upstream Mathlib PR #28013; "
            "remaining S5d path needs continued-fraction API absent from the "
            "pinned Mathlib " + TRIAGE_TAG
        ],
    },
    "prob-method-lovasz-local-oq-01": {"action": "available"},
    "roth-theorem-k3-oq-03-incomplete-01": {
        "action": "available",
        "statement": (
            "Density increment via Gowers norms: companion to "
            "Proofs.RothTheoremOQ03 (roth-theorem-k3-oq-03)."
        ),
        "next": (
            "Verify parent build first: the recorded v4.26 API-drift errors in "
            "Proofs.RothTheoremOQ03 predate the #37676 drift repair and the "
            "v4.31 migration (#39062); run ./proofs/scripts/docker-build.sh "
            "Proofs.RothTheoremOQ03, then resume the companion roadmap "
            + TRIAGE_TAG
        ),
    },
    "roth-theorem-oq-02": {"action": "available"},
    "sperner-ndim-mathlib-oq-02": {
        "action": "available",
        "next": (
            "Verify parent build first: the recorded 100+ v4.26-drift errors in "
            "SpernerFreudenthalSimplex.lean predate the v4.31 migration "
            "(#39062) which touched the file; run ./proofs/scripts/"
            "docker-build.sh Proofs.SpernerFreudenthalSimplex and resume the "
            "rebase queue if green " + TRIAGE_TAG
        ),
    },
    "sum-of-divisors-oq-02": {"action": "available"},
    # -------------------------------------------------------- sig NULL (deep OQ)
    "halting-problem-oq-03": {"action": "available"},
    "motivic-flag-maps-oq-03": {"action": "available"},
    "weak-goldbach-oq-03": {"action": "available"},
    # ------------------------------------------------------------------ sig 6
    "abel-ruffini-galois-extensions-oq-05": {
        "action": "available",
        "next": "Begin problem exploration (state.md: phase NEW, blockers: none) "
        + TRIAGE_TAG,
    },
    "abel-ruffini-oq-08": {
        "action": "available",
        "next": "Resume OBSERVE (state.md: blockers none) " + TRIAGE_TAG,
    },
    "algebraic-numbers-countable-oq-02-oq-01": {
        "action": "blocked",
        "reasons": [
            "Ungrounded: no research/problems/algebraic-numbers-countable-oq-02-"
            "oq-01/ state; blocked in registry with no recorded reason; needs "
            "re-triage/grounding " + TRIAGE_TAG
        ],
    },
    "binomial-theorem-oq-02-oq-01-oq-01-oq-03": {"action": "available"},
    "bounded-prime-gaps-oq-03-oq-02": {"action": "available"},
    "cantor-diagonalization-oq-01-oq-01-oq-02-oq-01": {
        "action": "blocked",
        "reasons": [
            "At axiom floor: 4 genuine Easton-1970 realizability axioms require "
            "class-forcing infrastructure absent from Mathlib (multi-year); "
            "no session-sized discharge exists " + TRIAGE_TAG
        ],
    },
    "cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01": {
        "action": "available"
    },
    "cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01": {
        "action": "available",
        "next": (
            "Discharge skolemNoether_module_iso (Wedderburn-Artin + isotypic "
            "module isomorphism, ~200-300 LOC — research-hard but no external "
            "blocker now that Docker is back) " + TRIAGE_TAG
        ),
    },
    "central-limit-theorem-oq-01-oq-01-oq-04-oq-01": {"action": "available"},
    "dilworth-theorem-oq-01-oq-03": {
        "action": "skipped",
        "reasons": [
            "Duplicate of completed work under sibling slugs dilworth-theorem-"
            "oq-01 and dilworth-theorem-oq-01-oq-01-oq-02 (state.md: SURVEYED, "
            "do not build) " + TRIAGE_TAG
        ],
    },
    "ehrhart-cube-proven-oq-05": {
        "action": "blocked",
        "reasons": [
            "Soundness blocker: the S5 target picks_theorem_derived is FALSE as "
            "stated (S4 OBSERVE, PR #23003 constant-curve/placement "
            "counterexample); the proposition must be restated before any ACT "
            + TRIAGE_TAG
        ],
    },
    "erdos-1006-oq-01-oq-02": {"action": "available"},
    "erdos-1036-oq-01-oq-01": {
        "action": "blocked",
        "reasons": [
            "Ungrounded: no research/problems/erdos-1036-oq-01-oq-01/ state and "
            "no recorded blocker; blocked status inherited without reason — "
            "needs seeker re-grounding " + TRIAGE_TAG
        ],
    },
    "erdos-1039-oq-04": {
        "action": "blocked",
        "reasons": [
            "Ungrounded: no research/problems/erdos-1039-oq-04/ state and no "
            "recorded blocker; blocked status inherited without reason — needs "
            "seeker re-grounding " + TRIAGE_TAG
        ],
    },
    "erdos-258-oq-01": {
        "action": "blocked",
        "reasons": [
            "General non-monotone case is open mathematics (Erdős problem 258); "
            "no state grounding recorded under research/problems/ " + TRIAGE_TAG
        ],
    },
    "erdos-460-incomplete-01": {
        "action": "blocked",
        "reasons": [
            "Ungrounded: no research/problems/erdos-460-incomplete-01/ state "
            "and no recorded blocker; blocked status inherited without reason — "
            "needs seeker re-grounding " + TRIAGE_TAG
        ],
    },
    "erdos-659-oq-01-oq-02": {
        "action": "available",
        "next": (
            "Resume S9 PREP ((5,7) axis-vs-plane mixed-modulus recipe); note "
            "the lower-bound side must be axiomatised (no Mathlib Solymosi-Vu) "
            + TRIAGE_TAG
        ),
    },
    "erdos-735-oq-04": {"action": "available"},
    "erdos-818-incomplete-01": {
        "action": "blocked",
        "reasons": [
            "Elementary provable layer mined out across prior sessions; "
            "remaining axioms are deep (vein saturated — see prior researcher "
            "session records) " + TRIAGE_TAG
        ],
    },
    "erdos-895-incomplete-01": {
        "action": "blocked",
        "reasons": [
            "barber_theorem positive direction needs a >1000-line SAT/case "
            "proof (graph space 2^(n choose 2), not decide-able, not "
            "session-sized; Aristotle not a fit); counterexample direction "
            "fully shipped; mined out across 7 sessions " + TRIAGE_TAG
        ],
    },
    "erdos-szekeres-oq-02": {"action": "available"},
    "fermat-defect-one-oq-02": {
        "action": "available",
        "next": (
            "Resume ACT on the n=3 result (state.md: no blockers for n=3; the "
            "n>=4 direction is abc/Pillai-hard and out of scope — do NOT "
            "submit the headline sorry to Aristotle) " + TRIAGE_TAG
        ),
    },
    "fodor-pressing-down-oq-04": {"action": "available"},
    "gauss-wilson-non-cyclic-oq-02": {"action": "available"},
    "gauss-wilson-non-cyclic-oq-03": {"action": "available"},
    "general-quartic-oq-02": {"action": "available"},
    "godel-second-incompleteness-oq02-oq-01": {
        "action": "blocked",
        "reasons": [
            "init-gap phantom: no research/problems/godel-second-incompleteness-"
            "oq02-oq-01/problem.md; demoted by seeker 2026-07-07; needs "
            "re-grounding " + TRIAGE_TAG
        ],
    },
    "godel-second-incompleteness-oq02-oq-02": {"action": "available"},
    "greens-theorem-oq-01-oq-01-oq-02-oq-01": {"action": "available"},
    "greens-theorem-oq-01-oq-01-oq-02-oq-02": {"action": "available"},
    "hilbert-14-oq-04": {"action": "available"},
    "infinitude-primes-4k1-oq-03": {
        "action": "blocked",
        "reasons": [
            "Mathlib gap: the natural-density form requires an Ikehara/"
            "Tauberian transfer absent from Mathlib " + TRIAGE_TAG
        ],
    },
    "inverse-galois-d4-oq-03": {"action": "available"},
    "kepler-conjecture-oq-03": {
        "action": "blocked",
        "reasons": [
            "init-gap phantom: no research/problems/kepler-conjecture-oq-03/"
            "problem.md; demoted by seeker 2026-07-07; needs re-grounding "
            + TRIAGE_TAG
        ],
    },
    "pell-equation-oq-05": {"action": "available"},
    "prime-number-theorem-oq-01": {
        "action": "blocked",
        "reasons": [
            "Target is the Riemann Hypothesis itself — open mathematics; no "
            "formal proof path exists " + TRIAGE_TAG
        ],
    },
    "product-of-segments-of-chords-oq-03": {"action": "available"},
    "shannon-channel-coding-oq-02-oq-01-oq-01": {"action": "available"},
    "shapley-folkman-oq-01": {"action": "available"},
    "sperner-simplicial-instance-oq-01": {"action": "available"},
    "sqrt2-minpoly-oq-03": {"action": "available"},
    "tietze-extension-theorem-oq-01-oq-02": {"action": "graduated"},
    "triangle-inequality-oq-04-oq-01": {"action": "available"},
    "wilson-theorem-oq-01": {"action": "graduated"},
    # ------------------------------------------------------------------ sig 5
    "ballot-problem-oq-01-oq-02-oq-01-oq-02-oq-01": {"action": "available"},
    "chinese-remainder-non-coprime-oq-01-oq-02": {"action": "available"},
    "desargues-theorem-oq-02-oq-02": {"action": "available"},
    "erdos-1002-oq-01-wip-01": {
        "action": "blocked",
        "reasons": [
            "Ungrounded: no research/problems/erdos-1002-oq-01-wip-01/ state "
            "and no recorded blocker; blocked status inherited without reason — "
            "needs seeker re-grounding " + TRIAGE_TAG
        ],
    },
    "spherical-law-of-sines-oq-03": {"action": "graduated"},
    # ------------------------------------------------------------------ sig 4
    "erdos-1064-oq-03": {
        "action": "blocked",
        "reasons": [
            "Ungrounded: no research/problems/erdos-1064-oq-03/ state and no "
            "recorded blocker; blocked status inherited without reason — needs "
            "seeker re-grounding " + TRIAGE_TAG
        ],
    },
    "erdos-1093-oq-02": {
        "action": "blocked",
        "reasons": [
            "state.md is Phase BLOCKED without a recorded blocker; needs "
            "per-problem re-triage before serving " + TRIAGE_TAG
        ],
    },
}


def main() -> None:
    apply = "--apply" in sys.argv
    dry_run = "--dry-run" in sys.argv or not apply

    if not DB_PATH.exists():
        print(f"Error: database not found at {DB_PATH}")
        print("(knowledge.db is gitignored runtime state; run from the main "
              "checkout where the live DB resides.)")
        sys.exit(1)

    if apply and not BACKUP_PATH.exists():
        shutil.copy2(DB_PATH, BACKUP_PATH)
        print(f"Backed up DB to {BACKUP_PATH}")

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cur = conn.cursor()

    cur.execute(
        "SELECT slug, status, statement_plain, current_blockers, next_action "
        "FROM problems WHERE status = 'blocked'"
    )
    blocked_rows = {r["slug"]: r for r in cur.fetchall()}

    missing = sorted(set(blocked_rows) - set(D))
    if missing:
        print(f"WARNING: {len(missing)} blocked rows have NO disposition "
              "(left untouched):")
        for s in missing:
            print(f"  {s}")

    stats = {"available": 0, "blocked": 0, "graduated": 0, "skipped": 0,
             "already-done": 0, "stmt-fixed": 0}
    changes = []

    for slug, d in sorted(D.items()):
        row = blocked_rows.get(slug)
        if row is None:
            # Row no longer blocked (already applied, or claimed since).
            stats["already-done"] += 1
            continue

        action = d["action"]
        sets, args = [], []

        if action != "blocked":
            sets.append("status = ?")
            args.append(action)
        if action in ("blocked", "skipped") and d.get("reasons"):
            sets.append("current_blockers = ?")
            args.append(json.dumps(d["reasons"], ensure_ascii=False))
        if action == "available":
            # Clear stale blackout/blocker text on rows returning to the pool.
            sets.append("current_blockers = ?")
            args.append("[]")

        stmt = d.get("statement")
        if stmt is not None and (row["statement_plain"] or "").strip() in \
                PLACEHOLDER_STATEMENTS:
            sets.append("statement_plain = ?")
            args.append(stmt)
            stats["stmt-fixed"] += 1

        nxt = d.get("next")
        if nxt:
            sets.append("next_action = ?")
            args.append(nxt)

        sets.append("last_updated = CURRENT_TIMESTAMP")
        stats[action] += 1
        changes.append((slug, action))
        if apply:
            cur.execute(
                f"UPDATE problems SET {', '.join(sets)} WHERE slug = ? "
                "AND status = 'blocked'",
                (*args, slug),
            )

    # ---- registry.json: blocked -> active for rows returned to the pool ----
    registry_flips = []
    if REGISTRY_PATH.exists():
        with open(REGISTRY_PATH) as f:
            registry = json.load(f)
        avail_slugs = {s for s, d in D.items() if d["action"] == "available"}
        for p in registry.get("problems", []):
            if p.get("slug") in avail_slugs and p.get("status") == "blocked":
                registry_flips.append(p["slug"])
                if apply:
                    p["status"] = "active"
        if apply and registry_flips:
            with open(REGISTRY_PATH, "w") as f:
                json.dump(registry, f, indent=2, ensure_ascii=False)
                f.write("\n")

    mode = "APPLY" if apply else "DRY-RUN"
    print(f"[{mode}] triage-blocked-pool (issue #43007)")
    print(f"  dispositions:      {len(D)}")
    print(f"  currently blocked: {len(blocked_rows)}")
    print(f"  -> available:      {stats['available']}")
    print(f"  -> kept blocked:   {stats['blocked']} (reasons rewritten)")
    print(f"  -> graduated:      {stats['graduated']}")
    print(f"  -> skipped:        {stats['skipped']}")
    print(f"  statements fixed:  {stats['stmt-fixed']}")
    print(f"  already applied:   {stats['already-done']}")
    print(f"  registry blocked->active flips: {len(registry_flips)}")

    if apply:
        conn.commit()
        print("  DB committed.")
        print("  Now regenerate the pool: python3 research/db/sync_pool.py")
    conn.close()


if __name__ == "__main__":
    main()
