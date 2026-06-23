#!/usr/bin/env python3
"""
End-to-end (capstone) certification of the MAIN theorem of
AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean:

    primitive_solvable_subgroup_embeds_AGL1Z :
        every primitive solvable subgroup H of S_p = Perm(ZMod p)
        embeds into AGL(1, p).                                     (Galois 1832)

Why this is distinct from the prior session certs.  Sessions S7/S9/S11 added
verify_step5_normalizer.py and verify_step4_normalizer.py, which certify the
INTERMEDIATE lemmas (`normalizer_iso_AGL1Z`, the AGL ⊆ N inclusion).  None of
them certify the ASSEMBLED main theorem — and this slug has a documented history
of assembly bugs (S5 found "Step 5 statement is unsound").  Intermediate-step
certs cannot catch a composition error in
    sylow_p_unique → sylow_p_normal → sylow_p_is_pcycle
                   → normalizer_iso_AGL1Z → H_le_normalizer → main.
This script brute-forces the main statement itself.

Method (exhaustive for p ∈ {3, 5, 7}).  For prime degree p a transitive group is
automatically primitive (block sizes divide p, so blocks are trivial), hence
"primitive solvable subgroup of S_p" = "transitive solvable subgroup of S_p".
By Cauchy every transitive subgroup contains an element of order p — a p-cycle —
so up to conjugacy every transitive subgroup contains the fixed p-cycle
σ = (0 1 … p−1).  The embedding property "H embeds into AGL(1,p)" is invariant
under conjugacy, so it suffices to range over all subgroups H with ⟨σ⟩ ≤ H.

We enumerate ALL such H exhaustively: any H ⊇ ⟨σ⟩ equals the join over its
elements of ⟨σ, h⟩, so the set { ⟨σ, g⟩ : g ∈ S_p } generates (under join) the
full lattice of subgroups containing σ.  We then check, for every transitive
solvable H, that H ⊆ AGL(1,p)_std = N_{S_p}(⟨σ⟩) (which equals AGL(1,p) for prime
p).  We also report the transitive NON-solvable subgroups: these are exactly the
ones that escape AGL(1,p), confirming the solvability hypothesis is NECESSARY.

Expected (classical) result:
  p=3: containing-σ subgroups {C3, S3=AGL(1,3)}; both solvable, both ⊆ AGL1.
  p=5: {C5, D5, F20=AGL(1,5), A5, S5}; solvable {C5,D5,F20} ⊆ AGL1; A5,S5 escape.
  p=7: {C7, D7, F21, F42=AGL(1,7), 2×PSL(3,2), A7, S7};
       solvable {C7,D7,F21,F42} ⊆ AGL1; PSL(3,2), A7, S7 escape (non-solvable).

Run:   python3 verify_capstone_embedding.py
Requires: sympy. p=7 takes ~10–15s; p=3,5 are instant.
"""

import sys
import time
from sympy.combinatorics import Permutation, PermutationGroup
from sympy.combinatorics.named_groups import SymmetricGroup


def primitive_root(p):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = (x * g) % p
            seen.add(x)
        if len(seen) == p - 1:
            return g
    raise ValueError(f"no primitive root for {p}")


def p_cycle(p):
    """σ : x ↦ x+1 (mod p)."""
    return Permutation([(i + 1) % p for i in range(p)])


def scaling(p, g):
    """μ_g : x ↦ g·x (mod p); fixes 0."""
    return Permutation([(g * i) % p for i in range(p)])


def AGL1(p):
    """Standard AGL(1,p) = ⟨ x↦x+1, x↦g·x ⟩, g a primitive root.  Order p(p−1)."""
    return PermutationGroup([p_cycle(p), scaling(p, primitive_root(p))])


def _key(G):
    return frozenset(tuple(e.array_form) for e in G.generate())


def subgroups_containing_sigma(p, time_budget=200.0):
    """Exhaustive lattice of subgroups H with ⟨σ⟩ ≤ H ≤ S_p, via join-closure of
    { ⟨σ, g⟩ : g ∈ S_p }.  Returns a list of PermutationGroup, or None on timeout."""
    sigma = p_cycle(p)
    Sp = SymmetricGroup(p)
    seen, groups = set(), []
    t0 = time.time()

    def add(G):
        k = _key(G)
        if k in seen:
            return False
        seen.add(k)
        groups.append(G)
        return True

    for g in Sp.generate():
        add(PermutationGroup([sigma, g]))
        if time.time() - t0 > time_budget:
            return None

    changed = True
    while changed:
        changed = False
        snapshot = list(groups)
        for i in range(len(snapshot)):
            for j in range(i, len(snapshot)):
                J = PermutationGroup(list(snapshot[i].generators) +
                                     list(snapshot[j].generators))
                if add(J):
                    changed = True
            if time.time() - t0 > time_budget:
                return None
    return groups


def certify(p):
    t0 = time.time()
    AG = AGL1(p)
    agl_elems = set(tuple(e.array_form) for e in AG.generate())
    subs = subgroups_containing_sigma(p)
    if subs is None:
        print(f"  p={p}: TIMEOUT")
        return False

    counterexamples = []   # solvable+transitive but NOT ⊆ AGL1  (would refute)
    escapers = []          # transitive but NOT solvable AND NOT ⊆ AGL1 (expected)
    print(f"  p={p}:  {len(subs)} subgroups contain a fixed p-cycle"
          f"  (AGL(1,{p}) order = {AG.order()})")
    for G in subs:
        order = G.order()
        transitive = G.is_transitive()
        solvable = G.is_solvable
        inside = all(tuple(e.array_form) in agl_elems for e in G.generate())
        tags = [t for t, c in (("trans", transitive), ("solv", solvable),
                               ("⊆AGL1", inside)) if c]
        print(f"      |H|={order:5d}   {', '.join(tags)}")
        if transitive and solvable and not inside:
            counterexamples.append(order)
        if transitive and not solvable and not inside:
            escapers.append(order)

    ok_main = not counterexamples
    necessity = bool(escapers)   # at least one non-solvable transitive escaper
    print(f"      MAIN theorem (every transitive solvable H ⊆ AGL1): "
          f"{'PASS' if ok_main else 'FAIL ' + str(counterexamples)}")
    print(f"      solvability NECESSARY (non-solvable transitive escapers): "
          f"{'YES ' + str(escapers) if necessity else 'none found'}")
    print(f"      ({time.time() - t0:.1f}s)")
    # For p=3 there are no non-solvable transitive subgroups (S3 is solvable), so
    # necessity is only asserted for p ≥ 5.
    return ok_main and (necessity or p == 3)


def main():
    print("=" * 70)
    print("Capstone cert: primitive_solvable_subgroup_embeds_AGL1Z  (exhaustive)")
    print("=" * 70)
    results = {p: certify(p) for p in (3, 5, 7)}
    print("-" * 70)
    all_ok = all(results.values())
    for p, ok in results.items():
        print(f"  p={p}: {'PASS' if ok else 'FAIL'}")
    print("-" * 70)
    print("ALL CHECKS PASS" if all_ok else "SOME CHECKS FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
