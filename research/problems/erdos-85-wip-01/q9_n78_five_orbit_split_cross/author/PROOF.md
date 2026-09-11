# Complete partial-graph domain for the split-center five-orbit case

Use accepted2334 for the order24 case with orbit sizes3,3,24,24,24. The group tables and complete cubic Cayley lists are those independently accepted in2322. Groups with no cubic Cayley set cannot supply R and are omitted from subsequent subgroup actions.

The checker generates every subgroup H of order eight by starting with the identity subgroup and repeatedly adjoining one group element and closing under multiplication. Closures larger than eight are discarded, since adjoining elements cannot reduce size. Every order-eight subgroup is reached by successively adjoining its elements, so this is a complete subgroup cover, including groups requiring three generators. It produces41 group/subgroup contexts. Left cosets are ordered by their least elements.

For each context, take every saved cubic Cayley set with one element in each of its three H cosets. Reject an internal set S if |S intersect gS|+1[lambda(g)=0]>1 for some nonidentity g; the indicator is the shared fixed center. For each T with one element in each of the two nonidentity cosets, require its inverse set to do likewise. No inverse closure of T is imposed.

For all remaining SU,SV,T, test the translated common-neighbor counts:

    U1,Ug: |SU intersect gSU|+|T intersect gT|+1[lambda(g)=0]<=1, g!=1;
    V1,Vg: |SV intersect gSV|+|T^-1 intersect gT^-1|+1[lambda(g)=0]<=1, g!=1;
    U1,Vg: |SU intersect gT^-1|+|T intersect gSV|<=1, all g.

Unlike the four-orbit model, the mixed pair has no fixed-center indicator: U attaches to the first three-center orbit, V to the second, so those fixed neighbors are distinct. These formulas follow directly from the left-translate adjacency conventions of2334.

The original aggregate30-second run completed in0.253 seconds. All41 contexts are COMPLETE, with22848 surviving configurations across20 contexts. The exact subgroup/coset records, internal-set lists and every surviving SU,SV,T are saved in results.json. This is a complete necessary partial-graph domain; it does not choose residual neighborhoods or residual internal connections.

A separate verifier rebuilt every54-vertex partial graph directly, including the matching between the two three-center sets. It verified center degree nine, attached degree six, simplicity and all32695488 unordered-pair codegrees. All22848 graphs passed in3.074 seconds under a separate original30-second verification cap. An adjacency-stream SHA256 is stored in verification.json. The positive verification alone is not a proof of exhaustive negative coverage; that coverage requires independent review of the producer and its accepted inputs.

No full graph solver, residual-incidence search, capped UNKNOWN premise or Lean formalization is used. No five-orbit exclusion or graph completion is claimed by this packet.
