# Excluding the remaining double-attachment five-orbit case

Assume the order24 five-orbit double-attachment case of accepted2340. Write F6 for the matching centers and B12 for the orbit whose vertices each have two F neighbors. Accepted2335 gives internal degree one on B in all four quotients of this type. Accepted2340 identifies B equivariantly with the twelve unordered pairs of centers from distinct matching edges, and identifies A with one of the signed matching actions

    A0={(v,sigma): sum(v)=0},
    A1={(v,sigma): sum(v)=sign(sigma)}.

Label the matching centers (i,+),(i,-), for i=0,1,2. Let b in B be the pair {(0,+),(1,+)} and let b' be {(0,-),(1,-)}. In A0 take the automorphism t interchanging axes0 and1 and fixing the signs and axis2. In A1 take the same interchange and also flip the sign on axis2. These elements lie in the stated groups, respectively, and both fix b and b'.

These are the only B vertices fixed by t. An unordered pair in B uses two different axes. If one is axis2, applying t changes the other axis0 to1 or1 to0, so the pair is not invariant. If the two axes are0 and1, applying t interchanges them without changing their endpoint signs. The pair is invariant exactly when both signs agree, giving b or b'. The optional sign flip on axis2 does not affect this argument.

Because b has exactly one neighbor in B, that neighbor must be fixed by every automorphism fixing b, in particular by t. Simplicity prevents b from being its own neighbor. Thus the unique B neighbor of b is b'.

Now the four distinct vertices

    (0,+), b, b', (0,-)

form a C4: the first and last incidences follow from the defining F-neighbor pairs of b and b'; the middle edge is the forced internal B edge; and the closing edge is a matching edge of F. This contradicts C4-freeness. Both A0 and A1 cases are excluded.

The accompanying check.json only verifies the two explicit permutations and their two fixed B pairs, plus the saved quotient diagonal condition. It is not a search for graph completions. The proof itself is complete without computation.

Together with accepted2338 and2339, any remaining five-orbit candidate must have |A|=24, orbit sizes(6,12,12,24,24), and the unique-attachment quotient type: its matching F6 attaches only to the two24-orbits, four neighbors in each; the two12-orbits have no F neighbors. This remaining case and all larger orbit counts are not excluded here. No full Erdős85 solution or Lean formalization is claimed.
