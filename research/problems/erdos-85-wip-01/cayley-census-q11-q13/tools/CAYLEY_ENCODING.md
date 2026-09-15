# Cayley C4 criterion and encoding

Let G be a finite group with identity e, and S a subset of G excluding e with S=S^{-1}. Use right multiplication: vertices x,y are adjacent iff y=xs for some s in S. The graph is simple, undirected, and |S|-regular.

For h != e, its common neighbors with e are exactly the elements a in S for which a^{-1}h is in S. Thus they are in bijection with ordered representations h=ab with a,b in S. Two distinct representations ab=cd=h have a!=c (cancellation). The vertices e,a,h,c are distinct: h!=e; a,c!=e; h!=a,c because b,d!=e. They form a four-cycle, since h=ab=cd. Conversely translate any four-cycle so an opposite pair is e,h. Its two other vertices give two distinct representations. Therefore C4-freeness is equivalent to at most one ordered representation for every h!=e. Products equal to e must be exempt: these are returns along a single edge, not four-cycles.

For an abelian G and |S|>=3, choose distinct a,b in S with b!=a^{-1} (at most two elements are forbidden for a fixed a). Then ab=ba!=e yields distinct ordered representations and a C4. This is a consequence to check against the pipeline; no abelian group is removed by hand.

Encoding: identity is index0. Boolean x_g has variable number g for 1<=g<|G|. Impose inverse equality and exactly q selected elements. For each h!=e and each nonidentity a whose b=a^{-1}h is nonidentity, create a representation indicator equivalent to x_a AND x_b (reuse x_a for a=b). Impose at most one on the full ordered list of representation indicators; repeated identical indicators are deliberately retained. Sequential OR-prefix gates express at-most-one, and threshold recurrence t[i,k] iff t[i-1,k] OR (t[i-1,k-1] AND x_i) gives exact cardinality by t[last,q] AND NOT t[last,q+1]. All auxiliary gates are equivalences. No symmetry breaking or structural pruning is used.

A SAT result must be decoded and independently checked. Verdict-only UNSAT has no proof certificate and will be reported at precisely that scope. UNKNOWN never excludes a group.
