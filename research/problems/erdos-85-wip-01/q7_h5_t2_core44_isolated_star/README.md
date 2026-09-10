# Core44 isolated-pair star constraint

Under the reviewed H5/T2 premises, F={2,4} has no heavy neighbours and its empty demand is zero. BC=J and low degree5 therefore force exactly five singleton neighbours, one of each high colour. Call them f0 through f4.

Any second heavy neighbour of fi must have support disjoint from F. The only such available heavy is C={1,3}. C and F can share at most one singleton by C4-freeness. C already meets B={0,3,4}, so its missing singleton colours are1and2; sharing can occur only at f1or f2.

For a singleton with d heavy neighbours of total support weight w, BC=J forces5−w singleton neighbours. Its total degree7 minus one high neighbour then leaves1+w−d empty neighbours. Thus an unshared fi has2 empty neighbours, and a shared C/F singleton has3. Since all fi share F, their empty-neighbour sets are pairwise disjoint, or two would share both F and an empty and form C4.

There are exactly three possible profiles: no C/F shared singleton gives five disjoint2sets covering10 of12 empties; sharing at f1or f2 gives one3set and four2sets covering11. This is a necessary universal core44 constraint independent of singleton mutual edges. It is not a contradiction, class exclusion or kernel theorem. The small check.py audit verifies core supports and the three profiles without completion search. Independent review pending.
