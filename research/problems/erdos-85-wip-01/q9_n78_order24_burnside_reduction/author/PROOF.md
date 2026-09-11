# Order24 automorphism groups: seven or eight orbits and a normal-Sylow equality case

Let G be simple, C4-free and nine-regular on78 vertices, and suppose A=Aut(G) has order24. Accepted2357 gives at least seven vertex orbits. Accepted2257 gives at most six fixed vertices for every involution, accepted2207/2332 gives zero or three for every nonidentity order3 element, and accepted2315 bounds every vertex stabilizer by8. We derive necessary conditions without assuming any pending order48 result.

Every nonidentity element fixes at most six vertices, by taking a prime-order power. Let s be the number of Sylow3 subgroups. Then s is1 or4, and2s elements have order3. Burnside gives

    24r <= 78 + (23-2s)*6 + (2s)*3 =216-6s.

For either s, integrality yields r<=8. Thus r is7 or8.

## A normal Sylow3 subgroup is free

Suppose s=1 and P is the normal order3 subgroup. Its fixed set is A-invariant and has size0 or3. If a vertex were fixed, its A stabilizer would contain P, have order divisible by3 and be at most8. Its order would therefore be3 or6. Its A orbit would have size8 or4, too large to lie in a three-element invariant set. Hence P fixes no vertex.

Let C=C_A(P). Conjugation into Aut(C3) shows |C| is12 or24. Its central P and a Sylow2 subgroup T commute and have coprime orders; their product has all of C. Thus C=P times T. For each t in T and each nonidentity rho in P, rho*t has a nonidentity P power and fixes no vertex. There are2|T| such distinct elements.

If |C|=24, there are16 such fixed-point-free elements, and Burnside gives24r<=78+(23-16)*6=120, contrary to r>=7. Therefore |C|=12 and |T|=4. There are eight such elements, so

    24r <=78+(23-8)*6=168.

Together with r>=7, this forces equality and r=7. Every one of the other fifteen nonidentity elements fixes exactly six vertices. The eight fixed-point-free elements are precisely C minus T, namely the elements with nontrivial P component. Thus the fixed-point distribution is forced: identity78, eight elements0, fifteen elements6.

These conclusions also force conjugation A->Aut(P) to be surjective. No particular isomorphism type of T or of A, and no graph realization or exclusion, is inferred.

## Four Sylow3 subgroups

For s=4 the initial Burnside bound is24r<=192, so r=7 or8. If r=8, equality holds term by term: all eight order3 elements fix three vertices, and all fifteen remaining nonidentity elements fix six vertices. In particular A has no element whose order is divisible by6: such an element has a nonidentity order3 power and fixes at most three vertices, contradicting the equality requirement.

If r=7, that equality distribution is not asserted. The normal-Sylow and four-Sylow cases together exhaust all order24 groups.

This restricts full automorphism actions on N78 candidates. It excludes neither normal-Sylow nor four-Sylow order24 groups, and says nothing new about smaller groups, N78 existence, N80 or Erdős85. No finite search or Lean formalization is used.
