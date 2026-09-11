# Orbit sizes in the faithful order-sixteen branch

Assume the faithful alternative of accepted2422, under accepted2419. Then A=C2 x D8 acts faithfully on S=3K2 with orbit sizes2+4, H=D8 is the stabilizer of a vertex in the size-two orbit, and H acts freely outside S. Write j for the generator of the C2 factor. The invariant sets W and R have sizes48 and24, and outside S all A-orbits have size8 or16.

Every involution fixes at most six vertices by accepted2257. A central involution fixing any outside vertex would fix its entire A-orbit, since its fixed set is A-invariant. That orbit has size at least eight, a contradiction. Thus no central involution fixes any outside vertex.

An outside vertex stabilizer is trivial or has order two, and intersects H trivially. In the latter case its generator lies in jH and is an involution. Writing D8=<r,s | r^4=s^2=1, srs=r^-1>, the possibilities in jH are j, jr^2, or jr^k s for k=0,1,2,3. The first two are central and have just been excluded. The last four split into exactly two conjugacy classes, according to the parity of k, each of size two. The centralizer in A of each such involution has size eight.

For an outside orbit of size eight, write its stabilizer as K=<t> for one of these noncentral involutions. The number of points fixed by t in A/K is |C_A(t)|/|K|=8/2=4: a coset gK is fixed precisely when g^-1 t g belongs to K, and its only possible nonidentity value is t. The same holds for the conjugate involution in t's class. An involution from the other class fixes no point on this orbit.

Therefore there can be at most one size-eight outside orbit with stabilizer in each of the two classes. Otherwise an involution would fix at least eight vertices. In total the number a of size-eight outside orbits is at most two. The remaining orbits have size16, so72=8a+16b gives a+2b=9. Hence a is odd and necessarily a=1, b=4.

W is invariant and has size48, a multiple of16. Its number of size-eight orbits must be even, but there is only one such orbit in the entire complement of S. Thus W has no size-eight orbit and decomposes as16+16+16. The unique size-eight orbit lies in R, whose decomposition is8+16. Together with S-orbits2+4, the full action has exactly seven orbits, of sizes2,4,8,16,16,16,16.

This is a necessary restriction on the faithful C2 x D8 branch only. It does not exclude that branch, address the central-six-fixed alternative of2422, or prove graph existence/nonexistence. No finite graph search or Lean formalization is used.
