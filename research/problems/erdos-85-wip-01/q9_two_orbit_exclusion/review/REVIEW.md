# Review 2139: PASS

Independent local count: fix u in the first m-vertex orbit. Its x neighbors in the other orbit each have x-1 additional neighbors in the first orbit. These x(x-1) endpoints must be distinct, because a repeated endpoint supplies two common neighbors with u and hence a C4. Thus x(x-1)<=m-1, even without counting internal-center paths.

For a cyclic internal graph, any three distinct nonzero symmetric shifts include distinct noninverse u,v. The four vertices 0,u,u+v,v are distinct and have all four cycle edges. Hence an internal C4-free circulant has degree at most two, including even m and possible involution shifts. Minimum degree nine therefore forces x>=7.

For N80/m40, 42<=x(x-1)<=39 is impossible. This accepts the requested class exclusion without a regularity assumption, graph enumeration, SAT call, or Lean theorem.

The identical verified argument also excludes the authorized N78/m39 class, since 42>38. It does not exclude other N80/N78 action classes. N48/m24/d7 is not excluded because 20<=23.
