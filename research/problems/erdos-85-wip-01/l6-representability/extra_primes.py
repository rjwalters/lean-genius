# Complete step 5 at the four primes obtained by ECM from the composite cofactor C127.
import json, sys, hashlib
sys.argv=[sys.argv[0], 'results.json', '--crosscheck']   # prevent l6probe.main()
import importlib.util
spec=importlib.util.spec_from_file_location('l6','l6probe.py'); l6=importlib.util.module_from_spec(spec); spec.loader.exec_module(l6)
from sympy import isprime
ecm=json.load(open('ecm_cofactor.json'))
ps=[int(p) for p in ecm['ecm_factors']]
C=int(ecm['cofactor']); assert all(isprime(p) for p in ps)
prod=1
for p in ps: prod*=p
assert prod==C, "ECM factors do not multiply back to the cofactor"
M,S=l6.build_M(16); n=len(M)
minors=l6.bareiss_minors(M)
dsq=[minors[0]]+[minors[k]*minors[k-1] for k in range(1,n)]
res={}
for p in ps:
    c1=l6.hasse_invariant(dsq,p)
    d=l6.jordan_padic_odd(M,p,6); c2=l6.hasse_from_padic_diag(d,p)
    vals=sorted(v for v,u in d)
    res[str(p)]={"c_p_minors_route":c1,"c_p_padic_jordan_route":c2,"p_part_valuations":{str(v):vals.count(v) for v in set(vals)}}
    print(p, c1, c2, res[str(p)]["p_part_valuations"])
r=json.load(open('results.json'))
r["cofactor_C127_factorisation"]={"C127":str(C),"primes":[str(p) for p in ps],"all_prime":True}
r["hasse_at_C127_primes"]=res
odd_all=[7,17,127,1871,36353,674565247]+ps
r["full_odd_part_prime_factorisation"]={str(p):2 for p in sorted(odd_all)}
r["odd_primes_with_c_p_minus_1"]=[str(p) for p in sorted(odd_all) if (r["hasse_invariants_M"].get(str(p)) if str(p) in r["hasse_invariants_M"] else res[str(p)]["c_p_minors_route"])==-1]
# product formula over all genuine places
prod=r["hasse_real"]*r["hasse_invariants_M"]["2"]
for p in odd_all:
    prod*= r["hasse_invariants_M"][str(p)] if str(p) in r["hasse_invariants_M"] else res[str(p)]["c_p_minors_route"]
r["hilbert_reciprocity_product_all_places"]=prod
r["extra_primes_script_sha256"]=hashlib.sha256(open('extra_primes.py','rb').read()).hexdigest()
json.dump(r,open('results.json','w'),indent=1)
print("primes with c_p=-1:", r["odd_primes_with_c_p_minus_1"], "reciprocity product:", prod)
