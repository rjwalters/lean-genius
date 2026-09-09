# Bounded ECM attempt on the composite 127-digit cofactor of the odd part of det M.
import json, sys, time
from sympy.ntheory import ecm, isprime
c = 3824599876041302297803151167150579386117788109059339271116216677888376338297534342806287918240771309973777303534155812716671
t=time.time(); out={"cofactor": str(c), "isprime": isprime(c)}
try:
    fs = ecm(c, B1=100000, B2=10000000, max_curve=60)
    out["ecm_factors"] = {str(f): isprime(f) for f in fs}
except Exception as e:
    out["ecm_error"] = repr(e)
out["time_s"]=round(time.time()-t,1)
json.dump(out, open("ecm_cofactor.json","w"), indent=1); print(out)
