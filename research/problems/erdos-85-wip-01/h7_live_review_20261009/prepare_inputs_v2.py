"""Read-only cloud reconstruction of the pinned 394 canary v2 CNF identities.

No solver, checker, Lean, campaign import, or cloud mutation is invoked.
This prepares an expected-input ledger, not canary acceptance.
"""
import argparse,hashlib,json,platform
from pathlib import Path

INPUT_SHA='f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c'
LEAF_CUBES=['cube_F6_t14','cube_F6_t16','cube_F6_t18','cube_F7_t10','cube_F7_t13','cube_F8_t0','cube_F9_t0']
COVER_CUBES=['cube_F6_t14','cube_F7_t10']
BINS={'cadical':'fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2',
      'cake_lpr':'4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b'}
def sha(b):return hashlib.sha256(b).hexdigest()
def prepare(root):
    raw=(root/'inputs.json').read_bytes();assert sha(raw)==INPUT_SHA
    meta=json.loads(raw);assert meta['depth']==3 and meta['variables']==17633 and meta['canonical_clauses']==720804
    body=(root/'canonical.body').read_bytes()
    assert sha(body)==meta['canonical_body_sha256'] and body.count(b'\n')==720804
    batches={};files={'inputs.json':INPUT_SHA,'canonical.body':sha(body)}
    header=lambda count:f'p cnf 17633 {count}\n'.encode()
    for name in LEAF_CUBES:
        info=meta['cubes'][name];parts={e:(root/(name+'.'+e)).read_bytes() for e in ('units','hsb','cover')}
        for ext,b in parts.items():
            assert sha(b)==info[ext+'_sha256'];files[name+'.'+ext]=sha(b)
        assert parts['units'].count(b'\n')==21 and parts['hsb'].count(b'\n')==info['hsb_clauses']
        lines=parts['cover'].splitlines();assert len(lines)==info['leaves']>=64
        cube=body+parts['units'];hsb=cube+parts['hsb'];count=720825+info['hsb_clauses']
        assert sha(header(720825)+cube)==info['cube_cnf_sha256']
        assert sha(header(count)+hsb)==info['hsb_cnf_sha256']
        cover=header(count+len(lines))+hsb+parts['cover']
        assert sha(cover)==info['cover_cnf_sha256']
        if name in COVER_CUBES:
            batches[name+'-cover']=[{'cube':name,'kind':'cover','leaf':None,'cnf_sha256':sha(cover),'cnf_bytes':len(cover),'units':None}]
        prefix=header(count+info['leaf_units'])+hsb;prefix_hash=hashlib.sha256(prefix);rows=[]
        for leaf in (range(8) if name == 'cube_F6_t14' else range(1024,1088)):
            line=lines[leaf]
            lits=[int(x) for x in line.split()]
            assert lits[-1]==0 and len(lits)-1==info['leaf_units'] and all(-17633<=x<0 for x in lits[:-1])
            units=[-x for x in lits[:-1]];tail=''.join(f'{x} 0\n' for x in units).encode();h=prefix_hash.copy();h.update(tail)
            rows.append({'cube':name,'kind':'leaf','leaf':leaf,'cnf_sha256':h.hexdigest(),'cnf_bytes':len(prefix)+len(tail),'units':units})
        if name == 'cube_F6_t14':
            batches[name+'-h0000']=rows[:4]
            batches[name+'-h0001']=rows[4:8]
        else:
            batches[name+'-b0000']=rows
    assert len(batches)==10 and sum(map(len,batches.values()))==394
    for n,h in files.items():assert sha((root/n).read_bytes())==h,'Input changed during preparation: '+n
    return {'status':'CANARY_V2_INPUT_IDENTITIES_PREPARED','inputs_sha256':INPUT_SHA,'binaries':BINS,'depth':3,'cap_seconds':7200,'heap_mb':6000,'batches':batches,'input_file_sha256':files,'canary_verified':False,'full_campaign_verified':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--inputs',type=Path,required=True);p.add_argument('--output',type=Path);a=p.parse_args()
    assert platform.system()=='Linux','Actual formula-byte reconstruction runs on the cloud builder'
    result=prepare(a.inputs);raw=(json.dumps(result,indent=2)+'\n').encode()
    if a.output:
        with a.output.open('xb') as f:f.write(raw)
        print(json.dumps({'status':result['status'],'output_sha256':sha(raw),'batches':10,'items':394,'canary_verified':False}))
    else:print(raw.decode(),end='')
