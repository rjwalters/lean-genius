import boto3,csv,json,hashlib,concurrent.futures,datetime
from pathlib import Path
out=Path(__file__).parent
base=Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49')
source=base/'audits/h1-live-revalidation-20260908.noindex/coverage.tsv'
rows=list(csv.DictReader(source.open(),delimiter='\t'));assert len(rows)==13351
s=boto3.Session(profile_name='2am-admin').client('s3');bucket='2am-erdos85-certs';prefix='sat49/campaign-20260825/'
def listing(p):
 return [x for page in s.get_paginator('list_objects_v2').paginate(Bucket=bucket,Prefix=prefix+p) for x in page.get('Contents',[])]
objects=listing('h1/');present={Path(x['Key']).name.split('.')[0] for x in objects if x['Key'].endswith('.compact.lrat.gz') and x['Size']>0}
prior={r['tag'] for r in rows if r['certificate_ledger_valid']=='1' and r['tag'] in present}
candidate={r['tag'] for r in rows}-prior
items=listing('h1-fleet-v3/ledger/')+listing('h1-fleet-v2/ledger/')
selected=[x for x in items if Path(x['Key']).stem in candidate]
def get(x):
 raw=s.get_object(Bucket=bucket,Key=x['Key'])['Body'].read().decode();return {'key':x['Key'],'raw':raw,'sha256':hashlib.sha256(raw.encode()).hexdigest()}
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as e: fresh=list(e.map(get,selected))
valid={};verdicts={}
for x in fresh:
 fields=x['raw'].split();tag=Path(x['key']).stem;a=dict(f.split('=',1) for f in fields if '=' in f)
 verdict='UNSAT' if 'UNSAT' in fields else 'UNKNOWN'
 verdicts.setdefault(tag,[]).append({'verdict':verdict,'rc':a.get('rc'),'cnf_sha256':a.get('cnf_sha256'),'key':x['key']})
 if verdict=='UNSAT' and a.get('rc')=='20' and a.get('trim')=='VERIFIED' and a.get('compact')=='ok' and a.get('upload','').startswith('uploaded') and tag in present:valid[tag]=x['key']
remaining=[dict(r, fresh_verdicts=verdicts.get(r['tag'],[])) for r in rows if r['tag'] not in prior and r['tag'] not in valid]
result={'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'total':len(rows),'present_objects':len(present),'prior_screened_present':len(prior),'fresh_screened':len(valid),'remaining':len(remaining),'fresh_ledger_count':len(fresh),'scope':'Producer screening only; no proof readback. Remaining is conservative relative to retained Sep08 screened rows and fresh candidate ledgers.'}
(out/'h1-refresh-summary.json').write_text(json.dumps(result,indent=2)+'\n')
(out/'h1-fresh-ledgers.json').write_text(json.dumps(fresh,indent=2)+'\n')
(out/'h1-remaining.json').write_text(json.dumps(remaining,indent=2)+'\n')
(out/'h1-object-list.json').write_text(json.dumps(objects,default=str,indent=2)+'\n')
print(json.dumps(result))
