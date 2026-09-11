"""Prepared singleton rows; use only on validated H/E/S-complete a7 inputs."""
import itertools

def pairings(xs):
 if not xs:yield ();return
 for j in range(1,len(xs)):
  for rest in pairings(xs[1:j]+xs[j+1:]):yield ((xs[0],xs[j]),)+rest

def prepare(adjacency):
 # Caller establishes the reviewed2109 preconditions. P-host assignment is
 # irrelevant to this plan; it may be reused for the same H/E/S structure.
 g=list(map(set,adjacency));H=set(range(7));support=[g[v]&H for v in range(49)];E={v for v in range(7,49) if not support[v]};S={v for v in range(7,49) if len(support[v])==1};P={tuple(sorted(support[v])):v for v in range(7,49) if len(support[v])==2};plan=[]
 for s in sorted(S):
  missing=[h for h in range(7) if not g[s]&g[h]];B=set()
  for e in g[s]&E:B|=g[e]&E
  for t in g[s]&S:B|=g[t]&E
  candidates=[tuple(P[e] for e in pm) for pm in pairings(missing)]
  assert len(candidates)=={4:3,6:15}[len(missing)]
  plan.append((s,sum(1<<e for e in B),candidates))
 return plan

def evaluate(plan,host_masks):
 # host_masks[p] is zero for an R pair, or 1<<e for its unique E host.
 rows={}
 for s,forbidden,candidates in plan:
  accepted=[]
  for vs in candidates:
   used=0
   for v in vs:
    host=host_masks[v]
    if host&(forbidden|used):break
    used|=host
   else:accepted.append(sum(1<<v for v in vs))
  rows[s]=accepted
 return rows
