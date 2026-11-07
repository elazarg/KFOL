#!/usr/bin/env python3
"""Ten fixed checks of the one-neutral-constraint identity compilers.

Standard library only; no repository imports or saved algebra tables.
Two independent exhaustive evaluations are compared:
 (1) the atomic CSP on the occurring labelled atoms together with n;
 (2) the actual compiled identity on full D_K and every proper D_R.
The compiler builds a literal reset AST from join and all K choices.
No term search is performed. Thirty-second terminal wall-time cap.
"""
from itertools import product,combinations
import json,signal,time

V=lambda i: ('v',i)
J=lambda a,b: ('+',a,b)
H=lambda i,a,b: ('h',i,a,b)
x,y,z=map(V,range(3))
CASES=[
 ('basic_unsat', x, [(0,H(0,x,y)),(1,H(1,x,y))], False, (3,4)),
 ('basic_sat', x, [(0,y),(1,z)], True, (3,4)),
 ('join_source_sat', J(x,y), [(0,H(0,x,y)),(1,H(1,x,y))], True, (3,4)),
 ('mixed_absorption_unsat', H(0,x,H(1,x,y)),
     [(0,H(0,x,z)),(1,H(1,x,z))], False, (3,4)),
 ('foreign_join_sat', H(2,x,y), [(0,x),(1,y)], True, (3,4)),
 ('foreign_arm_unsat', x, [(0,H(2,x,y)),(1,z)], False, (3,4)),
 ('foreign_source_mixed_sat', H(2,H(0,x,y),H(1,x,z)),
     [(0,H(0,x,y)),(1,H(1,x,z))], True, (3,4)),
 ('two_foreign_arms_unsat', x,
     [(0,H(0,x,H(3,y,z))),(1,H(1,x,H(2,y,z)))], False, (4,)),
 ('one_owner_sat', x, [(0,y)], True, (3,4)),
 ('one_owner_unsat', x, [(0,x)], False, (3,4)),
]

def variables(t):
 if t[0]=='v':return {t[1]}
 a,b=t[-2:];return variables(a)|variables(b)

def build_native(K,owners):
 # Global labels: atoms are0..K-1, n=K and p=K+1.
 carrier=tuple(owners)+(K,K+1)
 def join(a,b):
  if a==b:return a
  if K+1 in(a,b):return K+1
  return K
 add={(a,b):join(a,b) for a,b in product(carrier,repeat=2)}
 choices=[{(a,b):(i if i in(a,b) else join(a,b))
           for a,b in product(carrier,repeat=2)} for i in range(K)]
 return carrier,add,choices

def evaluate(t,values,add,choices):
 if t[0]=='v':return values[t[1]]
 if t[0]=='+':return add[evaluate(t[1],values,add,choices),evaluate(t[2],values,add,choices)]
 return choices[t[1]][evaluate(t[2],values,add,choices),evaluate(t[3],values,add,choices)]

def compile_identity(K,q,arms,fresh,guarded=False):
 # pi_p(q): first p+q, then each translation h_i(q,-) once.
 reset=J(V(fresh),q)
 for i in range(K):reset=H(i,q,reset)
 summands=[H(i,reset,t) for i,t in arms]
 rhs=summands[0]
 for t in summands[1:]:rhs=J(rhs,t)
 if guarded:rhs=J(q,rhs)
 return J(reset,rhs),rhs,reset

def atomic_csp(K,q,arms,nvars):
 # Rebuild atomic operations separately from the native reset evaluator.
 atoms=tuple(sorted({i for i,_ in arms}))+(K,)
 def atom_join(a,b):return a if a==b else K
 def ev(t,v):
  if t[0]=='v':return v[t[1]]
  a,b=ev(t[-2],v),ev(t[-1],v)
  if t[0]=='+':return atom_join(a,b)
  owner=t[1];return owner if owner in(a,b) else atom_join(a,b)
 witness=None;checks=0
 for v in product(atoms,repeat=nvars):
  checks+=1
  good=ev(q,v)==K and all(ev(t,v)==i for i,t in arms)
  if good and witness is None:witness=v
 return witness,checks

def check_native_identity(K,R,lhs,rhs,reset,q,arms,nvars):
 carrier,add,ops=build_native(K,R);failure=None;checks=0
 for v in product(carrier,repeat=nvars+1):
  checks+=1
  lv=evaluate(lhs,v,add,ops);rv=evaluate(rhs,v,add,ops)
  if lv!=rv and failure is None:
   failure=dict(values=v,left=lv,right=rv,L=evaluate(reset,v,add,ops),
                q=evaluate(q,v,add,ops),arms=[evaluate(t,v,add,ops) for _,t in arms])
 return failure,checks

def main():
 start=time.monotonic();signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('30-second terminal cap')));signal.alarm(30)
 results=[];total_csp=total_full=total_proper=0;case_owner_instances=0
 for name,q,arms,expected,ks in CASES:
  used=variables(q)
  for i,t in arms:used|=variables(t)
  labels={i for i,_ in arms};assert labels in({0},{0,1})
  nvars=max(used)+1;assert used==set(range(nvars));fresh=nvars
  for K in ks:
   case_owner_instances+=1
   assert all(i<K for i,_ in arms)
   assert fresh not in variables(q) and all(fresh not in variables(t) for _,t in arms)
   witness,csp_count=atomic_csp(K,q,arms,nvars);sat=witness is not None;assert sat==expected
   total_csp+=csp_count
   for guarded in ((False,True) if len(labels)==2 else (True,)):
    lhs,rhs,reset=compile_identity(K,q,arms,fresh,guarded)
    full,full_count=check_native_identity(K,tuple(range(K)),lhs,rhs,reset,q,arms,nvars)
    proper=[];proper_count=0
    for size in range(K):
     for R in combinations(range(K),size):
      failure,count=check_native_identity(K,R,lhs,rhs,reset,q,arms,nvars)
      proper.append(dict(owners=R,valid=failure is None,first_failure=failure,valuations=count));proper_count+=count
    assert (full is None)==(not sat)
    assert all(row['valid'] for row in proper)==(not sat)
    if sat:
     # Explicit semantic direction: keep the atomic assignment, set fresh p=P.
     carrier,add,ops=build_native(K,tuple(sorted(labels)));v=tuple(witness)+(K+1,)
     assert evaluate(reset,v,add,ops)==K+1
     assert evaluate(rhs,v,add,ops)==K
     assert evaluate(lhs,v,add,ops)==K+1
    results.append(dict(case=name,K=K,guarded=guarded,q=q,arms=arms,ordinary_variables=nvars,fresh_p=fresh,
        csp_satisfiable=sat,csp_witness=witness,csp_valuations=csp_count,
        full_native_valid=full is None,full_first_failure=full,full_valuations=full_count,
        proper_native=proper,proper_valuations=proper_count))
    total_full+=full_count;total_proper+=proper_count
 # The local bit argument does not require the old neutral term to be lower:
 # every basic operation inside a fixed nonowned base fiber is Boolean OR.
 reset_bit_checks=0
 for K,b in product((3,4),(0,1)):
  accumulator=1|b
  for _ in range(K):accumulator=b|accumulator
  assert accumulator==1;reset_bit_checks+=1
 out=dict(status='PASS',fixed_cases=len(CASES),case_owner_instances=case_owner_instances,identity_instances=len(results),
          atomic_csp_valuations=total_csp,full_native_valuations=total_full,
          all_proper_native_valuations=total_proper,neutral_input_bit_checks=reset_bit_checks,
          cases=results,seconds=time.monotonic()-start,
          scope='Fixed compiler instances only; no term search or finite-basis claim. Unguarded instances use both labels; guarded instances allow one. Fresh p is absent from q and all labelled terms.')
 signal.alarm(0)
 print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
if __name__=='__main__':main()
