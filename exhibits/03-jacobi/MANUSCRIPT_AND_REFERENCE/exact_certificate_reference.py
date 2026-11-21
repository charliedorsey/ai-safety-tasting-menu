#!/usr/bin/env python3
"""Research cross-check only, NOT a substitute for the Lean producer/checker.

Exact Fraction mirror of the stated rational continuant, target-centered radial
certificate, and logarithmic fuel. No floating-point number influences results.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path


def fq(v):
    return str(Q(v))


def validate_input(data):
    n = data['n']
    d = [Q(v) for v in data['diag']]
    b = [Q(v) for v in data['hop']]
    tau = Q(data['target'])
    eps = Q(data['tolerance'])
    if not isinstance(n, int) or n < 1 or len(d) != n or len(b) != n-1 or any(v == 0 for v in b):
        return None, 'invalid_data'
    if eps <= 0:
        return None, 'invalid_tolerance'
    return (n,d,b,tau,eps), None


def continuants(d,b,x):
    n=len(d)
    p=[Q(1), x-d[0]]
    for k in range(n-1):
        p.append((x-d[k+1])*p[-1]-b[k]**2*p[-2])
    return p


def variations(vals):
    nz=[(1 if v>0 else -1) for v in vals if v != 0]
    return sum(a != b for a,b in zip(nz,nz[1:]))


def count(d,b,x):
    return variations(continuants(d,b,x))


def seed(d,b,tau):
    n=len(d)
    vals=continuants(d,b,tau)
    if vals[-1] == 0:
        return None
    C=[Q(1), abs(tau-d[0])+1]
    S=[Q(0), Q(1)]
    for k in range(n-1):
        C.append((abs(tau-d[k+1])+1)*C[-1]+abs(b[k])**2*C[-2])
        S.append(C[-2]+abs(tau-d[k+1])*S[-1]+abs(b[k])**2*S[-2])
    lo=min(Q(1,2), abs(vals[-1])/(2*(S[n]+1)))
    # The last padded hopping coefficient is canonically zero, not input data.
    out_budget=2*sum((abs(d[k])+(b[k]**2 if k<n-1 else Q(0))+2 for k in range(n)),Q(0))
    hi=lo+abs(tau)+out_budget+2
    return lo,hi,tuple(C[:n+1]),tuple(S[:n+1])


def ceiling_nonneg(x):
    if x <= 0: return 0
    return (x.numerator+x.denominator-1)//x.denominator


def log_fuel(width,eps):
    n=ceiling_nonneg(width/eps)
    return (n-1).bit_length() if n>0 else 0


def canonical_json(x):
    return json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=True)


def public_input(obj):
    return {k:obj[k] for k in ('n','diag','hop','target','tolerance')}


def check_certificate(obj):
    src=public_input(obj)
    t,err=validate_input(src)
    if err: return {'ok':False,'reason':err}
    n,d,b,tau,eps=t
    if obj['input_sha256'] != hashlib.sha256(canonical_json(src).encode()).hexdigest():
        return {'ok':False,'reason':'input commitment mismatch'}
    w=obj['witness']
    a,bb,c,dd=[Q(w[k]) for k in ('gap_left','gap_right','near_left','near_right')]
    if not (a < tau < bb and c<dd):
        return {'ok':False,'reason':'endpoint ordering failure'}
    counts={'gap_left':count(d,b,a),'gap_right':count(d,b,bb),
            'near_left':count(d,b,c),'near_right':count(d,b,dd)}
    L=min(tau-a,bb-tau)
    U=max(abs(c-tau),abs(dd-tau))
    ok=(counts['gap_left']==counts['gap_right'] and counts['near_left']>counts['near_right']
        and L>0 and L<=U and U-L<=eps)
    return {'ok':ok,'lower':fq(L),'upper':fq(U),'width':fq(U-L),
            'counts':counts,'accuracy':U-L<=eps,'eps':fq(eps)}


def produce(inp):
    parsed, err=validate_input(inp)
    if err:return {'status':err,'input':inp}
    n,d,b,tau,eps=parsed
    vals=continuants(d,b,tau)
    if vals[-1]==0:return {'status':'singular','input':inp,'characteristic_at_target':'0'}
    low,high,C,S=seed(d,b,tau)
    assert low>0 and low<high
    assert count(d,b,tau-low)==count(d,b,tau+low)
    assert count(d,b,tau+high)<count(d,b,tau-high)
    width=high-low
    fuel=log_fuel(width,eps)
    assert width/Q(2)**fuel<=eps
    trace=[]
    for i in range(fuel):
        middle=(low+high)/2
        left=count(d,b,tau-middle)
        right=count(d,b,tau+middle)
        if right<left: high=middle; action='occupied'
        else: low=middle; action='empty'
        trace.append({'step':i+1,'radius':fq(middle),'drop':left-right,'action':action})
    assert high-low<=eps
    src={**inp}
    out={'status':'regular',**src, 'input_sha256':hashlib.sha256(canonical_json(src).encode()).hexdigest(),
       'witness':{'gap_left':fq(tau-low),'gap_right':fq(tau+low),
                  'near_left':fq(tau-high),'near_right':fq(tau+high)},
       'initial_inner':fq(seed(d,b,tau)[0]),'initial_outer':fq(seed(d,b,tau)[1]),
       'fuel':fuel, 'trace':trace,
       'scope':'Independent exact Python mirror; Lean export and checker proof must be recorded separately.'}
    verdict=check_certificate(out)
    assert verdict['ok'],verdict
    out['independent_checker_verdict']=verdict
    return out


def test():
    samples=[
      ({'n':3,'diag':['0','0','0'],'hop':['1','1'],'target':'7/5','tolerance':'1/32'},'regular'),
      ({'n':3,'diag':['0','0','0'],'hop':['1','1'],'target':'0','tolerance':'1/32'},'singular'),
      ({'n':3,'diag':['0','0','0'],'hop':['1','0'],'target':'7/5','tolerance':'1/32'},'invalid_data'),
      ({'n':0,'diag':[],'hop':[],'target':'0','tolerance':'1/32'},'invalid_data'),
      ({'n':1,'diag':['0'],'hop':[],'target':'1','tolerance':'0'},'invalid_tolerance'),
      ({'n':1,'diag':['0'],'hop':[],'target':'1','tolerance':'1/4'},'regular'),
      ({'n':3,'diag':['0','0','0'],'hop':['-1','-1'],'target':'7/5','tolerance':'1/32'},'regular')]
    for inp,expected in samples:
        observed=produce(inp)
        assert observed['status']==expected,(inp,observed)
        if expected=='regular': assert check_certificate(observed)['ok']
    print('SELF-TEST',len(samples),'passed, exact rational only')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--self-test',action='store_true')
    parser.add_argument('--write-demo',type=Path)
    parser.add_argument('--check',type=Path)
    args=parser.parse_args()
    if args.self_test:test()
    if args.write_demo:
      v=produce({'n':3,'diag':['0','0','0'],'hop':['1','1'],'target':'7/5','tolerance':'1/32'})
      args.write_demo.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
      print('WROTE',args.write_demo,'fuel',v['fuel'],'verdict',v['independent_checker_verdict'])
    if args.check:
      obj=json.loads(args.check.read_text()); print('INDEPENDENT_CHECK',check_certificate(obj))
