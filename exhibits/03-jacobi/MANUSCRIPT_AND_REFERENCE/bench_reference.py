"""Timing of independent Fraction mirror only, not Lean and not a method claim."""
import json, time
from exact_certificate_reference import produce
from fractions import Fraction
from pathlib import Path
rows=[]
for n in (3,10,50,160):
 for eps in ('1/32','1/1099511627776'):
  inp={'n':n,'diag':['0']*n,'hop':['1']*(n-1),'target':('7/5' if n==3 else '0'), 'tolerance':eps}
  t=time.perf_counter(); out=produce(inp); elapsed=time.perf_counter()-t
  row={'n':n,'tolerance':eps,'status':out['status'],'fuel':out.get('fuel'),
   'elapsed_python_s':round(elapsed,5),'lower':out.get('independent_checker_verdict',{}).get('lower'),
   'upper':out.get('independent_checker_verdict',{}).get('upper'),
   'width':out.get('independent_checker_verdict',{}).get('width')}
  rows.append(row)
  print('n',n,'eps',eps,'status',row['status'],'fuel',row['fuel'],'seconds',row['elapsed_python_s'])
Path('/mnt/data/aster_jacobi_manuscript_r0005/python_reference_benchmark.json').write_text(json.dumps({'warning':'These are timings of the independent Python Fraction mirror, NOT of the Lean implementation.','results':rows},indent=2)+'\n')
