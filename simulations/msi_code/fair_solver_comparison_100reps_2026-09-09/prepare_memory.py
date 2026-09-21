from benchmark import CASES,HERE,load_input
import numpy as np
for rep in range(20):
 dest=HERE/'memory_inputs'/f'rep_{rep:03d}';dest.mkdir(parents=True,exist_ok=True)
 for index in [7,8,2,9]:
  case=CASES[index];b,_=load_input(case,rep);np.save(dest/f"n{case['n']}.npy",b);del b
