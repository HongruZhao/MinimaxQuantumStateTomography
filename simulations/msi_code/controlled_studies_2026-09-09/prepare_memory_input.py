import sys
from pathlib import Path
import numpy as np
task=int(sys.argv[1]);n=[4,6,8,10][task//2]
base=Path('/projects/standard/galin/shared/hongru/Clifford_Minimax')
if n==8:
    b=np.load(base/'T_sweep_n8_k2_2026-09-09/results/rep_00/data.npz')['means'][2]
else:
    b=np.load(base/f'controlled_studies_2026-09-09/results/rep_00/n{n}_k2/data.npz')['mean']
out=Path('memory_inputs');out.mkdir(exist_ok=True)
np.save(out/f'task_{task}.npy',b)
