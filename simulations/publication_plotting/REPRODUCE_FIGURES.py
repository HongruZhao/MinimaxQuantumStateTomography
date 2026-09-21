"""Regenerate all four published comparison figures from bundled summaries."""
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
for name in ['plot_main_figures.py','plot_block_figure.py','plot_supplement_comparison.py']:
    subprocess.run([sys.executable,str(root/name)],cwd=root,check=True)
