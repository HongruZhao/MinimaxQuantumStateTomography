#!/bin/bash
#SBATCH --job-name=render-controlled-plots
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:10:00
#SBATCH --output=logs/render_%j.out
#SBATCH --error=logs/render_%j.err
set -euo pipefail
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
export MPLCONFIGDIR=/tmp/clifford-plot-cache-${SLURM_JOB_ID}
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/T_sweep_n8_k2_2026-09-09
python plot_results.py > plot_summary.log
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/controlled_studies_2026-09-09
python plot_studies.py > controlled_plot_summary.log
