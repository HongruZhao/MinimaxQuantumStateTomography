#!/bin/bash
#SBATCH --job-name=mwfw-plots
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH --output=logs/render_%j.out
#SBATCH --error=logs/render_%j.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/mw_pls_fw_benchmark_2026-09-10
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 MPLCONFIGDIR=/tmp/minimax-matplotlib
python summarize.py --allow-partial
