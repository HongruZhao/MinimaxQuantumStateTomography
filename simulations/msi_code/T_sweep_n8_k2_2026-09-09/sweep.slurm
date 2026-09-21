#!/bin/bash
#SBATCH --job-name=T-sweep-n8-k2
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=8G
#SBATCH --time=01:00:00
#SBATCH --array=0-19%4
#SBATCH --output=logs/%A_%a.out
#SBATCH --error=logs/%A_%a.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/T_sweep_n8_k2_2026-09-09
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
export MKL_DYNAMIC=FALSE PYTHONUNBUFFERED=1
python run.py "$SLURM_ARRAY_TASK_ID"
