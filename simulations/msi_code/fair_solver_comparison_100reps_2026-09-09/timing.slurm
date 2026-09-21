#!/bin/bash
#SBATCH --job-name=fair100-timing
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --constraint=milan
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=12G
#SBATCH --time=02:00:00
#SBATCH --array=0-799%20
#SBATCH --output=logs/%A_%a.out
#SBATCH --error=logs/%A_%a.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/fair_solver_comparison_100reps_2026-09-09
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
export MKL_DYNAMIC=FALSE OMP_PROC_BIND=TRUE OMP_PLACES=cores PYTHONUNBUFFERED=1
srun --cpu-bind=cores python benchmark.py "$SLURM_ARRAY_TASK_ID"
