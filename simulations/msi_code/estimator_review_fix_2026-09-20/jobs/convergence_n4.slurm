#!/bin/bash
#SBATCH --job-name=tom-convergence_n4
#SBATCH --time=02:00:00
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --constraint=milan
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=8G
#SBATCH --output=logs/%x_%A_%a.out
#SBATCH --error=logs/%x_%A_%a.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/estimator_review_fix_2026-09-20
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
export MKL_DYNAMIC=FALSE OMP_PROC_BIND=TRUE OMP_PLACES=cores PYTHONUNBUFFERED=1
srun --cpu-bind=cores python src/run_convergence.py configs/convergence_n4.json "$SLURM_ARRAY_TASK_ID"
