#!/bin/bash
#SBATCH --job-name=estimator-memory
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=12G
#SBATCH --time=01:00:00
#SBATCH --array=0-7%4
#SBATCH --output=logs/memory_%A_%a.out
#SBATCH --error=logs/memory_%A_%a.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/controlled_studies_2026-09-09
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
export MKL_DYNAMIC=FALSE PYTHONUNBUFFERED=1
python prepare_memory_input.py "$SLURM_ARRAY_TASK_ID"
python memory_run.py "$SLURM_ARRAY_TASK_ID"
