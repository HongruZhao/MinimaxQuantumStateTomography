#!/bin/bash
#SBATCH --job-name=mwfw-timed-pilot
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --constraint=milan
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=12G
#SBATCH --time=02:00:00
#SBATCH --output=logs/timed_%A_%a.out
#SBATCH --error=logs/timed_%A_%a.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/mw_pls_fw_benchmark_2026-09-10
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
export MKL_DYNAMIC=FALSE OMP_PROC_BIND=TRUE OMP_PLACES=cores PYTHONUNBUFFERED=1
srun --cpu-bind=cores python benchmark_mw.py timed_pilot.json "$SLURM_ARRAY_TASK_ID"
