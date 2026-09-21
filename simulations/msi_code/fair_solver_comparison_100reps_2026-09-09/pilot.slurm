#!/bin/bash
#SBATCH --job-name=fair-pilot
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --constraint=milan
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=8G
#SBATCH --time=00:20:00
#SBATCH --output=logs/pilot_%j.out
#SBATCH --error=logs/pilot_%j.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/fair_solver_comparison_100reps_2026-09-09
module load python/3.10.9_anaconda2023.03_libmamba
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
export MKL_DYNAMIC=FALSE OMP_PROC_BIND=TRUE OMP_PLACES=cores PYTHONUNBUFFERED=1
srun --cpu-bind=cores python check_solver.py
srun --cpu-bind=cores /projects/standard/galin/shared/hongru/Clifford_Minimax/.venv-qiskit/bin/python generate_data.py 20 --only-n4
srun --cpu-bind=cores python pilot.py
