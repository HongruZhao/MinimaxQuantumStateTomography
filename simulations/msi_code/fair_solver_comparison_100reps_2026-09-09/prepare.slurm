#!/bin/bash
#SBATCH --job-name=fair-inputs
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:05:00
#SBATCH --output=logs/prepare_%j.out
#SBATCH --error=logs/prepare_%j.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/fair_solver_comparison_100reps_2026-09-09
module load python/3.10.9_anaconda2023.03_libmamba
python prepare_memory.py
