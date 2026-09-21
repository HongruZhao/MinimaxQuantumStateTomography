#!/bin/bash
#SBATCH --job-name=fair100-plots
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:10:00
#SBATCH --output=logs/render_%j.out
#SBATCH --error=logs/render_%j.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/fair_solver_comparison_100reps_2026-09-09
module load python/3.10.9_anaconda2023.03_libmamba
export MPLCONFIGDIR=/tmp/minimax-matplotlib
python plot_results.py
