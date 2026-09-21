#!/bin/bash
#SBATCH --job-name=mwfw-integrity
#SBATCH --account=galin
#SBATCH --partition=agsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH --output=logs/final_integrity_%j.out
#SBATCH --error=logs/final_integrity_%j.err
set -euo pipefail
cd /projects/standard/galin/shared/hongru/Clifford_Minimax/mw_pls_fw_benchmark_2026-09-10
module load python/3.10.9_anaconda2023.03_libmamba
python monitoring/final_integrity.py verify --root . --manifest reports_final_2026-09-11/MANIFEST.json --output reports_final_2026-09-11/integrity_msi.json
