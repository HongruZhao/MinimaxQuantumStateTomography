"""Portable metadata and atomic JSON writing; no solver dependencies."""
import json
import os
from pathlib import Path
import platform


def save_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')
    temporary.replace(path)


def hardware():
    import numpy
    import scipy
    try:
        from threadpoolctl import threadpool_info
        pools = threadpool_info()
    except ImportError:
        pools = 'threadpoolctl unavailable; numerical routines are unchanged'
    return dict(host=platform.node(), python=platform.python_version(),
                numpy=numpy.__version__, scipy=scipy.__version__, threadpools=pools,
                slurm_job_id=os.environ.get('SLURM_JOB_ID'),
                slurm_array_task_id=os.environ.get('SLURM_ARRAY_TASK_ID'))
