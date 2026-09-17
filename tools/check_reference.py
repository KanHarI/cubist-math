#!/usr/bin/env python3
"""Regenerate checked C proof traces and compare the upstream-verified fixture."""
import difflib
import os
import subprocess
import tempfile
from pathlib import Path

root=Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory() as tmp:
    trace=Path(tmp)/'actual.txt'
    env={**os.environ,'TT_TRACE_FILE':str(trace)}
    subprocess.run([str(root/'build/test')],env=env,check=True)
    expected=(root/'tests/reference_trace.txt').read_text().splitlines(True)
    actual=trace.read_text().splitlines(True)
    if actual!=expected:
        print(''.join(list(difflib.unified_diff(expected,actual,fromfile='reference',tofile='actual'))[:100]))
        raise SystemExit('Proof trace differs from upstream-verified reference')
    print(f'Reference trace: {len(actual)} checked inference records match')
