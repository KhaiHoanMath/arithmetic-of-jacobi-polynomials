"""Run the published finite verifications from any working directory."""

from pathlib import Path
import subprocess
import sys


CHECKS = (
    'check_manuscript_examples.py',
    'check_cutoff_constants.py',
    'check_legendre_small.py',
    'check_derivative_newton.py',
    'appendix_c.py',
    'check_factor_degrees.py',
    'check_galois_ranges.py',
    'appendix_b.py',
    'check_appendix_b_independent.py',
    'check_kaneko_zagier_irreducibility.py',
)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so that all assertions are checked.')
    from importlib.util import find_spec
    if find_spec('flint') is None:
        raise SystemExit('Install python-flint first (tested with python-flint==0.9.0).')
    directory = Path(__file__).resolve().parent
    for name in CHECKS:
        print(f'Running {name}', flush=True)
        subprocess.run([sys.executable, str(directory / name)], check=True)
    generator = directory / 'generate_derivative_certificates.py'
    print('Checking the generated Lean certificates', flush=True)
    subprocess.run([sys.executable, str(generator), '--check'], check=True)
    print(f'All {len(CHECKS)} verification programs and certificate regeneration passed.')
