"""Check a frozen export with independent kernels in separate sandboxes."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json, subprocess, time


def collect_checks(checks, *, workers, logs):
    """Join every check; an explicit rejection takes precedence over resource errors."""
    logs.mkdir(parents=True, exist_ok=True)
    def run(name, check):
        started = time.monotonic()
        print(f'Start {name}', flush=True)
        try:
            result = check()
        except Exception as error:
            (logs/(name+'.log')).write_text(str(error))
            return error
        (logs/(name+'.log')).write_text(result.stdout+'\n'+result.stderr)
        print(f'Finished {name} in {time.monotonic()-started:.1f}s (exit {result.returncode})', flush=True)
        return result
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {name: pool.submit(run, name, check) for name, check in checks.items()}
        results = {name: future.result() for name, future in futures.items()}
    failures = [r for r in results.values() if isinstance(r, subprocess.CompletedProcess) and r.returncode != 0]
    errors = [r for r in results.values() if isinstance(r, Exception)]
    if errors and not failures:
        raise errors[0]
    stdout, stderr = [], []
    for name, result in results.items():
        if isinstance(result, Exception):
            stderr.append(f'{name}: {result}')
        else:
            stdout.append(f'{name}:\n{result.stdout}')
            stderr.append(f'{name}:\n{result.stderr}')
    return subprocess.CompletedProcess(['parallel-kernel-checks'], 1 if failures else 0,
                                       '\n'.join(stdout), '\n'.join(stderr))


def judge_exports(v, *, config, challenge_export, solution_export, scratch,
                  bundled, lean_prefix, environment, tools, capacity, timeout):
    workers = capacity['kernel_jobs']
    if workers == 1:
        # Parallel checks each get this allowance; serial Comparator needs their sum.
        # Palomar still caps the combined process by the shared replay deadline.
        return v.judge_exports(lake=bundled['lake'], config=config,
            challenge_export=challenge_export, solution_export=solution_export,
            scratch=scratch, bwrap=v._BWRAP, lean_prefix=lean_prefix,
            environment=environment, tools=tools,
            timeout=timeout * (1 + len(v.protected_kernels(bundled))))
    scratch.mkdir(parents=True)
    # Comparator owns statement/axiom comparison and the default Lean replay.
    # The other two checks consume the identical frozen solution export.
    original = json.loads(config.read_text())
    lean_config = scratch/'comparator-lean.json'
    lean_config.write_text(json.dumps({**original, 'external_kernels': {}}))
    checks = {'Lean default': lambda: v.judge_exports(
        lake=bundled['lake'], config=lean_config, challenge_export=challenge_export,
        solution_export=solution_export, scratch=scratch/'lean', bwrap=v._BWRAP,
        lean_prefix=lean_prefix, environment=environment, tools=tools, timeout=timeout)}
    for name, command in v.protected_kernels(bundled).items():
        if name == 'con-ron':
            command = [command[0], f"--jobs={max(1, min(2, capacity['threads'] // workers))}"]
        directory = scratch/name
        directory.mkdir()
        config_path = directory/'kernel.json'
        config_path.write_text(json.dumps({
            'use_stdin': False, 'export_file_path': str(solution_export),
            'permitted_axioms': original['permitted_axioms'],
            'unpermitted_axiom_hard_error': False,
            'num_threads': max(1, min(4, capacity['threads'] // workers)),
            'nat_extension': True, 'string_extension': True,
        }))
        args = [*command, str(config_path if name == 'nanoda' else solution_export)]
        def check(name=name, args=args, directory=directory, config_path=config_path):
            result = v.sandboxed_run(args, cwd=directory,
                environment={'PATH': str(lean_prefix/'bin')+':/usr/bin:/bin',
                             'HOME': str(directory), 'TMPDIR': str(directory),
                             'LANG': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1'},
                writable_directories=[directory],
                readable_paths=[config_path, solution_export, *v.system_readable_paths()],
                executable_paths=[lean_prefix, Path('/usr')], tools=tools, timeout=timeout, check=False)
            message = f'{name} kernel accepts the solution' if result.returncode == 0 else f'{name} kernel rejected the solution'
            return subprocess.CompletedProcess(args, result.returncode,
                                               result.stdout+'\n'+message, result.stderr)
        checks[name] = check
    limits = v.VERIFICATION_LIMITS
    # All simultaneous checkers together stay within the serial memory budget.
    v.VERIFICATION_LIMITS = {**limits,
        'memory_high_percent': max(1, limits['memory_high_percent'] // workers),
        'memory_max_percent': max(1, limits['memory_max_percent'] // workers)}
    try:
        return collect_checks(checks, workers=workers, logs=scratch/'logs')
    finally:
        v.VERIFICATION_LIMITS = limits
