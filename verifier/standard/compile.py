"""Compile a module DAG with separate writable state for each compiler process."""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import shutil


def compile_modules(order, dependencies, compile_one, *, jobs, is_memory_error=lambda error: False):
    pending = set(order)
    if len(pending) != len(order) or set(dependencies) != pending:
        raise ValueError('Invalid module build graph')
    if any(not set(deps) <= pending for deps in dependencies.values()):
        raise ValueError('Missing build dependency')
    done, running, retries = set(), {}, []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running or retries:
            if retries:
                # Drain active compilers before giving a large module the whole
                # existing memory budget. Its dependents remain blocked.
                if not running:
                    name = retries.pop(0)
                    running[pool.submit(compile_one, name, jobs)] = (name, jobs)
            else:
                available = jobs - sum(threads for _, threads in running.values())
                ready = [name for name in order if name in pending and set(dependencies[name]) <= done]
                slots = min(available, len(ready))
                for index, name in enumerate(ready[:slots]):
                    threads = available // (slots - index)
                    running[pool.submit(compile_one, name, threads)] = (name, threads)
                    available -= threads
                    pending.remove(name)
            if not running:
                raise ValueError('Cyclic module build graph')
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed:
                name, threads = running.pop(future)
                try:
                    future.result()
                except Exception as error:
                    if threads == jobs or not is_memory_error(error):
                        raise
                    print(f'Memory limit reached for {name}; retrying alone after active compilers finish', flush=True)
                    retries.append(name)
                else:
                    done.add(name)


def publish_module(output, destination):
    # The sandbox supervisor has reaped the compiler and all descendants.
    # Copy only regular compiler products for this module into the read-only
    # dependency library presented to subsequent compiler processes.
    if not output.is_file() or output.is_symlink():
        raise ValueError('Compiler did not produce a regular olean')
    destination.parent.mkdir(parents=True, exist_ok=True)
    for suffix in ['', '.private', '.server']:
        product = Path(str(output) + suffix)
        if product.is_symlink():
            raise ValueError('Symlink compiler output')
        if product.exists():
            if not product.is_file():
                raise ValueError('Invalid compiler output')
            target = Path(str(destination) + suffix)
            if target.exists():
                raise ValueError('Duplicate compiler output')
            shutil.copyfile(product, target)
            target.chmod(0o444)
