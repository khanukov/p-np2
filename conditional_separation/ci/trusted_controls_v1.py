"""Pinned Python control admission/snapshot dispatch, never a build launcher.

The external, independently reviewed workflow supplies this file's SHA256.
The embedded manifest SHA authenticates the complete other-control roster.
Default --check only reads; --run executes an admitted control in this process.
No project object, compiler result or source-review acceptance follows.
"""
import sys
if sys.flags.optimize:
    raise SystemExit('optimized trusted controls rejected')
import hashlib
import importlib.abc
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import types

MANIFEST_SHA256 = '020cdc2e9196831b7182f9d011e3ab294d38a7c890ceb0634752abff3b655cd8'
MANIFEST = 'ci/TRUSTED_NATIVE_CONTROLS_V1.json'
SELF = 'ci/trusted_controls_v1.py'
WORKFLOW_DATA = 'ci/conditional-separation-native-v2.yml'
_ANCHOR = None
_PACKAGE = None


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read_snapshot(path):
    path = Path(path)
    require(path.is_absolute() and path.resolve(strict=True) == path,
            'literal physical control path')
    require(not any(p.is_symlink() or getattr(p, 'is_junction', lambda: False)()
                    for p in (path, *path.parents)), 'aliased control path')
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1,
            'regular single-link control')
    data = path.read_bytes()
    after = path.lstat()
    fields = ('st_dev', 'st_ino', 'st_mode', 'st_nlink', 'st_size', 'st_mtime_ns', 'st_ctime_ns')
    require(all(getattr(before, k) == getattr(after, k) for k in fields)
            and len(data) == before.st_size, 'control changed during read')
    return data


def manifest_rows(data, expected):
    require(type(expected) is str and re.fullmatch('[0-9a-f]{64}', expected), 'manifest anchor')
    require(hashlib.sha256(data).hexdigest() == expected, 'trusted manifest digest')
    def pairs(items):
        value = {}
        for key, item in items:
            require(key not in value, 'duplicate manifest key')
            value[key] = item
        return value
    value = json.loads(data, object_pairs_hook=pairs)
    require(type(value) is dict and set(value) == {'schema', 'seed_revision', 'files'}
            and value['schema'] == 'trusted-native-controls-v1', 'control manifest schema')
    require(value['seed_revision'] == '9c8e998457514fbf3f2dba5cc3a0edf362010571',
            'unchanged-body attribution seed')
    rows = value['files']
    require(type(rows) is list and 1 <= len(rows) <= 128, 'finite control roster')
    names = []
    for row in rows:
        require(type(row) is dict and set(row) == {'path', 'bytes', 'sha256'}, 'control pin schema')
        name = row['path']
        require(type(name) is str and re.fullmatch(r'[A-Za-z0-9_.+/-]+', name)
                and PurePosixPath(name).as_posix() == name and not name.startswith('/')
                and all(p not in {'.', '..'} for p in name.split('/')), 'control relative name')
        reserved = {'CON', 'PRN', 'AUX', 'NUL'} | {p + str(i) for p in ('COM', 'LPT') for i in range(1, 10)}
        require(all(not p.endswith(('.', ' ')) and p.split('.')[0].upper() not in reserved
                    for p in name.split('/')), 'portable control name')
        require(name not in {SELF, MANIFEST, WORKFLOW_DATA}, 'nonrecursive control roster')
        require(type(row['bytes']) is int and row['bytes'] >= 0
                and type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}', row['sha256']),
                'control pin type/size/hash')
        names.append(name)
    require(names == sorted(names) and len({n.casefold() for n in names}) == len(names),
            'ordered unique complete control names')
    return rows


def verify_controls(package, anchor):
    require(type(anchor) is str and re.fullmatch('[0-9a-f]{64}', anchor), 'external control anchor')
    require(hashlib.sha256(read_snapshot(Path(__file__).absolute())).hexdigest() == anchor,
            'external dispatcher digest')
    package = Path(package)
    require(package.is_absolute() and package.resolve(strict=True) == package, 'physical tested package')
    own = read_snapshot(package / SELF)
    require(hashlib.sha256(own).hexdigest() == anchor, 'tested dispatcher differs from trusted controller')
    rows = manifest_rows(read_snapshot(package / MANIFEST), MANIFEST_SHA256)
    snapshots = {SELF: own}
    for row in rows:
        raw = read_snapshot(package / row['path'])
        require(len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256'],
                'untrusted changed control: ' + row['path'])
        snapshots[row['path']] = raw
    wanted = set(snapshots) | {MANIFEST, WORKFLOW_DATA}
    actual = set()
    for name in ('ci', 'tools', 'tests'):
        root = package / name
        require(root.is_dir() and not root.is_symlink(), 'control directory')
        for parent, dirs, files in os.walk(root, followlinks=False):
            require(not dirs, 'unknown control directory, bytecode or alias')
            for file in files:
                path = Path(parent) / file
                read_snapshot(path)
                actual.add(path.relative_to(package).as_posix())
    require(actual == {n for n in wanted if n.split('/')[0] in {'ci', 'tools', 'tests'}},
            'complete control filename domain')
    python = set()
    for parent, dirs, files in os.walk(package, followlinks=False):
        dirs[:] = [d for d in dirs if not (Path(parent) == package and d == '.lake')]
        require(not any((Path(parent) / d).is_symlink() for d in dirs), 'source directory alias')
        python.update((Path(parent) / n).relative_to(package).as_posix() for n in files if n.endswith('.py'))
    require(python == {n for n in snapshots if n.endswith('.py')}, 'unknown/missing Python source')
    return snapshots


class SnapshotLoader(importlib.abc.Loader):
    def __init__(self, path, data):
        self.path, self.data = path, data

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        module.__file__ = str(self.path)
        exec(compile(self.data, str(self.path), 'exec'), module.__dict__)


def snapshot_spec(name, path, data):
    return _ORIGINAL_SPEC(name, str(path), loader=SnapshotLoader(path, data))


_ORIGINAL_SPEC = importlib.util.spec_from_file_location


class SnapshotFinder(importlib.abc.MetaPathFinder):
    def __init__(self, package, snapshots):
        self.paths = {str(package / n): data for n, data in snapshots.items() if n.endswith('.py')}
        self.modules = {Path(n).stem: (package / n, data) for n, data in snapshots.items() if n.endswith('.py')}
        require(len(self.modules) == len(self.paths), 'ambiguous control module stem')

    def find_spec(self, fullname, path=None, target=None):
        if fullname in self.modules:
            location, data = self.modules[fullname]
            return snapshot_spec(fullname, location, data)
        return None

    def file_spec(self, name, location=None, *, loader=None, submodule_search_locations=None):
        key = str(Path(location).absolute()) if location is not None else ''
        if key in self.paths:
            return snapshot_spec(name, Path(key), self.paths[key])
        return _ORIGINAL_SPEC(name, location, loader=loader,
                              submodule_search_locations=submodule_search_locations)


def require_control_context(package):
    require(_ANCHOR is not None and _PACKAGE == Path(package),
            'independently authenticated control dispatch required')
    return {'dispatcher_sha256': _ANCHOR, 'manifest_sha256': MANIFEST_SHA256}


def control_argv(package, argv):
    """Route existing owned Python children; no process creation or new reaper."""
    require_control_context(package)
    require(type(argv) is list and all(type(a) is str for a in argv), 'literal command argv')
    if not argv or argv[0] != sys.executable:
        return argv
    require(len(argv) >= 3 and argv[1] == '-B', 'registered Python control shape')
    path = Path(argv[2])
    package = Path(package)
    if not path.is_absolute():
        path = package / path
    base = package
    if not path.is_relative_to(base):
        base = Path(os.environ['RUNNER_TEMP']) / 'w/u'
        require(path == base / 'tools/workbench.py' and argv[3:] == ['verify-core', '--core', str(base)],
                'only registered unpacked-source identity control')
    name = path.relative_to(base).as_posix()
    require(name in {'ci/run_data_tests_v2.py', 'tests/lean_rejections.py', 'tools/workbench.py'},
            'unregistered Python control')
    return [sys.executable, '-I', '-S', '-B', str(Path(__file__).absolute()),
            '--run', _ANCHOR, str(base), name, *argv[3:]]


def run_control(package, anchor, entry, args):
    """Execute only authenticated snapshots, with original filename/__file__.

    Assumes a trusted interpreter/stdlib and no hostile concurrent host mutation.
    This is not a sandbox for arbitrary Lean/Lake/native code or OS attestation.
    """
    global _ANCHOR, _PACKAGE
    package = Path(package)
    snapshots = verify_controls(package, anchor)
    require(entry in {'ci/native_ci_v1.py', 'ci/export_ci_evidence_v2.py',
                      'ci/run_data_tests_v2.py', 'tests/lean_rejections.py', 'tools/workbench.py'},
            'registered control entry')
    require(type(args) is list and all(type(a) is str for a in args), 'control argument list')
    finder = SnapshotFinder(package, snapshots)
    old_path, old_spec, old_argv = list(sys.meta_path), importlib.util.spec_from_file_location, sys.argv
    old_context = _ANCHOR, _PACKAGE
    missing = object()
    old_modules = {name: sys.modules.get(name, missing) for name in finder.modules}
    error = None
    try:
        _ANCHOR, _PACKAGE = anchor, package
        for name in finder.modules:
            sys.modules.pop(name, None)
        # Authenticated exec may use a separate __main__ namespace; export these
        # actual functions, never the ambient launcher's unrelated __main__.
        control_module = types.ModuleType('trusted_controls_v1')
        control_module.__dict__.update(globals())
        sys.modules['trusted_controls_v1'] = control_module
        sys.meta_path.insert(0, finder)
        importlib.util.spec_from_file_location = finder.file_spec
        sys.argv = [str(package / entry), *args]
        namespace = {'__name__': '__main__', '__file__': str(package / entry), '__package__': None}
        try:
            exec(compile(snapshots[entry], str(package / entry), 'exec'), namespace)
        except BaseException as failure:
            error = failure
        try:
            verify_controls(package, anchor)
        except BaseException as integrity:
            if error is not None:
                if isinstance(error, SystemExit):
                    code = SystemExit.code.__get__(error)
                    # Linux/macOS can report success for a zero low-byte status.
                    # Conservatively normalize these requests, retaining both causes.
                    if code is None or (isinstance(code, int) and int.__mod__(code, 256) == 0):
                        integrity.__cause__ = error
                        raise RuntimeError('post-control integrity failed after successful entry exit') from integrity
                # Explicit cause preserves both failures on Python 3.10 too.
                raise error from integrity
            if isinstance(integrity, SystemExit):
                code = SystemExit.code.__get__(integrity)
                if code is None or (isinstance(code, int) and int.__mod__(code, 256) == 0):
                    raise RuntimeError('post-control integrity failed') from integrity
            raise
        if error is not None:
            raise error
    finally:
        _ANCHOR, _PACKAGE = old_context
        sys.meta_path[:] = old_path
        importlib.util.spec_from_file_location = old_spec
        sys.argv = old_argv
        for name, value in old_modules.items():
            if value is missing:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = value


def main():
    args = sys.argv[1:]
    require(len(args) >= 3 and args[0] in {'--check', '--run'},
            'explicit mode, external dispatcher SHA256 and physical tested package')
    mode, anchor, package = args[:3]
    if mode == '--check':
        require(len(args) == 3, 'check has no execution arguments')
        snapshots = verify_controls(Path(package), anchor)
        print(json.dumps({'control_source_integrity': True, 'controls': len(snapshots),
                          'execution': False, 'native_validation_pass': False}))
    else:
        require(len(args) >= 4, 'explicit control entry required')
        require(os.environ.get('GITHUB_ACTIONS') == 'true' and os.environ.get('CI') == 'true',
                'native Actions context required; no local operational dispatch')
        run_control(Path(package), anchor, args[3], args[4:])


if __name__ == '__main__':
    main()
