"""Native Codex or a trusted argv protocol. Never a shell command string.

The native provider is deliberately NOT invoked by source-author tests.
Requested identity/usage reports are not independently authenticated identity.
"""
import datetime
import json
import os
import signal
import subprocess
import time
from pathlib import Path
from . import kernel as K

SCHEMA = {'type': 'object', 'properties': {'proof': {'type': 'string'}},
          'required': ['proof'], 'additionalProperties': False}
REQUEST_LIMIT = 9000


def request_bytes(request):
    """Exact UTF-8 bytes supplied on native stdin (also the command protocol file)."""
    return (json.dumps(request, ensure_ascii=False, separators=(',', ':'))+'\n').encode('utf-8')


def config(d):
    if not isinstance(d, dict) or d.get('kind') not in {'codex', 'command', 'DATA'}:
        raise ValueError('explicit candidate backend required')
    if type(d.get('seconds')) is not int or not 1 <= d['seconds'] <= 3600:
        raise ValueError('candidate wall budget 1..3600 seconds')
    if d['kind'] == 'codex':
        if d.get('model') != 'gpt-6.1-sol' or d.get('effort') != 'xhigh':
            raise ValueError('pilot native identity must be explicitly Sol/xhigh')
    else:
        argv = d.get('argv')
        if not isinstance(argv, list) or not argv or any(not isinstance(s, str) or '\0' in s for s in argv):
            raise ValueError('trusted command needs argv array')
    return d


def generate(cfg, request, output):
    """One owned candidate process, real waited result even on timeout/failure.

    POSIX/main-thread/default SIGCHLD/sole reaper; direct child remains unreaped
    when its group is signalled. This is not universal descendant/crash safety.
    Caller trusts executable and filesystem isolation; not arbitrary-code sandbox.
    """
    cfg = config(cfg)
    raw = request_bytes(request)
    if len(raw) > REQUEST_LIMIT:
        raise ValueError('candidate request exceeds 9000 UTF-8 bytes')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    with (output/'request.json').open('xb') as stream:
        stream.write(raw)
    K.write(output/'schema.json', SCHEMA)
    response = output/'response.json'
    if cfg['kind'] == 'codex':
        argv = ['codex', 'exec', '--model', cfg['model'], '-c',
                'model_reasoning_effort="xhigh"', '--sandbox', 'read-only',
                '--skip-git-repo-check', '--json', '--output-schema',
                str(output/'schema.json'), '--output-last-message', str(response), '-']
    else:
        argv = cfg['argv']+[str(output/'request.json'), str(response)]
    receipt = {'argv': argv, 'cwd': str(output), 'PID': None, 'OS_exit': None,
               'waited': False, 'timeout': False, 'start_UTC':
               datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'requested_model': cfg.get('model'), 'requested_effort': cfg.get('effort'),
               'permissions': 'read-only' if cfg['kind'] == 'codex' else 'trusted command',
               'verified_actual_model': None, 'cost': None, 'kind': cfg['kind']}
    receipt['request_stdin'] = K.pin(output/'request.json')
    start = time.monotonic()
    owned_command(argv, output, cfg['seconds'], receipt)
    receipt['elapsed_seconds'] = time.monotonic()-start
    receipt['end_UTC'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    receipt['reported_usage'] = []
    receipt['verified_actual_usage'] = None
    if cfg['kind'] == 'codex':
        # Provider event reports are retained, never promoted to API attestation.
        with (output/'stdout.txt').open(errors='replace') as stream:
            for line in stream:
                try:
                    event = json.loads(line)
                    if event.get('type') == 'turn.completed' and isinstance(event.get('usage'), dict):
                        receipt['reported_usage'].append(event['usage'])
                except (ValueError, AttributeError):
                    pass
    receipt['files'] = [K.pin(p) for p in sorted(output.iterdir()) if p.is_file()]
    K.write(output/'PROVIDER.json', receipt)
    if receipt['timeout'] or receipt['OS_exit'] != 0 or not receipt['waited'] or receipt.get('cleanup_errors'):
        return None, receipt
    try:
        if response.stat().st_size > 20000:
            raise ValueError('candidate response too large')
        obj = K.read(response)
        if not isinstance(obj, dict) or set(obj) != {'proof'}:
            raise ValueError('candidate response schema')
        return K.proof_body(obj['proof']), receipt
    except (OSError, ValueError, KeyError, TypeError) as e:
        receipt['response_error'] = repr(e)
        # Immutable actual receipt above; a separate parsing observation follows.
        K.write(output/'RESPONSE_REJECTED.json', {'reason': repr(e)})
        return None, receipt


def owned_command(argv, output, seconds, receipt):
    """Signal-blocked spawn assignment; exact unreaped child anchors its group."""
    import threading
    if (os.name != 'posix' or threading.current_thread() is not threading.main_thread()
            or signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL):
        raise ValueError('POSIX main-thread/default-SIGCHLD sole-reaper required')
    pid = None
    exited = False
    signals = {signal.SIGINT, signal.SIGTERM, signal.SIGHUP}
    oldmask = signal.pthread_sigmask(signal.SIG_BLOCK, signals)
    oldcwd = Path.cwd()
    handlers = {s: signal.getsignal(s) for s in signals}
    def interrupted(n, frame):
        raise InterruptedError('candidate owner interrupted: '+str(n))
    def observe(deadline):
        while True:
            if os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None:
                return True
            if time.monotonic() >= deadline:
                return False
            time.sleep(0.01)
    try:
        os.chdir(output)
        for sig in signals:
            signal.signal(sig, interrupted)
        with (output/'request.json').open('rb') as inp, (output/'stdout.txt').open('xb') as out, (output/'stderr.txt').open('xb') as err:
            actions = [(os.POSIX_SPAWN_DUP2, inp.fileno(), 0),
                       (os.POSIX_SPAWN_DUP2, out.fileno(), 1),
                       (os.POSIX_SPAWN_DUP2, err.fileno(), 2)]
            # No shell, no preexec/fork Python. The child receives the OLD mask.
            pid = os.posix_spawnp(argv[0], argv, dict(os.environ), setpgroup=0,
                                  setsigmask=oldmask, file_actions=actions)
            receipt['PID'] = pid
            receipt['pgid'] = pid
            try:
                receipt['startticks'] = Path('/proc', str(pid), 'stat').read_text().rsplit(')', 1)[1].split()[19]
            except OSError:
                receipt['startticks'] = None
            signal.pthread_sigmask(signal.SIG_SETMASK, oldmask)
            exited = observe(time.monotonic()+seconds)
            receipt['timeout'] = not exited
    except OSError as e:
        receipt['error'] = repr(e)
    finally:
        errors = []
        try:
            signal.pthread_sigmask(signal.SIG_BLOCK, signals)
            if pid is not None:
                if not exited:
                    try:
                        os.killpg(pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    except OSError as e:
                        errors.append('signal:'+repr(e))
                    try:
                        exited = observe(time.monotonic()+2)
                    except OSError as e:
                        errors.append('observe:'+repr(e))
                    if not exited:
                        try:
                            os.killpg(pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        except OSError as e:
                            errors.append('kill:'+repr(e))
                # Signalling errors do not skip the independent owned wait.
                try:
                    while True:
                        try:
                            q, status = os.waitpid(pid, 0)
                            break
                        except InterruptedError:
                            continue
                    receipt.update(waited=q == pid, OS_exit=os.waitstatus_to_exitcode(status), raw_wait=status)
                except OSError as e:
                    errors.append('wait:'+repr(e))
        finally:
            try:
                os.chdir(oldcwd)
            except OSError as e:
                errors.append('restore-cwd:'+repr(e))
            for sig, handler in handlers.items():
                try:
                    signal.signal(sig, handler)
                except OSError as e:
                    errors.append('restore-handler:'+repr(e))
            try:
                signal.pthread_sigmask(signal.SIG_SETMASK, oldmask)
            except OSError as e:
                errors.append('restore-mask:'+repr(e))
        if errors:
            receipt['cleanup_errors'] = errors
