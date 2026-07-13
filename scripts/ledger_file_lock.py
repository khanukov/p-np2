"""Portable advisory locking for append-only ledger lockfiles.

Unix uses ``fcntl.flock``.  Native Windows Python has no ``fcntl`` module, so
it locks byte zero of the same sibling lockfile with ``msvcrt.locking``.  Both
backends keep the existing contract: callers hold one exclusive lock across
the complete scan/validate/append critical section.
"""

from __future__ import annotations

import errno
import os
import time
from typing import TextIO

if os.name == "nt":
    import msvcrt
else:
    import fcntl


def acquire_exclusive_lock(lock_file: TextIO) -> None:
    """Block until ``lock_file`` is exclusively locked by this process."""
    if os.name != "nt":
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        return

    # msvcrt locks a byte range at the current file position.  Give the
    # otherwise-content-free lockfile one byte and consistently lock byte 0.
    lock_file.seek(0, os.SEEK_END)
    if lock_file.tell() == 0:
        lock_file.write("\0")
        lock_file.flush()
    lock_file.seek(0)
    while True:
        try:
            msvcrt.locking(lock_file.fileno(), msvcrt.LK_NBLCK, 1)
            return
        except OSError as exc:
            # LK_NBLCK reports ordinary lock contention as EACCES.  Surface
            # permanent errors (bad descriptors, unsupported filesystems,
            # invalid byte ranges) instead of spinning forever.
            if exc.errno != errno.EACCES:
                raise
            time.sleep(0.01)


def release_exclusive_lock(lock_file: TextIO) -> None:
    """Release a lock previously acquired by ``acquire_exclusive_lock``."""
    if os.name != "nt":
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
        return

    lock_file.seek(0)
    msvcrt.locking(lock_file.fileno(), msvcrt.LK_UNLCK, 1)
