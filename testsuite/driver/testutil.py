import os
import platform
import subprocess
import shutil
from pathlib import Path, PurePath

import threading

from my_typing import *

def passed():
    return {'passFail': 'pass'}

def failBecauseStderr(reason, stderr, tag=None):
    return failBecause(reason, tag, stderr=stderr)

def failBecause(reason, tag=None, **kwargs):
    return (dict ({'passFail': 'fail', 'reason': reason, 'tag': tag}, **kwargs))

def strip_quotes(s):
    # Don't wrap commands to subprocess.call/Popen in quotes.
    return s.strip('\'"')

def str_fail(s):
    return '\033[1m\033[31m' + s + '\033[0m'

def str_pass(s):
    return '\033[1m\033[32m' + s + '\033[0m'

def str_warn(s):
    return '\033[1m\033[33m' + s + '\033[0m'

def str_info(s):
    return '\033[1m\033[34m' + s + '\033[0m'

def getStdout(cmd_and_args: "List[str]"):
    # Can't use subprocess.check_output, since we also verify that
    # no stderr was produced
    p = subprocess.Popen([strip_quotes(cmd_and_args[0])] + cmd_and_args[1:],
                         stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    r = p.wait()
    if r != 0:
        raise Exception("Command failed: " + str(cmd_and_args))
    if stderr:
        raise Exception("stderr from command: %s\nOutput:\n%s\n" % (cmd_and_args, stderr))
    return stdout.decode('utf-8')

def lndir(srcdir: Path, dstdir: Path):
    # Create symlinks for all files in src directory.
    # Not all developers might have lndir installed.
    # os.system('lndir -silent {0} {1}'.format(srcdir, dstdir))
    for filename in srcdir.iterdir():
        base = filename.relative_to(srcdir)
        src = srcdir / base
        dst = dstdir / base
        if src.is_file():
            link_or_copy_file(src, dst)
        else:
            dst.mkdir()
            lndir(src, dst)

# All possible test metric strings.
def testing_metrics():
    return ['bytes allocated', 'peak_megabytes_allocated', 'max_bytes_used']

# On Windows, os.symlink is not defined with Python 2.7, but is in Python 3
# when using msys2, as GHC does. Unfortunately, only Administrative users have
# the privileges necessary to create symbolic links by default. Consequently we
# are forced to just copy instead.
#
# We define the following function to make this magic more
# explicit/discoverable. You are enouraged to use it instead of os.symlink.
if platform.system() == 'Windows' and os.getenv('FORCE_SYMLINKS') == None:
    def link_or_copy_file(src: Path, dst: Path):
        shutil.copyfile(str(src), str(dst))
else:
    def link_or_copy_file(src: Path, dst: Path):
        os.symlink(str(src), str(dst))

class Watcher(object):
    def __init__(self, count: int):
        self.pool = count
        self.evt = threading.Event()
        self.sync_lock = threading.Lock()
        if count <= 0:
            self.evt.set()

    def wait(self):
        self.evt.wait()

    def notify(self):
        self.sync_lock.acquire()
        self.pool -= 1
        if self.pool <= 0:
            self.evt.set()
        self.sync_lock.release()
