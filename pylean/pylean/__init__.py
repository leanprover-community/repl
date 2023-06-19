import pexpect
import json

import os

class LeanServer:
    def __init__(self):
        path_to_repl = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))

        self.proc = pexpect.spawn(
            "lake env lean --run REPL/Main.lean", cwd=path_to_repl, encoding="utf-8"
        )

    def run_code(self, code, env=None, verbose=False):
        if env:
            command = (
                json.dumps(dict(cmd=code, env=env))
            )  # [1:-1] removes single quotes
        else:
            command = (
                '{ "cmd" : "' + repr(code)[1:-1] + '" }'
            )  # [1:-1] removes single quotes

        if verbose:
            print(command)
        self.proc.sendline(command)
        self.proc.expect_exact(command + "\r\n")
        self.proc.sendline()
        self.proc.expect_exact("\r\n")
        try:
            index = self.proc.expect('env": \d+\}', timeout=20)
            output = self.proc.before + self.proc.match.group()
            if verbose: 
                print(output)
            return json.loads(output)
        except pexpect.exceptions.TIMEOUT:
            raise pexpect.exceptions.TIMEOUT
