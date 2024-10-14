import subprocess
import os, shutil
import os.path
import sys
from typing import Union

def execute(cmd: list[str], t: Union[None, int] = None) -> str:

    return subprocess.run(
        cmd,
        text = True,
        stdout = subprocess.PIPE,
        stderr = subprocess.STDOUT,
        timeout = t
    ).stdout


def run_all(path: str, dim: str) -> None:
    for dirpath, dirnames, filenames in os.walk(path):
        for filename in filenames:
            print("Running", filename)
            try:
                output = execute(['go','run', '.', dirpath + '/' + filename, dim],6000)
            except subprocess.TimeoutExpired:
                print('TIMEOUT')

argumentList = sys.argv[1:]

if os.path.isdir('taint-out'):
    shutil.rmtree('taint-out')
os.mkdir('taint-out') 
run_all('taint', argumentList[0])