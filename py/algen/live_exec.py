"""Изолировать рабочий кэш worker: built_library не чистит прежние кэши проекта."""

import os
from pathlib import Path
import runpy
import shutil
import sys


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ("algen.table", "algen.compress_base"):
        raise ValueError("допустимы только table и compress_base")
    from . import library
    private = Path(os.environ["ALGEN_WORKER_CACHE"]).resolve()
    private.mkdir(parents=True, exist_ok=True)
    name = "библиотека-" + library._fingerprint() + ".pickle"
    original, target = library.CACHE / name, private / name
    if original.is_file() and not target.exists():
        shutil.copyfile(original, target)
    library.CACHE = private
    module = sys.argv.pop(1)
    runpy.run_module(module, run_name="__main__")


if __name__ == "__main__":
    main()
