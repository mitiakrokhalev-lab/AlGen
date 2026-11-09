"""Read-only diagnostic: standard memory watchdog; cProfile of a verdict prefix.

The prefix is deliberately incomplete and is never a full scheme result.
No production module is edited by this harness.
"""
import sys
from pathlib import Path

sys.path.insert(0, '/workspace/work/algen-dev/py')
from tools import profile_memory as P

if '--profile-child' not in sys.argv:
    original_popen = P.subprocess.Popen

    def launch(command, *args, **kwargs):
        if '--child' in command and 'tools.profile_memory' in command:
            offset = command.index('tools.profile_memory') + 1
            command = [sys.executable, '-B', __file__, '--profile-child'] + command[offset:]
        return original_popen(command, *args, **kwargs)

    P.subprocess.Popen = launch
    P.main()
else:
    import cProfile
    import json
    import signal
    import time
    from collections import Counter
    from algen import enumerate as E

    sys.argv.remove('--profile-child')
    out = Path(sys.argv[sys.argv.index('--out') + 1])
    profile = cProfile.Profile()
    started = None
    count = 0
    kinds = Counter()
    prefix_limit = 12000
    original_minimal = E.minimal
    original_decide = E.cdecide

    class PrefixComplete(BaseException):
        pass

    class WatchdogStop(BaseException):
        pass

    def minimal(*args, **kwargs):
        global started
        result = original_minimal(*args, **kwargs)
        started = time.monotonic()
        profile.enable()
        return result

    def decide(*args, **kwargs):
        global count
        result = original_decide(*args, **kwargs)
        if started is not None:
            count += 1
            kinds[result.kind] += 1
            if count >= prefix_limit:
                raise PrefixComplete()
        return result

    def stopped(*args):
        raise WatchdogStop()

    E.minimal = minimal
    E.cdecide = decide
    signal.signal(signal.SIGTERM, stopped)
    reason = 'normal_module_exit'
    try:
        P.main()
    except PrefixComplete:
        reason = 'diagnostic_prefix_limit'
    except WatchdogStop:
        reason = 'parent_watchdog'
    except BaseException:
        reason = 'unexpected_exception'
        raise
    finally:
        profile.disable()
        elapsed = None if started is None else time.monotonic() - started
        profile.dump_stats(str(out / 'verdict-prefix.prof'))
        receipt = dict(scope='diagnostic verdict prefix, NOT full scheme',
                       full_scheme_complete=False, stop_reason=reason,
                       decisions=count, limit=prefix_limit, kinds=dict(kinds),
                       profiled_seconds=elapsed)
        (out / 'diagnostic.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
