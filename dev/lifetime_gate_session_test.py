import importlib.util
import contextlib
import io
import json
import os
import sys
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

# Keep test imports from dirtying the harness checked by the session runner.
sys.dont_write_bytecode = True

spec = importlib.util.spec_from_file_location('session', Path(__file__).with_name('lifetime_gate_session.py'))
session = importlib.util.module_from_spec(spec)
spec.loader.exec_module(session)

class SessionTests(unittest.TestCase):
    def test_any_overload_repeats_whole_round(self):
        self.assertFalse(session.overloaded([{'load': 4}], 8))
        self.assertTrue(session.overloaded([{'load': 1}, {'load': 4.01}, {'load': 1}], 8))
        self.assertTrue(session.overloaded([{'load': -1}], 8))

    def test_foreign_process_record_excludes_own_work(self):
        with patch.object(session, 'command', side_effect=['uptime', '1 80 java\n2 75 native\n3 0 sh']), patch.object(session.os, 'getloadavg', return_value=(1, 2, 3)):
            self.assertEqual(['2 75 native'], session.host([1])['foreign_high_cpu'])

    def run_session(self, loads, result_code=0):
        """Execute orchestration with no JVMs, real locks or measured workloads."""
        launches = []

        def fake_command(args, **_):
            if args[:2] == ['git', 'rev-parse']:
                return args[-1]
            if args[:2] == ['git', 'status']:
                return ''
            if args[0] == 'clojure':
                return 'src:dev:test'
            if args[0] == 'java':
                return '8'
            raise AssertionError(args)

        def launch(args, **_):
            report = Path(args[-1])
            report.write_text(report.name)
            launches.append(report.name)
            return SimpleNamespace(poll=lambda: 0, returncode=0, pid=123)

        original = Path.cwd()
        with tempfile.TemporaryDirectory() as directory:
            try:
                os.chdir(directory)
                baseline = Path('dev/org/replikativ/spindel/baselines/main-06ce205.edn')
                baseline.parent.mkdir(parents=True)
                baseline.write_text('old baseline')
                observations = iter({'load': load, 'uptime': 'test uptime', 'foreign_high_cpu': []}
                                    for load in loads)
                with patch.object(session, 'command', side_effect=fake_command), \
                     patch.object(session.Path, 'exists', return_value=True), \
                     patch.object(session.subprocess, 'check_output', return_value=b''), \
                     patch.object(session.tarfile, 'open'), \
                     patch.object(session.subprocess, 'Popen', side_effect=launch), \
                     patch.object(session.subprocess, 'run', return_value=SimpleNamespace(returncode=result_code)), \
                     patch.object(session, 'host', side_effect=lambda: next(observations)), \
                     patch.object(session.time, 'sleep'), contextlib.redirect_stdout(io.StringIO()):
                    if result_code == 2:
                        with self.assertRaisesRegex(RuntimeError, 'Invalid measurement evidence'):
                            session.main('reports')
                        self.assertEqual('old baseline', baseline.read_text())
                        return
                    self.assertEqual(0, session.main('reports'))
                manifest = json.loads(Path('reports/session.json').read_text())
                self.assertEqual(['repeat-overloaded', 'accepted', 'accepted', 'accepted'],
                                 [a['status'] for a in manifest['attempts']])
                self.assertEqual(8, len(launches))
                self.assertEqual(['baseline', 'candidate'] * 4,
                                 [name.removesuffix('.edn').split('-')[-1] for name in launches])
                self.assertEqual('r2-attempt3-baseline.edn', baseline.read_text())
            finally:
                os.chdir(original)

    def test_overloaded_pair_repeats_and_never_becomes_stored_baseline(self):
        self.run_session([1, 5, 1, 1, 1, 1, 1, 1])

    def test_invalid_evidence_never_replaces_baseline(self):
        self.run_session([1, 1], result_code=2)


if __name__ == '__main__':
    unittest.main()
