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

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('session', Path(__file__).with_name('lifetime_gate_session.py'))
session = importlib.util.module_from_spec(spec)
spec.loader.exec_module(session)


class SessionTests(unittest.TestCase):
    def test_any_overload_or_missing_observation_invalidates(self):
        self.assertFalse(session.overloaded([{'load': 4}], 8))
        for rows in [[], [{'load': 4.01}], [{'load': -1}], [{'load': float('nan')}]]:
            self.assertTrue(session.overloaded(rows, 8))

    def test_foreign_process_record_excludes_own_work(self):
        with patch.object(session, 'command', side_effect=['uptime', '1 80 java\n2 75 native\n3 0 sh']), patch.object(session.os, 'getloadavg', return_value=(1, 2, 3)):
            self.assertEqual(['2 75 native'], session.host([1])['foreign_high_cpu'])

    def run_session(self, codes, expected, loads=None):
        """Exercise orchestration without JVMs, locks or measured workloads."""
        launches, checks = [], []

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

        def launch(args, env, **_):
            # The schedule and attempt cap must already be archived on disk.
            preregistered = json.loads(Path('reports/session.json').read_text())
            self.assertEqual(4, len(preregistered['schedule']))
            self.assertEqual(12, preregistered['max_attempts'])
            report = Path(args[-1])
            report.write_text(report.name)
            launches.append((env['SPINDEL_BENCH_ROLE'], int(env['SPINDEL_BENCH_POSITION'])))
            return SimpleNamespace(poll=lambda: 0, returncode=0, pid=123)

        code_iter = iter(codes)

        def check(paths, host_paths, log):
            checks.append((paths, host_paths))
            log.write_text('check')
            return next(code_iter)

        original = Path.cwd()
        with tempfile.TemporaryDirectory() as directory:
            try:
                os.chdir(directory)
                baseline = Path('dev/org/replikativ/spindel/baselines/main-06ce205.edn')
                baseline.parent.mkdir(parents=True)
                baseline.write_text('historical v3 baseline')
                observations = iter(loads) if loads is not None else None
                def host(*_):
                    return {'at': 0, 'load': next(observations) if observations else 1,
                            'uptime': 'test uptime', 'foreign_high_cpu': []}
                with patch.object(session, 'command', side_effect=fake_command), \
                     patch.object(session.Path, 'exists', return_value=True), \
                     patch.object(session.subprocess, 'check_output', return_value=b''), \
                     patch.object(session.tarfile, 'open'), \
                     patch.object(session.subprocess, 'Popen', side_effect=launch), \
                     patch.object(session, 'check_pair', side_effect=check, create=True), \
                     patch.object(session, 'host', side_effect=host), \
                     patch.object(session.time, 'sleep'), contextlib.redirect_stdout(io.StringIO()):
                    if expected == 'invalid':
                        with self.assertRaisesRegex(RuntimeError, 'Invalid measurement evidence'):
                            session.main('reports')
                    else:
                        self.assertEqual({'passed': 0, 'failed': 1, 'inconclusive': 3}[expected],
                                         session.main('reports'))
                self.assertEqual('historical v3 baseline', baseline.read_text())
                manifest = json.loads(Path('reports/session.json').read_text())
                if expected != 'invalid':
                    self.assertEqual(expected, manifest['status'])
                return manifest, launches, checks
            finally:
                os.chdir(original)

    def test_invalid_pair_repeated_whole_in_preregistered_order(self):
        manifest, launches, checks = self.run_session([3, 0, 0, 0, 0], 'passed')
        self.assertEqual(['environmental-invalid'] + ['accepted'] * 4,
                         [a['status'] for a in manifest['attempts']])
        self.assertEqual([('baseline', 0), ('candidate', 1)] * 2 +
                         [('candidate', 2), ('baseline', 3), ('baseline', 4), ('candidate', 5),
                          ('candidate', 6), ('baseline', 7)], launches)
        self.assertEqual(5, len(checks))
        # Checker receives baseline/candidate paths even for BA measurement order.
        for paths, _ in checks:
            self.assertTrue(paths[0].endswith('baseline.edn'))
            self.assertTrue(paths[1].endswith('candidate.edn'))

    def test_valid_failed_outcomes_are_never_retried(self):
        manifest, launches, checks = self.run_session([1, 0, 1, 0], 'failed')
        self.assertEqual(4, len(checks))
        self.assertEqual(8, len(launches))
        self.assertEqual(['accepted'] * 4, [a['status'] for a in manifest['attempts']])

    def test_attempt_cap_is_inconclusive(self):
        manifest, launches, checks = self.run_session([3] * 12, 'inconclusive')
        self.assertEqual(12, len(checks))
        self.assertEqual(24, len(launches))
        self.assertEqual(0, manifest['valid_pairs'])
        self.assertFalse(manifest['gates_passed'])

    def test_admission_waits_also_consume_capped_attempts(self):
        manifest, launches, checks = self.run_session([], 'inconclusive', [5] * 12)
        self.assertEqual([], launches)
        self.assertEqual([], checks)
        self.assertEqual(12, len(manifest['attempts']))

    def test_invalid_measurement_never_publishes_baseline(self):
        self.run_session([2], 'invalid')

    def test_controller_records_role_and_fixture_window(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'host.ednlog'
            session.record_host(path, 'candidate', 'fixture', 'start',
                                {'at': 1, 'load': 1, 'uptime': 'u', 'foreign_high_cpu': ['2 75 native']})
            text = path.read_text()
            self.assertIn(':role :candidate', text)
            self.assertIn(':window "fixture"', text)
            self.assertIn(':phase :start', text)
            self.assertIn(':foreign-high-cpu ["2 75 native"]', text)

    def test_checker_rejects_missing_windows_before_missing_outcomes(self):
        # Real Babashka gate entry, synthetic evidence: no measured workloads.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths, hosts = [], []
            for role in ['baseline', 'candidate']:
                report = root / (role + '.edn')
                report.write_text('{:processors 8 :session {:role :' + role + '} :host-observations []}')
                host = root / (role + '.ednlog')
                host.write_text('')
                paths.append(str(report))
                hosts.append(str(host))
            log = root / 'check.log'
            self.assertEqual(3, session.check_pair(paths, hosts, log))
            self.assertIn(':environmental-invalid', log.read_text())
            self.assertNotIn(':gate ', log.read_text())

    def test_active_window_survives_periodic_controller_samples(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'host.ednlog'
            self.assertEqual('worker', session.active_window(path))
            Path(str(path) + '.window').write_text(json.dumps('timed fixture'))
            self.assertEqual('timed fixture', session.active_window(path))


if __name__ == '__main__':
    unittest.main()
