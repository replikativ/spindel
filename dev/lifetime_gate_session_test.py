import importlib.util
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('session', 'dev/lifetime_gate_session.py')
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

if __name__ == '__main__':
    unittest.main()
