"""Small fail-closed parser regressions; no accepted receipts are edited."""
import sys
sys.dont_write_bytecode = True
import unittest
import audit
import aggregate


class ParserTests(unittest.TestCase):
    def test_multiline_and_empty(self):
        self.assertEqual(audit.exports("'B' depends on axioms:\n[Quot.sound, propext]\n'A' does not depend on any axioms\n"),
                         [{'name': 'A', 'axioms': []}, {'name': 'B', 'axioms': ['Quot.sound', 'propext']}])

    def test_bad_logs(self):
        for text in ["'A' depends on axioms: [sorryAx]", "warning: hi",
                     "'A' depends on axioms: []\n'A' depends on axioms: []"]:
            with self.assertRaises(RuntimeError):
                audit.exports(text)

    def test_exact_lists_not_just_whitelist(self):
        self.assertNotEqual(audit.exports("'A' depends on axioms: [propext]"),
                            audit.normalized([{'name': 'A', 'axioms': ['Classical.choice']}]))

    def test_aggregate_counts_and_axioms(self):
        text = 'MODULE\tResearch.X\nCOVERAGE\tResearch.X\tX.a\t[propext]\nCOVERAGE_COUNT\t1\n'
        self.assertEqual(len(aggregate.parsed(text)[1]), 1)
        for bad in [text.replace('COUNT\t1', 'COUNT\t2'), text.replace('propext', 'sorryAx'),
                    text + 'MODULE\tResearch.X\n']:
            with self.assertRaises(RuntimeError):
                aggregate.parsed(bad)


if __name__ == '__main__':
    unittest.main()
