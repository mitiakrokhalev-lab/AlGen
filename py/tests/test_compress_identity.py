"""Exact identities, including adversarial collisions and persisted reports."""
import copy
import json
import unittest
from unittest.mock import patch

from algen import compress as C, compress_base as B
from test_compress import ATOMS, FakeForm, row


class CompressionIdentityTest(unittest.TestCase):
    def independent_questions(self):
        form = FakeForm(ATOMS, [])
        rows = [row(form, ["a"], "b", n=2), row(form, ["d"], "e", n=1)]
        for r in rows:
            r["запрет"] = list(r["класс"])
        return form, rows

    def test_full_id_survives_json_and_exact_copies_still_merge(self):
        form, rows = self.independent_questions()
        self.assertEqual(len(C.row_id(rows[0])), 64)
        self.assertEqual(C.row_id(rows[0]), C.row_id(json.loads(json.dumps(rows[0]))))
        self.assertNotEqual(C.row_id(rows[0]), C.row_id(rows[1]))
        rows.append(copy.deepcopy(rows[0]))
        C.compress(form, rows, use_instances=False)
        kept = C.kept_questions(rows)
        self.assertEqual(len(kept), 2)
        self.assertEqual(kept[0]["класс"], list(rows[0]["класс"]))
        self.assertEqual(C.verify(form, rows), [])

    def test_generated_collision_rejected_before_rows_are_mutated(self):
        form, rows = self.independent_questions()
        before = copy.deepcopy(rows)
        with patch.object(C, "row_id", return_value="0000000000"):
            with self.assertRaisesRegex(ValueError, "коллизия"):
                C.compress(form, rows, use_instances=False)
        self.assertEqual(rows, before)

    def test_old_refuted_id_is_not_silently_reenabled_during_recompression(self):
        form, rows = self.independent_questions()
        rows[0]["№"] = "1234567890"
        before = copy.deepcopy(rows)
        with self.assertRaisesRegex(ValueError, "миграции"):
            C.compress(form, rows, refuted=["1234567890"], use_instances=False)
        self.assertEqual(rows, before)

    def test_persisted_collision_cannot_pass_verifier_export_or_reopen(self):
        form, rows = self.independent_questions()
        for r in rows:
            r.update({"№": "0000000000", "свёрнута": False, "следует из": []})
        before = copy.deepcopy(rows)
        self.assertEqual(C.verify(form, rows)[0][0], "идентичность")
        self.assertEqual(C.regress(before, rows)[0][0], "идентичность")
        with self.assertRaisesRegex(ValueError, "коллизия"):
            C.kept_questions(rows)
        with self.assertRaisesRegex(ValueError, "коллизия"):
            C.reopen(rows, ["0000000000"])
        self.assertEqual(rows, before)

    def test_present_invalid_ids_are_not_treated_as_missing_ids(self):
        form, rows = self.independent_questions()
        for invalid in (None, "", 0, False):
            with self.subTest(invalid=invalid):
                bad = [dict(r, **{"№": invalid}) for r in rows]
                self.assertEqual(C.verify(form, bad)[0][0], "идентичность")
                with self.assertRaisesRegex(ValueError, "невалидный"):
                    C.kept_questions(bad)

    def test_cross_scheme_old_short_id_does_not_merge_independent_questions(self):
        form, rows = self.independent_questions()
        qs = [{"id": "S1:x", "№": "x", "запрет": rows[0]["запрет"], "примеров": 2},
              {"id": "S2:x", "№": "x", "запрет": rows[1]["запрет"], "примеров": 1}]
        names = {a: (a, True) for a in ATOMS} | {"¬" + a: (a, False) for a in ATOMS}
        kept, folded, why, enc, fixed = B.fold_across(form.sc.T, names, [], qs)
        self.assertEqual(kept, ["S1:x", "S2:x"])
        self.assertEqual(folded, {})
        self.assertEqual(B.verify_across(form.sc.T, enc, fixed, kept, folded), [])
        # A colliding fully qualified ID must fail before enc can overwrite it.
        qs[1]["id"] = "S1:x"
        with self.assertRaisesRegex(ValueError, "коллизия"):
            B.fold_across(form.sc.T, names, [], qs)
        with self.assertRaisesRegex(ValueError, "повтор"):
            B.fold_across(form.sc.T, names, [], [qs[0], copy.deepcopy(qs[0])])
        self.assertTrue(B.verify_across(form.sc.T, {"S:x": [1]}, [], ["S:x"], {"S:x": ["S:x"]}))

    def test_result_resume_version_changes_without_invalidating_library_tables(self):
        from algen import table
        with patch.object(table, "_fp", return_value="same-library"):
            with patch.dict("os.environ", {"ALGEN_COMPRESS": ""}):
                self.assertEqual(table.result_fp("G", 3), "same-library:3")
            with patch.dict("os.environ", {"ALGEN_COMPRESS": "1"}):
                self.assertEqual(table.result_fp("G", 3), "same-library:3:compression:3")
                self.assertEqual(table.result_fp("GHK", 3), "same-library:3:pair-req:1:compression:3")
                self.assertEqual(table._fp("G"), "same-library")
                with patch.object(table.E, "CENSUS", True):
                    self.assertEqual(table.result_fp("G", 3), "same-library:3")

    def test_basis_input_hash_includes_the_exact_class_metadata(self):
        q = {"id": "S:x", "№": "x", "запрет": ["a", "¬b"], "класс": ["a", "¬b"]}
        changed = dict(q, класс=["d", "¬e"])
        self.assertNotEqual(B.questions_hash([q]), B.questions_hash([changed]))


if __name__ == "__main__":
    unittest.main()
