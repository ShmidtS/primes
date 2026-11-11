#!/usr/bin/env python3
"""Focused public-CLI and real-olean regressions for merge_module.py."""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import merge_module as merger


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "scripts" / "merge_module.py"
PACKET = REPO / ".tmp" / "refactor" / "append-retarget"
RAW_PREFIX = "Hagi.MergeP3ProtectedRaw"
CHILD_REL = Path("Hagi/MergeP3ProtectedRaw/Provider.lean")
PARENT_REL = Path("Hagi/MergeP3ProtectedRaw/Destination.lean")
DEP_REL = Path("Hagi/MergeP3ProtectedRaw/Dependency.lean")
EXISTING_REL = Path("Hagi/MergeP3ProtectedRaw/Existing.lean")


def output_text(result: subprocess.CompletedProcess) -> str:
    stdout = result.stdout.decode("utf-8", errors="replace")
    stderr = result.stderr.decode("utf-8", errors="replace")
    return stdout + stderr


class RawCliRegression(unittest.TestCase):
    def setUp(self):
        PACKET.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(
            prefix="merge-module-raw-", dir=PACKET)
        self.root = Path(self.temporary.name).resolve()
        self.provider_body = (
            b"\r\n/- provider body \xcf\x80 -/\n"
            b"set_option maxRecDepth 129 in\r\n"
            b"private def providerValue : Nat := 7")

    def tearDown(self):
        self.temporary.cleanup()

    def write(self, relative: Path | str, data: bytes | str):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(data, str):
            data = data.encode("utf-8")
        path.write_bytes(data)
        return path

    def consumer(self, index: int):
        return Path(f"Hagi/MergeP3ProtectedRaw/Consumer{index}.lean")

    def fixture(self, count=1, append=False, parent_on_consumers=True):
        provider = (
            b"/- \xcf\x80 leading provider -/\r\n"
            + f"import {RAW_PREFIX}.Dependency\r\n".encode()
            + f"import {RAW_PREFIX}.Existing\n".encode()
            + b"import Mathlib\r\nimport Mathlib.Tactic\n"
            + self.provider_body
        )
        parent_header = b"/- \xce\xb3 leading parent -/\n"
        if not append:
            parent_header += f"import {RAW_PREFIX}.Provider\r\n".encode()
        parent_header += f"import {RAW_PREFIX}.Existing\n".encode()
        parent_body = (
            b"\n-- parent bytes stay here\r\n"
            b"private def destinationValue : Nat := 8")
        self.write(CHILD_REL, provider)
        self.write(PARENT_REL, parent_header + parent_body)
        self.write(DEP_REL, b"def dependencyValue : Nat := 2\n")
        self.write(EXISTING_REL, b"def existingValue : Nat := 1\n")
        root = (f"import {RAW_PREFIX}.Provider\r\n"
                f"import {RAW_PREFIX}.Destination\n").encode()
        self.write("Hagi.lean", root)
        for index in range(1, count + 1):
            imports = f"/- consumer {index} π -/\nimport {RAW_PREFIX}.Provider\r\n"
            if parent_on_consumers and index == 1:
                imports += f"import {RAW_PREFIX}.Destination\n"
            body = f"\ndef consumer{index} : Nat := {index}\n"
            self.write(self.consumer(index), (imports + body).encode())
        return provider, parent_header, parent_body

    def run_cli(self, *arguments, root=None):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *map(str, arguments)],
            cwd=self.root if root is None else root,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)

    def merge_arguments(self, count, append=False, all_targets=False):
        arguments = [CHILD_REL, PARENT_REL]
        if append:
            arguments.append("--append")
        if all_targets:
            arguments.append("--retarget-all")
        else:
            for index in range(1, count + 1):
                arguments.extend(["--retarget", self.consumer(index)])
        return arguments

    def snapshot(self):
        paths = list((self.root / "Hagi").rglob("*.lean"))
        if (self.root / "Hagi.lean").exists():
            paths.append(self.root / "Hagi.lean")
        return {path.relative_to(self.root): path.read_bytes()
                for path in sorted(paths)}

    def assert_snapshot(self, before):
        after = self.snapshot()
        self.assertEqual(after, before)
        for relative, raw in before.items():
            self.assertEqual(hashlib.sha256((self.root / relative).read_bytes()).digest(),
                             hashlib.sha256(raw).digest())

    def assert_failure(self, result, fragment):
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(fragment, output_text(result))

    def test_default_cli_exact_raw_union_order_and_provider_first(self):
        _, _, parent_body = self.fixture(count=1)
        result = self.run_cli(*self.merge_arguments(1))
        self.assertEqual(result.returncode, 0, output_text(result))
        expected = (
            b"/- \xce\xb3 leading parent -/\n"
            + f"import {RAW_PREFIX}.Existing\n".encode()
            + f"import {RAW_PREFIX}.Dependency\n".encode()
            + b"import Mathlib\nimport Mathlib.Tactic\n"
            + self.provider_body + parent_body
        )
        self.assertEqual((self.root / PARENT_REL).read_bytes(), expected)
        self.assertFalse((self.root / CHILD_REL).exists())
        self.assertEqual(
            (self.root / self.consumer(1)).read_bytes(),
            (f"/- consumer 1 π -/\nimport {RAW_PREFIX}.Destination\n"
             "\ndef consumer1 : Nat := 1\n").encode())
        self.assertEqual((self.root / "Hagi.lean").read_bytes(),
                         f"import {RAW_PREFIX}.Destination\n".encode())

    def test_append_all_three_exact_raw_receiver_first_and_final_eol(self):
        self.fixture(count=3, append=True)
        original_parent_body = (
            b"\n-- parent bytes stay here\r\n"
            b"private def destinationValue : Nat := 8")
        result = self.run_cli(*self.merge_arguments(
            3, append=True, all_targets=True))
        self.assertEqual(result.returncode, 0, output_text(result))
        actual = (self.root / PARENT_REL).read_bytes()
        self.assertLess(actual.index(original_parent_body),
                        actual.index(self.provider_body))
        self.assertIn(b"import Mathlib\nimport Mathlib.Tactic\n", actual)
        self.assertEqual(actual[-len(self.provider_body):], self.provider_body)
        self.assertNotIn(f"import {RAW_PREFIX}.Provider".encode(), actual)
        for index in range(1, 4):
            raw = (self.root / self.consumer(index)).read_bytes()
            self.assertEqual(raw.count(
                f"import {RAW_PREFIX}.Destination".encode()), 1)
            self.assertNotIn(f"import {RAW_PREFIX}.Provider".encode(), raw)
        self.assertFalse((self.root / CHILD_REL).exists())

    def test_repeatable_legacy_retarget_flags_cover_all_three(self):
        self.fixture(count=3, parent_on_consumers=False)
        result = self.run_cli(*self.merge_arguments(3))
        self.assertEqual(result.returncode, 0, output_text(result))
        for index in range(1, 4):
            raw = (self.root / self.consumer(index)).read_bytes()
            self.assertIn(
                f"import {RAW_PREFIX}.Destination\r\n".encode(), raw)

    def test_symlink_and_case_aliases_are_canonicalized_or_rejected(self):
        self.fixture(count=1)
        before = self.snapshot()
        alias = self.root / "HagiAlias"
        if os.name == "nt":
            linked = subprocess.run(
                ["cmd", "/c", "mklink", "/J", str(alias), str(self.root / "Hagi")],
                capture_output=True, text=True, timeout=30)
            self.assertEqual(linked.returncode, 0,
                             linked.stdout + linked.stderr)
        else:
            alias.symlink_to(self.root / "Hagi", target_is_directory=True)
        try:
            linked_child = alias / Path(*CHILD_REL.parts[1:])
            result = self.run_cli(linked_child, PARENT_REL,
                                  *self.merge_arguments(1)[2:])
            self.assert_failure(result, "symbolic links")
            self.assert_snapshot(before)
            if os.name == "nt":
                case_child = Path(str(CHILD_REL).replace("Provider.lean", "provider.lean"))
                result = self.run_cli(case_child, case_child)
                self.assert_failure(result, "distinct")
                self.assert_snapshot(before)
        finally:
            alias.unlink()

    def test_zero_retarget_set_is_valid(self):
        self.fixture(count=0)
        result = self.run_cli(CHILD_REL, PARENT_REL)
        self.assertEqual(result.returncode, 0, output_text(result))
        self.assertFalse((self.root / CHILD_REL).exists())

    def test_plan_precomputes_parent_root_every_retarget_and_deletion(self):
        self.fixture(count=3)
        plan = merger.make_plan(
            self.root / CHILD_REL, self.root / PARENT_REL,
            retarget_all=True, root=self.root)
        self.assertEqual(len(plan.operations), 5)
        self.assertEqual(len(plan.outputs), 6)
        self.assertIsNone(plan.outputs[self.root / CHILD_REL])
        for path in plan.operations:
            self.assertIsInstance(plan.outputs[path], bytes)
        self.assertEqual(set(plan.snapshots), set(plan.outputs))
        before = self.snapshot()
        self.assertEqual(self.snapshot(), before)

    def test_canonical_aliases_duplicates_and_forbidden_retargets(self):
        for kind in ("same", "outside", "duplicate", "alias",
                     "parent", "child", "root", "missing", "extra"):
            with self.subTest(kind=kind):
                self.fixture(count=1)
                before = self.snapshot()
                if kind == "same":
                    arguments = [CHILD_REL, CHILD_REL]
                elif kind == "outside":
                    outside = self.root.parent / "outside-merge-input.lean"
                    outside.write_bytes(b"def outside : Nat := 0\n")
                    try:
                        result = self.run_cli(outside, PARENT_REL)
                        self.assert_failure(result, "outside")
                    finally:
                        outside.unlink()
                    self.assert_snapshot(before)
                    continue
                elif kind == "duplicate":
                    arguments = self.merge_arguments(1) + [
                        "--retarget", self.consumer(1)]
                elif kind == "alias":
                    arguments = [CHILD_REL, PARENT_REL,
                                 "--retarget", self.consumer(1),
                                 "--retarget", Path("Hagi") / ".." /
                                 self.consumer(1)]
                elif kind == "parent":
                    arguments = [CHILD_REL, PARENT_REL,
                                 "--retarget", PARENT_REL]
                elif kind == "child":
                    arguments = [CHILD_REL, PARENT_REL,
                                 "--retarget", CHILD_REL]
                elif kind == "root":
                    arguments = [CHILD_REL, PARENT_REL,
                                 "--retarget", Path("Hagi.lean")]
                elif kind == "missing":
                    arguments = [CHILD_REL, PARENT_REL]
                else:
                    self.write("Hagi/MergeP3ProtectedRaw/Extra.lean",
                               "def extra : Nat := 0\n")
                    before = self.snapshot()
                    arguments = self.merge_arguments(1) + [
                        "--retarget", "Hagi/MergeP3ProtectedRaw/Extra.lean"]
                result = self.run_cli(*arguments)
                expected = "missing" if kind == "outside" else {
                    "same": "distinct", "duplicate": "duplicate",
                    "alias": "duplicate", "parent": "non-C/P/Root",
                    "child": "non-C/P/Root", "root": "non-C/P/Root",
                    "missing": "missing=", "extra": "extra="}[kind]
                self.assert_failure(result, expected)
                self.assert_snapshot(before)

    def test_missing_root_and_internal_source_fail_closed(self):
        for kind in ("root-absent", "root-dangling", "missing-dependency"):
            with self.subTest(kind=kind):
                self.fixture(count=1)
                if kind == "root-absent":
                    (self.root / "Hagi.lean").unlink()
                elif kind == "root-dangling":
                    self.write("Hagi.lean",
                               f"import {RAW_PREFIX}.Destination\n")
                else:
                    (self.root / DEP_REL).unlink()
                before = self.snapshot()
                result = self.run_cli(*self.merge_arguments(1))
                self.assert_failure(result, "Root" if kind != "missing-dependency"
                                    else "missing internal source")
                self.assert_snapshot(before)

    def test_preexisting_direct_and_indirect_cycles_are_rejected(self):
        for kind in ("direct", "indirect"):
            with self.subTest(kind=kind):
                self.fixture(count=1, append=True)
                if kind == "direct":
                    self.write(EXISTING_REL,
                               f"import {RAW_PREFIX}.Destination\n"
                               "def existingValue : Nat := 1\n")
                else:
                    self.write(DEP_REL,
                               f"import {RAW_PREFIX}.Existing\n"
                               "def dependencyValue : Nat := 2\n")
                    self.write(EXISTING_REL,
                               f"import {RAW_PREFIX}.Dependency\n"
                               "def existingValue : Nat := 1\n")
                before = self.snapshot()
                result = self.run_cli(*self.merge_arguments(
                    1, append=True))
                self.assert_failure(result, "pre-existing dependency cycle")
                self.assert_snapshot(before)

    def test_post_retarget_ancestor_and_copied_dependency_cycles(self):
        for kind in ("retarget", "copied"):
            with self.subTest(kind=kind):
                self.fixture(count=1, append=True,
                             parent_on_consumers=kind != "retarget")
                if kind == "retarget":
                    parent = (self.root / PARENT_REL).read_bytes().replace(
                        f"import {RAW_PREFIX}.Existing\n".encode(),
                        f"import {RAW_PREFIX}.Existing\nimport {RAW_PREFIX}.Consumer1\n".encode())
                    self.write(PARENT_REL, parent)
                    arguments = self.merge_arguments(1, append=True)
                else:
                    self.write(DEP_REL,
                               f"import {RAW_PREFIX}.Destination\n"
                               "def dependencyValue : Nat := 2\n")
                    arguments = self.merge_arguments(1, append=True)
                before = self.snapshot()
                result = self.run_cli(*arguments)
                self.assert_failure(result, "post-merge dependency cycle")
                self.assert_snapshot(before)

    def test_unsupported_headers_trailing_forms_and_body_imports(self):
        variants = {
            "module": b"/- copyright \xcf\x80 -/\nmodule\n\n"
                      + f"import {RAW_PREFIX}.Provider\n".encode(),
            "module-order": b"module\nmeta public " + f"import {RAW_PREFIX}.Provider\n".encode(),
            "module-public": b"module\npublic " + f"import {RAW_PREFIX}.Provider\n".encode(),
            "module-meta": b"module\npublic meta " + f"import {RAW_PREFIX}.Provider\n".encode(),
            "module-all": b"module\nimport all " + f"{RAW_PREFIX}.Provider\n".encode(),
            "prelude": b"prelude\n" + f"import {RAW_PREFIX}.Provider\n".encode(),
            "public": b"public " + f"import {RAW_PREFIX}.Provider\n".encode(),
            "meta": b"meta " + f"import {RAW_PREFIX}.Provider\n".encode(),
            "all": f"import all {RAW_PREFIX}.Provider\n".encode(),
            "trailing-token": f"import {RAW_PREFIX}.Provider junk\n".encode(),
            "trailing-comment": f"import {RAW_PREFIX}.Provider -- no\n".encode(),
            "body-import": f"import {RAW_PREFIX}.Provider\nimport {RAW_PREFIX}.Existing\ndef x : Nat := 0\nimport {RAW_PREFIX}.Dependency\n".encode(),
        }
        for kind, replacement in variants.items():
            with self.subTest(kind=kind):
                self.fixture(count=1)
                self.write(PARENT_REL, replacement + b"\ndef destination : Nat := 8\n")
                before = self.snapshot()
                result = self.run_cli(*self.merge_arguments(1))
                expected = ("invalid module import modifiers" if kind == "module-order"
                            else "module headers" if kind.startswith("module-") or kind == "module"
                            else {
                    "prelude": "prelude headers",
                    "public": "public/meta imports", "meta": "public/meta imports",
                    "all": "trailing tokens", "trailing-token": "trailing tokens",
                    "trailing-comment": "trailing comment",
                    "body-import": "body import"}[kind])
                self.assert_failure(result, expected)
                self.assert_snapshot(before)

    def test_fake_import_comments_literals_nested_and_private_body_pass(self):
        self.fixture(count=1)
        parent = (self.root / PARENT_REL).read_bytes()
        parent += (b'\n/- outer import Hagi.MergeP3ProtectedRaw.Nope\n'
                   b'/- nested import Also.Nope -/ -- still nested -/\n'
                   b'/-- doc import Fake.Nope -/\n'
                   b'def fake : String := "import Fake.Nope -- /-"\n'
                   b"def quoted : Char := 'i'\n")
        self.write(PARENT_REL, parent)
        result = self.run_cli(*self.merge_arguments(1))
        self.assertEqual(result.returncode, 0, output_text(result))
        merged = (self.root / PARENT_REL).read_bytes()
        self.assertIn(b'import Fake.Nope -- /-', merged)
        self.assertIn(b"/- outer import Hagi.MergeP3ProtectedRaw.Nope", merged)

    def test_invalid_encoding_bom_and_lone_cr_do_not_write(self):
        for kind, corrupt in (
                ("utf8", b"\xff"), ("bom", b"\xef\xbb\xbf"),
                ("lone-cr", b"\r")):
            with self.subTest(kind=kind):
                self.fixture(count=1)
                path = self.root / PARENT_REL
                original = path.read_bytes()
                self.write(PARENT_REL,
                           corrupt + original if kind == "bom" else original + corrupt)
                before = self.snapshot()
                result = self.run_cli(*self.merge_arguments(1))
                self.assert_failure(result, {
                    "utf8": "invalid UTF-8", "bom": "BOM",
                    "lone-cr": "lone CR"}[kind])
                self.assert_snapshot(before)

    def test_repeated_source_or_destination_imports_are_ambiguous(self):
        for target, repeated in (("parent", "Provider"),
                                 ("consumer", "Destination"),
                                 ("root", "Provider")):
            with self.subTest(target=target):
                self.fixture(count=1)
                relative = {"parent": PARENT_REL,
                            "consumer": self.consumer(1),
                            "root": Path("Hagi.lean")}[target]
                raw = (self.root / relative).read_bytes()
                needle = f"import {RAW_PREFIX}.{repeated}".encode()
                self.write(relative, raw.replace(
                    needle, needle + b"\n" + needle, 1))
                before = self.snapshot()
                result = self.run_cli(*self.merge_arguments(1))
                self.assert_failure(result, "ambiguous")
                self.assert_snapshot(before)

    def test_direct_edge_rules_retarget_mix_and_combined_option(self):
        for kind in ("default-missing", "append-present", "mix", "combined"):
            with self.subTest(kind=kind):
                self.fixture(count=1, append=kind == "default-missing")
                if kind == "append-present":
                    self.write(PARENT_REL, (self.root / PARENT_REL).read_bytes().replace(
                        f"import {RAW_PREFIX}.Existing\n".encode(),
                        f"import {RAW_PREFIX}.Provider\nimport {RAW_PREFIX}.Existing\n".encode()))
                before = self.snapshot()
                if kind == "default-missing":
                    arguments = self.merge_arguments(1)
                elif kind == "append-present":
                    arguments = self.merge_arguments(1, append=True)
                elif kind == "mix":
                    arguments = self.merge_arguments(1) + ["--retarget-all"]
                else:
                    arguments = [CHILD_REL, "--append+--retarget=" + str(PARENT_REL)]
                    arguments.insert(1, PARENT_REL)
                result = self.run_cli(*arguments)
                expected = {"default-missing": "DEFAULT receiver",
                            "append-present": "append receiver",
                            "mix": "cannot be mixed"}.get(kind, "unrecognized arguments")
                self.assert_failure(result, expected)
                self.assert_snapshot(before)

    def test_actual_module_header_discovers_without_mutation(self):
        path = REPO / "Hagi" / "Optimization" / "Schelling.lean"
        if not path.is_file():
            self.fail(f"required real module fixture missing: {path}")
        before = path.read_bytes()
        source = merger.parse_source(path)
        self.assertEqual(source.kind, "module")
        self.assertEqual(len(source.imports), 5)
        self.assertTrue(all(line.modified for line in source.imports))
        with self.assertRaisesRegex(merger.MergeError, "module headers"):
            merger.validate_mutation(source)
        self.assertEqual(path.read_bytes(), before)

    def test_every_write_and_provider_delete_rolls_back_raw_bytes(self):
        for fault in ("write-1", "write-2", "write-3", "write-4",
                      "write-5", "delete-before-error",
                      "delete-after-real-unlink-then-error"):
            with self.subTest(fault=fault):
                self.fixture(count=3)
                before = self.snapshot()
                plan = merger.make_plan(
                    self.root / CHILD_REL, self.root / PARENT_REL,
                    retarget_all=True, root=self.root)
                real_write = merger._atomic_write
                calls = [0]
                deleted_before_error = []

                def flaky_write(path, data):
                    calls[0] += 1
                    if calls[0] == int(fault.split("-")[1]):
                        raise OSError("injected write")
                    return real_write(path, data)

                if fault == "delete-before-error":
                    context = patch.object(merger, "_delete",
                                           side_effect=OSError("injected delete"))
                elif fault == "delete-after-real-unlink-then-error":
                    real_delete = merger._delete

                    def delete_then_fail(path):
                        real_delete(path)
                        deleted_before_error.append(not path.exists())
                        raise OSError("injected post-delete failure")

                    context = patch.object(merger, "_delete",
                                           side_effect=delete_then_fail)
                else:
                    context = patch.object(merger, "_atomic_write",
                                           side_effect=flaky_write)
                with context:
                    with self.assertRaisesRegex(merger.MergeError, "all originals restored"):
                        merger.apply_plan(plan)
                if fault == "delete-after-real-unlink-then-error":
                    self.assertEqual(deleted_before_error, [True])
                self.assertTrue((self.root / CHILD_REL).exists())
                self.assert_snapshot(before)

    def test_rollback_failure_is_separately_fatal(self):
        self.fixture(count=1)
        plan = merger.make_plan(
            self.root / CHILD_REL, self.root / PARENT_REL,
            retarget_all=True, root=self.root)
        with patch.object(merger, "_atomic_write",
                          side_effect=OSError("persistent write failure")):
            with self.assertRaisesRegex(merger.MergeError, r"ROLLBACK FAILURE \(fatal\)"):
                merger.apply_plan(plan)


class LeanCliSemantics(unittest.TestCase):
    """Actual fresh lean -R/-o fixture; no production module is imported."""

    @classmethod
    def setUpClass(cls):
        cls.lean = shutil.which("lean")
        cls.lake = shutil.which("lake")
        inherited = os.environ.get("LEAN_PATH", "")
        if not inherited:
            if not cls.lake:
                raise RuntimeError("Lean toolchain unavailable: lake not on PATH")
            result = subprocess.run(
                [cls.lake, "env", "printenv", "LEAN_PATH"], cwd=REPO,
                capture_output=True, text=True, timeout=60)
            if result.returncode != 0 or not result.stdout.strip():
                raise RuntimeError("unable to obtain LEAN_PATH: "
                                   + result.stdout + result.stderr)
            inherited = result.stdout.strip()
        if not cls.lean:
            if not cls.lake:
                raise RuntimeError("Lean toolchain unavailable: lean not on PATH")
            suffix = ".exe" if os.name == "nt" else ""
            candidate = Path(cls.lake).with_name("lean" + suffix)
            if not candidate.is_file():
                raise RuntimeError(f"lean executable not found beside lake: {candidate}")
            cls.lean = str(candidate)
        cls.base_lean_path = inherited
        version = subprocess.run([cls.lean, "--version"], capture_output=True,
                                 text=True, timeout=30)
        if version.returncode != 0:
            raise RuntimeError("lean --version failed: "
                               + version.stdout + version.stderr)
        print(f"LEAN_TOOLCHAIN: {version.stdout.strip()}")

    def setUp(self):
        PACKET.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(
            prefix="merge-module-lean-", dir=PACKET)
        self.root = Path(self.temporary.name).resolve()
        self.commands = 0

    def tearDown(self):
        self.temporary.cleanup()

    def write(self, root, relative, text):
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.encode("utf-8"))

    def source_fixture(self, source, prefix):
        namespace = f"Hagi.{prefix}"
        base_rel = Path(f"Hagi/{prefix}/Base.lean")
        provider_rel = Path(f"Hagi/{prefix}/Provider.lean")
        destination_rel = Path(f"Hagi/{prefix}/Destination.lean")
        one_rel = Path(f"Hagi/{prefix}/UserOne.lean")
        two_rel = Path(f"Hagi/{prefix}/UserTwo.lean")
        self.write(source, base_rel,
                   f"namespace {namespace}\n\ndef baseValue : Nat := 2\n\nend {namespace}\n")
        self.write(source, provider_rel,
                   f"import {namespace}.Base\n\n"
                   f"namespace {namespace}\n\n"
                   "set_option maxRecDepth 129\n\n"
                   "def providerValue : Nat := baseValue + 5\n"
                   "theorem providerValue_eq : providerValue = 7 := by rfl\n\n"
                   "structure ProviderRecord where\n  field : Nat\n\n"
                   "inductive Choice where\n  | left\n  | right\n\n"
                   f"end {namespace}\n")
        self.write(source, destination_rel,
                   f"import {namespace}.Base\n\n"
                   f"namespace {namespace}\n\n"
                   "open Nat\n\n"
                   "def destinationValue : Nat := baseValue + 6\n"
                   "theorem destinationValue_eq : destinationValue = 8 := by rfl\n\n"
                   f"end {namespace}\n")
        self.write(source, one_rel,
                   f"import {namespace}.Provider\nimport {namespace}.Destination\n\n"
                   f"theorem {namespace}.userOne : {namespace}.providerValue + "
                   f"{namespace}.destinationValue = 15 := by rfl\n")
        self.write(source, two_rel,
                   f"import {namespace}.Provider\nimport {namespace}.Destination\n\n"
                   f"def {namespace}.userTwo : {namespace}.ProviderRecord := "
                   f"{{ field := {namespace}.providerValue }}\n")
        self.write(source, "Hagi.lean",
                   f"import {namespace}.Provider\nimport {namespace}.Destination\n"
                   f"import {namespace}.UserOne\nimport {namespace}.UserTwo\n\n"
                   f"def {namespace}.rootValue : Nat := {namespace}.userTwo.field\n")
        if prefix.endswith("Default"):
            # DEFAULT requires the destination-to-provider direct edge.
            destination = destination_rel
            raw = (source / destination).read_bytes().replace(
                f"import {namespace}.Base\n".encode(),
                f"import {namespace}.Provider\nimport {namespace}.Base\n".encode())
            (source / destination).write_bytes(raw)
        return [base_rel, provider_rel, destination_rel, one_rel, two_rel,
                Path("Hagi.lean")]

    def manifest(self, prefix):
        namespace = f"Hagi.{prefix}"
        local = ["providerValue", "providerValue_eq",
                 "ProviderRecord", "ProviderRecord.mk", "ProviderRecord.field",
                 "ProviderRecord.rec", "Choice", "Choice.left", "Choice.right",
                 "Choice.rec", "destinationValue", "destinationValue_eq",
                 "baseValue", "userOne", "userTwo", "rootValue"]
        return [f"{namespace}.{name}" for name in local], namespace

    def witness(self, source, prefix):
        names, _ = self.manifest(prefix)
        quoted = ",\n    ".join("`" + name for name in names)
        text = f"""import Lean
import ImportGraph.Lean.Environment
import Hagi
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let names : List Name := [
    {quoted}]
  for name in names do
    let some ci := env.find? name | throwError "MISSING {{name}}"
    let body := match ci.value? (allowOpaque := true) with
      | some value => toString (hash value)
      | none => "NONE"
    let owner := (env.getModuleFor? name).getD Name.anonymous
    IO.println s!"{{name}}|{{hash ci.type}}|{{body}}|{{owner}}"
"""
        self.write(source, "Witness.lean", text)

    def environment(self, build):
        env = os.environ.copy()
        # Drop inherited sandbox credentials from subprocess environments.
        for key in list(env):
            if any(marker in key for marker in
                   ("KEY", "SECRET", "TOKEN", "PASSWORD")):
                del env[key]
        env["LEAN_PATH"] = str(build) + os.pathsep + self.base_lean_path
        return env

    def run_process(self, command, cwd, env=None, timeout=90):
        self.commands += 1
        result = subprocess.run(command, cwd=cwd, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout)
        if result.returncode != 0:
            print("FAILED COMMAND rc=" + str(result.returncode) + ": "
                  + " ".join(map(str, command)), flush=True)
            print(output_text(result), flush=True)
        return result

    def compile(self, source, build, modules):
        build.mkdir(parents=True, exist_ok=True)
        for relative in modules:
            target = build / relative.with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            result = self.run_process(
                [self.lean, "-R", str(source), "-o", str(target),
                 str(source / relative)], source, self.environment(build))
            if result.returncode != 0:
                raise AssertionError(f"fresh compile failed for {relative}: "
                                     + output_text(result))

    def compile_witness(self, source, build, modules, prefix):
        self.compile(source, build, modules)
        self.witness(source, prefix)
        result = self.run_process(
            [self.lean, "-R", str(source), "-o", str(build / "Witness.olean"),
             str(source / "Witness.lean")], source, self.environment(build))
        if result.returncode != 0:
            raise AssertionError("Environment.find? witness failed: "
                                 + output_text(result))
        rows = {}
        output = result.stdout.decode("utf-8")
        for line in output.splitlines():
            fields = line.split("|")
            if len(fields) != 4:
                raise AssertionError(f"unparsed witness row: {line!r}; all={output!r}")
            name, type_hash, body, owner = fields
            if name in rows:
                raise AssertionError(f"duplicate witness row {name}")
            rows[name] = (type_hash, body, owner)
        expected, _ = self.manifest(prefix)
        if list(rows) != expected:
            raise AssertionError(f"manifest mismatch: {list(rows)} != {expected}")
        return rows

    def cli(self, source, prefix, append):
        namespace = f"Hagi.{prefix}"
        arguments = [sys.executable, str(SCRIPT),
                     f"Hagi/{prefix}/Provider.lean",
                     f"Hagi/{prefix}/Destination.lean",
                     "--retarget-all"]
        if append:
            arguments.append("--append")
        result = self.run_process(arguments, source, timeout=60)
        if result.returncode != 0:
            raise AssertionError(f"public merge CLI failed ({namespace}): "
                                 + output_text(result))
        if (source / f"Hagi/{prefix}/Provider.lean").exists():
            raise AssertionError("provider source still present after public CLI")
        self.assertFalse((source / "Hagi/MergeP3ProtectedOther.lean").exists())

    def check_semantics(self, mode):
        prefix = f"MergeP3Protected{mode}"
        self.assertFalse((REPO / "Hagi" / prefix).exists())
        before_source = self.root / "before" / "source"
        before_build = self.root / "before" / "build"
        after_source = self.root / "after" / "source"
        after_build = self.root / "after" / "build"
        modules = self.source_fixture(before_source, prefix)
        shutil.copytree(before_source, after_source)
        before = self.compile_witness(
            before_source, before_build, modules, prefix)
        self.cli(after_source, prefix, append=mode == "Append")
        self.assertFalse((after_source / f"Hagi/{prefix}/Provider.olean").exists())
        after = self.compile_witness(
            after_source, after_build, modules[:1] + modules[2:], prefix)
        names, namespace = self.manifest(prefix)
        self.assertEqual(list(before), names)
        provider_names = {
            namespace + ".providerValue", namespace + ".providerValue_eq",
            namespace + ".ProviderRecord", namespace + ".ProviderRecord.mk",
            namespace + ".ProviderRecord.field", namespace + ".ProviderRecord.rec",
            namespace + ".Choice", namespace + ".Choice.left",
            namespace + ".Choice.right", namespace + ".Choice.rec"}
        expected_before_owners = {}
        expected_after_owners = {}
        for name in names:
            local = name.removeprefix(namespace + ".")
            if name in provider_names:
                before_owner = namespace + ".Provider"
                after_owner = namespace + ".Destination"
            else:
                before_owner = after_owner = {
                    "baseValue": namespace + ".Base",
                    "destinationValue": namespace + ".Destination",
                    "destinationValue_eq": namespace + ".Destination",
                    "userOne": namespace + ".UserOne",
                    "userTwo": namespace + ".UserTwo",
                    "rootValue": "Hagi"}[local]
            expected_before_owners[name] = before_owner
            expected_after_owners[name] = after_owner
        self.assertEqual({name: row[2] for name, row in before.items()},
                         expected_before_owners)
        self.assertEqual({name: row[2] for name, row in after.items()},
                         expected_after_owners)
        for name in names:
            self.assertEqual(before[name][:2], after[name][:2],
                             f"type/value presence+hash changed: {name}")

        old_path = after_source / "OldPath.lean"
        self.write(after_source, "OldPath.lean",
                   f"import {namespace}.Provider\n")
        rejected = self.run_process(
            [self.lean, "-R", str(after_source), "-o",
             str(after_build / "OldPath.olean"), str(old_path)],
            after_source, self.environment(after_build))
        print(f"LEAN_CONTROL {mode} stale-provider rc={rejected.returncode}")
        self.assertNotEqual(rejected.returncode, 0)
        rejection_text = output_text(rejected).lower()
        self.assertTrue("unknown" in rejection_text or "does not exist" in rejection_text,
                        rejection_text)
        self.assertIn((namespace + ".Provider").lower(), rejection_text)

        for mutant_kind in ("definition", "theorem"):
            mutant_source = self.root / mutant_kind / "source"
            mutant_build = self.root / mutant_kind / "build"
            shutil.copytree(after_source, mutant_source)
            (mutant_source / "OldPath.lean").unlink()
            destination = mutant_source / f"Hagi/{prefix}/Destination.lean"
            raw = destination.read_bytes()
            if mutant_kind == "definition":
                changed = raw.replace(b"def providerValue : Nat := baseValue + 5",
                                      b"def providerValue : Nat := 5 + baseValue")
                self.assertNotEqual(changed, raw)
            else:
                changed = raw.replace(
                    b"theorem providerValue_eq : providerValue = 7 := by rfl",
                    b"theorem providerValue_eq : providerValue = 7 := by\n"
                    b"  have witness : providerValue = 7 := Eq.refl 7\n"
                    b"  exact witness")
                self.assertNotEqual(changed, raw)
            destination.write_bytes(changed)
            mutant = self.compile_witness(
                mutant_source, mutant_build, modules[:1] + modules[2:], prefix)
            name = (namespace + ".providerValue" if mutant_kind == "definition"
                    else namespace + ".providerValue_eq")
            self.assertEqual(after[name][0], mutant[name][0],
                             f"{mutant_kind} negative control changed type")
            self.assertNotEqual(after[name][1], mutant[name][1],
                                f"{mutant_kind} body control did not differ")
            print(f"LEAN_CONTROL {mode} {mutant_kind}-body hashes "
                  f"{after[name][1]} != {mutant[name][1]}")

        if mode == "Append":
            early_source = self.root / "early" / "source"
            early_build = self.root / "early" / "build"
            shutil.copytree(before_source, early_source)
            destination = early_source / f"Hagi/{prefix}/Destination.lean"
            raw = destination.read_bytes().replace(
                b"def destinationValue : Nat := baseValue + 6",
                b"def earlyReference : Nat := providerValue\n"
                b"def destinationValue : Nat := baseValue + 6")
            destination.write_bytes(raw)
            self.cli(early_source, prefix, append=True)
            self.compile(early_source, early_build, modules[:1])
            failed = self.run_process(
                [self.lean, "-R", str(early_source), "-o",
                 str(early_build / f"Hagi/{prefix}/Destination.olean"),
                 str(destination)], early_source, self.environment(early_build))
            print(f"LEAN_CONTROL Append earlier-reference rc={failed.returncode}")
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("unknown identifier", output_text(failed).lower())
        print(f"LEAN_MODE {mode}: PASS; subprocesses={self.commands}")

    def test_real_lean_default_public_cli(self):
        self.check_semantics("Default")

    def test_real_lean_append_public_cli_and_early_reference_control(self):
        self.check_semantics("Append")


def main():
    # One UTF-8 stream: only the explicit counted PASS gate.
    sys.stdout.reconfigure(encoding="utf-8")
    result = unittest.TextTestRunner(
        stream=sys.stdout, verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__]))
    if result.wasSuccessful() and result.testsRun >= 10:
        print(f"MERGEMODULE: PASS ({result.testsRun} tests; Lean modes=2)")
        return 0
    print(f"MERGEMODULE: FAIL ({result.testsRun} tests)", file=sys.stdout)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
