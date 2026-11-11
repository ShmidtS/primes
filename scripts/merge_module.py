#!/usr/bin/env python3
"""Merge one ordinary-source Hagi provider into one receiver, byte-safely.

The supported import grammar is deliberately limited to the plain import
form documented at
https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/.
Module/prelude headers are recognized for graph discovery, never mutated.

Usage (from the source root containing Hagi/ and Hagi.lean):
  python scripts/merge_module.py CHILD PARENT [--append]
      [--retarget FILE ... | --retarget-all]

Rollback covers handled process errors only; it is not crash/power atomicity.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import sys
import tempfile


class MergeError(RuntimeError):
    pass


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int


class Cursor:
    """Small comment/literal-aware cursor, not a Lean body parser."""

    def __init__(self, text: str, label: str, pos: int = 0):
        self.text = text
        self.label = label
        self.pos = pos

    def error(self, message: str) -> MergeError:
        return MergeError(f"{self.label}: {message} at character {self.pos}")

    def skip_trivia(self) -> None:
        text = self.text
        while self.pos < len(text):
            char = text[self.pos]
            if char.isspace():
                self.pos += 1
                continue
            if text.startswith("--", self.pos):
                newline = text.find("\n", self.pos + 2)
                self.pos = len(text) if newline < 0 else newline + 1
                continue
            if text.startswith("/-", self.pos):
                start = self.pos
                self.pos += 2
                depth = 1
                while depth and self.pos < len(text):
                    if text.startswith("/-", self.pos):
                        depth += 1
                        self.pos += 2
                    elif text.startswith("-/", self.pos):
                        depth -= 1
                        self.pos += 2
                    else:
                        self.pos += 1
                if depth:
                    self.pos = start
                    raise self.error("unterminated block comment")
                continue
            return

    def quoted(self, delimiter: str) -> Token:
        start = self.pos
        self.pos += 1
        while self.pos < len(self.text):
            char = self.text[self.pos]
            if char == "\\":
                self.pos += 2
                if self.pos > len(self.text):
                    self.pos = start
                    raise self.error("unterminated literal escape")
                continue
            self.pos += 1
            if char == delimiter:
                return Token(self.text[start:self.pos], start, self.pos)
            if delimiter == "'" and char in "\r\n":
                break
        self.pos = start
        raise self.error("unterminated string/character literal")

    def next_token(self) -> Token | None:
        self.skip_trivia()
        if self.pos >= len(self.text):
            return None
        start = self.pos
        char = self.text[self.pos]
        if char in "\"'":
            return self.quoted(char)
        if _identifier_start(char):
            self.pos += 1
            while self.pos < len(self.text):
                char = self.text[self.pos]
                if _identifier_continue(char):
                    self.pos += 1
                    continue
                if (char == "." and self.pos + 1 < len(self.text)
                        and _identifier_start(self.text[self.pos + 1])):
                    self.pos += 2
                    continue
                break
            return Token(self.text[start:self.pos], start, self.pos)
        self.pos += 1
        return Token(char, start, self.pos)


def _identifier_start(char: str) -> bool:
    return char == "_" or char.isalpha()


def _identifier_continue(char: str) -> bool:
    return (char.isalnum() or char in "_'!?"
            or (ord(char) >= 128 and not char.isspace()))


_MODULE_NAME = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


@dataclass(frozen=True)
class ImportLine:
    name: str
    line_start: int
    line_end: int
    end_with_eol: int
    eol: str
    trailing_comment: bool
    modified: bool


@dataclass
class Source:
    path: Path
    raw: bytes
    text: str
    kind: str
    imports: list[ImportLine]
    body_start: int

    @property
    def body_start_byte(self) -> int:
        return _byte_at(self.text, self.body_start)

    @property
    def body(self) -> bytes:
        return self.raw[self.body_start_byte:]


def _byte_at(text: str, position: int) -> int:
    return len(text[:position].encode("utf-8"))


def _decode(path: Path, raw: bytes, mutation: bool) -> str:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise MergeError(f"{path}: UTF-8 BOM is not supported")
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise MergeError(f"{path}: invalid UTF-8: {exc}") from exc
    if mutation:
        for index, byte in enumerate(raw):
            if byte == 13 and (index + 1 == len(raw) or raw[index + 1] != 10):
                raise MergeError(f"{path}: lone CR at byte {index}")
    return text


def _line_boundary(text: str, position: int) -> tuple[int, int, str]:
    line_end = text.find("\n", position)
    if line_end < 0:
        line_end = len(text)
    content_end = line_end
    if content_end > position and text[content_end - 1] == "\r":
        content_end -= 1
    eol = text[content_end:line_end + 1] if line_end < len(text) else ""
    return content_end, line_end + (1 if line_end < len(text) else 0), eol


def _module_import_ahead(cursor: Cursor, token: Token) -> bool:
    probe = Cursor(cursor.text, cursor.label, token.start)
    current = probe.next_token()
    if current is not None and current.text == "public":
        current = probe.next_token()
    if current is not None and current.text == "meta":
        current = probe.next_token()
    return current is not None and current.text == "import"


def parse_source(path: Path, raw: bytes | None = None,
                 mutation: bool = False) -> Source:
    if raw is None:
        raw = path.read_bytes()
    text = _decode(path, raw, mutation)
    cursor = Cursor(text, str(path))
    token = cursor.next_token()
    kind = "ordinary"
    if token is not None and token.text in {"module", "prelude"}:
        kind = token.text
        content_end, _, _ = _line_boundary(text, token.end)
        if text[token.end:content_end].strip(" \t"):
            raise MergeError(f"{path}: trailing tokens after {kind}")
        token = cursor.next_token()

    imports: list[ImportLine] = []
    occupied_lines: set[int] = set()
    while token is not None:
        first = token
        modified = False
        public = False
        meta = False
        if (kind == "ordinary" and token.text in {"public", "meta"}
                and _module_import_ahead(cursor, token)):
            raise MergeError(
                f"{path}: public/meta imports require a module header")
        if kind == "module" and token.text in {"public", "meta"}:
            if not _module_import_ahead(cursor, token):
                probe = Cursor(cursor.text, cursor.label, token.start)
                probe.next_token()
                following = probe.next_token()
                if following is not None and following.text in {"public", "meta", "import"}:
                    raise MergeError(f"{path}: invalid module import modifiers")
                break
            modified = True
            if token.text == "public":
                public = True
                token = cursor.next_token()
            if token is not None and token.text == "meta":
                meta = True
                modified = True
                token = cursor.next_token()
        if token is None or token.text != "import":
            if public or meta:
                raise MergeError(f"{path}: invalid module import modifiers")
            break
        if kind != "module" and modified:
            raise MergeError(f"{path}: modified import in ordinary source")
        token = cursor.next_token()
        all_modifier = False
        if kind == "module" and token is not None and token.text == "all":
            all_modifier = True
            modified = True
            token = cursor.next_token()
        if token is None or not _MODULE_NAME.fullmatch(token.text):
            found = "end of file" if token is None else repr(token.text)
            raise MergeError(f"{path}: unsupported import identifier {found}")
        line_start = text.rfind("\n", 0, first.start) + 1
        if text[line_start:first.start].strip(" \t"):
            raise MergeError(f"{path}: import must start its own line")
        if line_start in occupied_lines:
            raise MergeError(f"{path}: multiple imports on one line")
        occupied_lines.add(line_start)
        content_end, end_with_eol, eol = _line_boundary(text, token.end)
        remainder = text[token.end:content_end]
        stripped = remainder.lstrip(" \t")
        trailing_comment = False
        if stripped:
            if not (stripped.startswith("--") or stripped.startswith("/-")):
                raise MergeError(
                    f"{path}: trailing tokens after import {token.text}")
            trailing_comment = True
        imports.append(ImportLine(
            token.text, line_start, content_end, end_with_eol, eol,
            trailing_comment, modified or all_modifier))
        token = cursor.next_token()

    if imports:
        body_start = imports[-1].end_with_eol
    else:
        body_start = 0
    return Source(path, raw, text, kind, imports, body_start)


def validate_mutation(source: Source) -> None:
    if source.kind != "ordinary":
        raise MergeError(
            f"{source.path}: {source.kind} headers cannot be mutated")
    for imported in source.imports:
        if imported.modified:
            raise MergeError(
                f"{source.path}: public/meta/all imports cannot be mutated")
        if imported.trailing_comment:
            raise MergeError(
                f"{source.path}: trailing comment on import {imported.name}")
    cursor = Cursor(source.text, str(source.path), source.body_start)
    while True:
        token = cursor.next_token()
        if token is None:
            return
        if token.text == "import":
            raise MergeError(
                f"{source.path}: genuine body import at character {token.start}")


def _canonical_file(path: Path, root: Path) -> Path:
    candidate = Path(os.path.abspath(os.path.normpath(os.fspath(path))))
    probe = candidate
    while True:
        if probe.is_symlink() or (
                hasattr(probe, "is_junction") and probe.is_junction()):
            raise MergeError(f"{path}: symbolic links are not accepted")
        if probe == probe.parent:
            break
        probe = probe.parent
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise MergeError(f"{path}: missing canonical source: {exc}") from exc
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise MergeError(f"{path}: source is outside {root}") from exc
    if not resolved.is_file():
        raise MergeError(f"{path}: not a regular source file")
    return resolved


def _path_key(path: Path) -> str:
    return os.path.normcase(os.fspath(path))


def _module_from_path(path: Path, root: Path) -> str:
    relative = path.relative_to(root)
    if relative == Path("Hagi.lean"):
        return "Hagi"
    if len(relative.parts) < 2 or relative.parts[0] != "Hagi" \
            or relative.suffix != ".lean":
        raise MergeError(f"{path}: selected file is not a Hagi source module")
    name = "Hagi." + ".".join(relative.with_suffix("").parts[1:])
    if not _MODULE_NAME.fullmatch(name):
        raise MergeError(f"{path}: unsupported module filename")
    return name


def _discover(root: Path) -> dict[str, Source]:
    hagi = root / "Hagi"
    if not hagi.is_dir():
        raise MergeError(f"{root}: missing Hagi source directory")
    if not (root / "Hagi.lean").is_file():
        raise MergeError(f"{root / 'Hagi.lean'}: missing Root source")
    paths = sorted(hagi.rglob("*.lean")) + [root / "Hagi.lean"]
    sources: dict[str, Source] = {}
    for path in paths:
        canonical = _canonical_file(path, root)
        name = _module_from_path(canonical, root)
        if name in sources:
            raise MergeError(f"{name}: duplicate canonical module path")
        sources[name] = parse_source(canonical)
    if "Hagi" not in sources:
        raise MergeError(f"{root / 'Hagi.lean'}: missing Root source")
    for name, source in sources.items():
        for imported in source.imports:
            target = imported.name
            if (target == "Hagi" or target.startswith("Hagi.")) \
                    and target not in sources:
                raise MergeError(f"{name}: missing internal source {target}")
    return sources


def _graph(sources: dict[str, Source]) -> dict[str, list[str]]:
    return {
        name: [line.name for line in source.imports
               if line.name == "Hagi" or line.name.startswith("Hagi.")]
        for name, source in sources.items()
    }


def _require_acyclic(graph: dict[str, list[str]], phase: str) -> None:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(name: str) -> None:
        if state.get(name) == 2:
            return
        if state.get(name) == 1:
            begin = stack.index(name)
            cycle = stack[begin:] + [name]
            raise MergeError(f"{phase} dependency cycle: {' -> '.join(cycle)}")
        state[name] = 1
        stack.append(name)
        for dependency in graph.get(name, []):
            visit(dependency)
        stack.pop()
        state[name] = 2

    for name in sorted(graph):
        visit(name)


def _import_occurrences(source: Source, child: str, parent: str) -> None:
    for module in (child, parent):
        count = sum(line.name == module for line in source.imports)
        if count > 1:
            raise MergeError(
                f"{source.path}: ambiguous repeated declaration of {module}")


def _apply_edits(raw: bytes, text: str,
                 edits: list[tuple[int, int, bytes]]) -> bytes:
    result = raw
    previous_start = len(text) + 1
    for start, end, replacement in sorted(
            edits, key=lambda item: (item[0], item[1]), reverse=True):
        if end < start or end > previous_start:
            raise MergeError("internal overlapping source edits")
        start_byte = _byte_at(text, start)
        end_byte = _byte_at(text, end)
        result = result[:start_byte] + replacement + result[end_byte:]
        previous_start = start
    return result


def _remove_or_retarget(source: Source, child: str,
                        parent: str) -> bytes:
    occurrences = [line for line in source.imports if line.name == child]
    if len(occurrences) != 1:
        raise MergeError(f"{source.path}: expected exactly one import {child}")
    parent_count = sum(line.name == parent for line in source.imports)
    if parent_count > 1:
        raise MergeError(f"{source.path}: ambiguous repeated import {parent}")
    line = occurrences[0]
    if parent_count:
        edit = (line.line_start, line.end_with_eol, b"")
    else:
        edit = (line.line_start, line.line_end,
                f"import {parent}".encode("utf-8"))
    return _apply_edits(source.raw, source.text, [edit])


def _join(left: bytes, right: bytes, eol: bytes) -> bytes:
    if left and right and left[-1:] not in {b"\n", b"\r"} \
            and right[:1] not in {b"\n", b"\r"}:
        return left + eol + right
    return left + right


def _parent_output(source: Source, provider: Source, child: str,
                   parent: str, append: bool) -> bytes:
    source_count = sum(line.name == child for line in source.imports)
    parent_count = sum(line.name == parent for line in source.imports)
    if parent_count:
        raise MergeError(f"{source.path}: receiver has a self import {parent}")
    if append and source_count:
        raise MergeError(f"{source.path}: --append rejects direct import {child}")
    if not append and source_count != 1:
        raise MergeError(f"{source.path}: DEFAULT requires direct import {child}")
    if source_count > 1:
        raise MergeError(f"{source.path}: ambiguous repeated import {child}")

    remaining = [line for line in source.imports if line.name != child]
    final_names = {line.name for line in remaining}
    additions: list[str] = []
    for line in provider.imports:
        if line.name != parent and line.name not in final_names:
            additions.append(line.name)
            final_names.add(line.name)

    edits: list[tuple[int, int, bytes]] = []
    if source_count:
        imported = next(line for line in source.imports if line.name == child)
        edits.append((imported.line_start, imported.end_with_eol, b""))
        fallback_position = imported.line_start
        fallback_eol = imported.eol
    else:
        fallback_position = source.body_start
        fallback_eol = ""

    if additions:
        if remaining:
            adjacent = remaining[-1]
            insertion = adjacent.end_with_eol
            eol = adjacent.eol or fallback_eol
        else:
            adjacent = None
            insertion = fallback_position
            eol = fallback_eol
        if not eol:
            eol = next((line.eol for line in provider.imports if line.eol), "")
        if not eol:
            match = re.search(rb"\r\n|\n", source.raw)
            eol = match.group(0).decode("ascii") if match else "\n"
        blob = "".join(f"import {name}{eol}" for name in additions)
        if adjacent is not None and not adjacent.eol:
            blob = eol + blob
        edits.append((insertion, insertion, blob.encode("utf-8")))

    header = _apply_edits(source.raw[:source.body_start_byte],
                          source.text[:source.body_start], edits)
    separator = source.imports[-1].eol if source.imports else ""
    if append:
        separator = separator or next(
            (line.eol for line in provider.imports if line.eol), "\n")
        return _join(header + source.body, provider.body,
                     separator.encode("ascii"))
    separator = next((line.eol for line in provider.imports if line.eol),
                     separator or "\n")
    merged_provider = _join(header, provider.body,
                            separator.encode("ascii"))
    return _join(merged_provider, source.body,
                 separator.encode("ascii"))


@dataclass
class MergePlan:
    root: Path
    child: str
    parent: str
    snapshots: dict[Path, bytes]
    outputs: dict[Path, bytes | None]
    operations: list[Path]

    def output_hashes(self) -> dict[Path, str]:
        return {path: hashlib.sha256(data).hexdigest()
                for path, data in self.outputs.items() if data is not None}


def make_plan(child_path: Path, parent_path: Path, *, append: bool = False,
              retargets: list[Path] | None = None,
              retarget_all: bool = False, root: Path | None = None) -> MergePlan:
    root = (Path.cwd() if root is None else root).resolve(strict=True)
    sources = _discover(root)
    by_path = {_path_key(source.path): name for name, source in sources.items()}
    child_path = _canonical_file(child_path, root)
    parent_path = _canonical_file(parent_path, root)
    for path in (child_path, parent_path):
        if _path_key(path) not in by_path:
            raise MergeError(f"{path}: selected path is not a discovered module")
    child = by_path[_path_key(child_path)]
    parent = by_path[_path_key(parent_path)]
    if child == "Hagi" or parent == "Hagi" or child == parent:
        raise MergeError("provider/receiver must be distinct non-Root modules")

    explicit = [] if retargets is None else retargets
    if retarget_all and explicit:
        raise MergeError("--retarget-all cannot be mixed with --retarget")
    canonical_targets: list[Path] = []
    seen: set[str] = set()
    for path in explicit:
        canonical = _canonical_file(path, root)
        key = _path_key(canonical)
        if key in seen or any(canonical.exists() and other.exists()
                              and os.path.samefile(canonical, other)
                              for other in canonical_targets):
            raise MergeError(f"{path}: duplicate retarget path/alias")
        seen.add(key)
        if key not in by_path:
            raise MergeError(f"{path}: retarget is not a Hagi source module")
        if by_path[key] in {child, parent, "Hagi"}:
            raise MergeError(f"{path}: retarget must be non-C/P/Root")
        canonical_targets.append(canonical)

    graph = _graph(sources)
    _require_acyclic(graph, "pre-existing")
    importers = {name for name, deps in graph.items() if child in deps}
    if "Hagi" not in importers:
        raise MergeError(f"Root Hagi.lean does not directly import {child}")
    if not append and parent not in importers:
        raise MergeError(f"DEFAULT receiver {parent} must directly import {child}")
    if append and parent in importers:
        raise MergeError("--append receiver must not directly import provider")

    required = importers - {parent, "Hagi"}
    supplied = {by_path[_path_key(path)] for path in canonical_targets}
    if not retarget_all and supplied != required:
        missing = sorted(required - supplied)
        extra = sorted(supplied - required)
        raise MergeError(
            f"retarget coverage mismatch; missing={missing}, extra={extra}")
    retarget_names = sorted(required)

    mutation_names = [child, parent, "Hagi"] + retarget_names
    for name in mutation_names:
        source = sources[name]
        source.text = _decode(source.path, source.raw, mutation=True)
        reparsed = parse_source(source.path, source.raw, mutation=True)
        sources[name] = reparsed
        validate_mutation(reparsed)
        _import_occurrences(reparsed, child, parent)

    parent_output = _parent_output(
        sources[parent], sources[child], child, parent, append)
    root_output = _remove_or_retarget(sources["Hagi"], child, parent)
    retarget_outputs = {
        name: _remove_or_retarget(sources[name], child, parent)
        for name in retarget_names
    }

    post: dict[str, list[str]] = {}
    for name, deps in graph.items():
        if name == child:
            continue
        if name == parent:
            transferred = [dep for dep in graph[child] if dep not in {child, parent}]
            result = [dep for dep in deps if dep != child]
            for dep in transferred:
                if dep not in result:
                    result.append(dep)
        elif name == "Hagi" or name in required:
            result = []
            for dep in deps:
                replacement = parent if dep == child else dep
                if replacement not in result:
                    result.append(replacement)
        else:
            if child in deps:
                raise MergeError(f"{name}: unhandled post-merge provider edge")
            result = list(deps)
        if name == parent and parent in result:
            raise MergeError("post graph would contain receiver self-edge")
        post[name] = result
    _require_acyclic(post, "post-merge")

    outputs: dict[Path, bytes | None] = {
        sources[parent].path: parent_output,
        sources["Hagi"].path: root_output,
    }
    operations = [sources[parent].path, sources["Hagi"].path]
    for name in retarget_names:
        outputs[sources[name].path] = retarget_outputs[name]
        operations.append(sources[name].path)
    outputs[sources[child].path] = None
    snapshots = {sources[name].path: sources[name].raw
                 for name in mutation_names}
    return MergePlan(root, child, parent, snapshots, outputs, operations)


def _atomic_write(path: Path, data: bytes) -> None:
    """Local seam used by fault-injection tests."""
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
                mode="wb", prefix=path.name + ".", suffix=".tmp",
                dir=path.parent, delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def _delete(path: Path) -> None:
    """Local seam used by fault-injection tests."""
    path.unlink()


def apply_plan(plan: MergePlan) -> None:
    try:
        for path in plan.operations:
            data = plan.outputs[path]
            if data is None:
                raise MergeError(f"internal missing output for {path}")
            _atomic_write(path, data)
        _delete(plan.root / Path(*plan.child.split(".")).with_suffix(".lean"))
    except Exception as original:
        failures: list[str] = []
        for path, raw in plan.snapshots.items():
            try:
                _atomic_write(path, raw)
                actual = path.read_bytes()
                if hashlib.sha256(actual).digest() != hashlib.sha256(raw).digest():
                    raise MergeError(f"hash mismatch restoring {path}")
            except Exception as rollback_error:
                failures.append(f"{path}: {rollback_error}")
        if failures:
            raise MergeError(
                f"mutation failed: {original}; ROLLBACK FAILURE (fatal): "
                + "; ".join(failures)) from original
        raise MergeError(f"mutation failed; all originals restored: {original}") \
            from original


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("child", type=Path)
    parser.add_argument("parent", type=Path)
    parser.add_argument("--append", action="store_true")
    parser.add_argument("--retarget", action="append", default=[], type=Path)
    parser.add_argument("--retarget-all", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        plan = make_plan(args.child, args.parent, append=args.append,
                         retargets=args.retarget,
                         retarget_all=args.retarget_all)
        apply_plan(plan)
    except MergeError as exc:
        print(f"merge_module: {exc}", file=sys.stderr)
        return 1
    print(f"merged {plan.child} -> {plan.parent}"
          f" ({'append' if args.append else 'default'}; "
          f"retargets={len(plan.operations) - 2})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
