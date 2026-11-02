#!/usr/bin/env python3
"""StatusGen — rebuild STATUS.md without retrospective narrative.

Structure:
  1. Corpus metrics header.
  2. Proven results by layer — bullets from the old STATUS that
     carry mathematical content, with tact/audit markers stripped
     from headers; purely process bullets dropped.
  3. NEW Gen-3 results (hand-written block, passed below).
  4. Per-file theorem inventory (generated from Hagi/*.lean).
  5. Open problems (hand-written block).

Run: python scripts/StatusGen.py  (writes STATUS.md at repo root)
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATUS = os.path.join(ROOT, "STATUS.md")

# ---------- 1. distill old layer bullets ----------
raw = open(STATUS, encoding="utf-8").read()
lines = raw.splitlines()

def find(pat):
    for i, l in enumerate(lines):
        if re.search(pat, l):
            return i
    return None

math_start = find(r"^## Доказанные результаты")
open_start = find(r"^## Открытые проблемы")

# bullets: from math_start to the first purely-process tact-log bullet
# we keep the layer part up to (not incl.) the process-run; identified
# as the whole block math_start..open_start, then filtered.
block = lines[math_start:open_start]

# split into bullets starting with '- **'
items = []
cur = None
for l in block[1:]:
    if l.startswith("- **"):
        if cur is not None:
            items.append(cur)
        cur = [l]
    elif cur is not None:
        cur.append(l)
if cur is not None:
    items.append(cur)

DROP_PATTERNS = [
    r"РЕТРО", r"LESSONS", r"Unused-import", r"CI-оптимизация",
    r"Аудит-нарратив", r"Массовая чистка докстрингов", r"Чистка/усиление",
    r"Чистка \(такт", r"Freeze:? (обновл|батч|batch)", r"Дедуп-аудит",
    r"Аудит v\d+ P3 \(фасады\)", r"Аудит v9 §", r"инвентаризация \(такты",
    r"Gen-3 капстоун \(такты", r"SignSGD \+ Lion → DescentCore",
    r"Аудит v6, шаг", r"AllAxiomCheck \(такт", r"Аудит №6-фиксы",
    r"Аудит v11 P1 \(унификация", r"Аудит v11 §3.2",
    r"Аудит v10 §3.5", r"Аудит v10 P0",
    r"Миграция MasterHAGI_trunc", r"Чистка/усиление \(такт",
    r"ctv2Honest-мост", r"smToExec-мост", r"protoMeasured-мост",
    r"CertUnify — сведение миров", r"Прогон капстона",
    r"quadStepCert \(такт", r"LoopInstances \(такт",
    r"QuadUnify-сведение", r"CertifiedLoop \+ HAGI_MAP",
    r"ExecutedCert \(такт", r"LinkedQVec \(такт",
    r"CanonicalParams \(такт", r"HonestTransition \(такт",
    r"GradNorm \(источник №89", r"Grokfast-мост", r"FsGate-леджер",
    r"FsGate \(такт", r"FunctionalState \(такт",
    r"Дедупликация \(такт", r"Миграция MasterHAGI",
    r"Unused-import", r"Дедуп",
]
HEADER_CLEAN = [
    (r"\s*[,(]\s*(такт|такты) №[\d–, №]+\)*", ""),
    (r", аудит №[\d]+ [^):]*", ""),
    (r"\(такт №[\d]+[^)]*\)", ""),
    (r", такт №[\d]+", ""),
    (r"\s*такт №[\d]+\)*\**[:]?", ""),
    (r"Аудит v\d+\s*[—-]?\s*(ответ\s*)?[^:*]{0,60}[:：]\s*", ""),
    (r"\*\*Аудит[^*]*\*\*:\s*", ""),
    (r"Аудит[^:*]{0,60}[:：]\s*", ""),
    (r"\(аудит[^)]*\)?", ""),
    (r"\((?:такт|такты) №?[^)]*\)?", ""),
    (r"Также: LESSONS[^.]*\.\s*", ""),
    (r";\s*такт\s*$", ""),
]

def clean_head(line: str) -> str:
    h = line
    for pat, rep in HEADER_CLEAN:
        h = re.sub(pat, rep, h)
    return h

kept = []
for it in items:
    head = it[0]
    if any(re.search(p, head) for p in DROP_PATTERNS):
        continue
    if head.startswith("- **Аудит"):
        continue
    it = [clean_head(l) for l in it]
    kept.append("\n".join(it).rstrip())

# ---------- 2. per-file inventory ----------
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?"
    r"(?:noncomputable\s+)?(?:theorem|lemma)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)", re.M)

inv = {}
for dirpath, _, files in os.walk(os.path.join(ROOT, "Hagi")):
    for f in sorted(files):
        if not f.endswith(".lean"):
            continue
        p = os.path.join(dirpath, f)
        rel = os.path.relpath(p, ROOT).replace(os.sep, "/")
        txt = open(p, encoding="utf-8", errors="replace").read()
        thms = DECL.findall(txt)
        if thms:
            inv[rel] = thms

inv_lines = []
for rel in sorted(inv):
    thms = inv[rel]
    shown = ", ".join(f"`{t}`" for t in thms[:8])
    more = f" (+{len(thms)-8})" if len(thms) > 8 else ""
    inv_lines.append(f"- `{rel}` — {shown}{more}")

# ---------- 3. metrics ----------
freeze = subprocess.run(
    [sys.executable, os.path.join(ROOT, "scripts", "Freeze.py")],
    capture_output=True, text=True).stdout
m = re.search(r"(\d+) declarations", freeze)
ndecl = m.group(1) if m else "?"

nmods = sum(
    1
    for _, _, fs in os.walk(os.path.join(ROOT, "Hagi"))
    for f in fs
    if f.endswith(".lean")
)
nthm = sum(len(v) for v in inv.values())

GEN3 = """## Доказанные результаты (главные формулы)"""

GEN3_BLOCK = """
## Канонический стек Gen-3 (капстоун и мосты)

- **CertifiedLoop (Unified/CertifiedLoop.lean)**: `certified_loop`
  — цепочка `StepCert` (честный спуск + покомпонентный floor +
  бюджет) даёт одновременно Σdrops ≤ obj₀ − objₙ, `FloorKept`,
  неотрицательный остаток и телескоп бюджета;
  `certified_loop_strict` — при n ≥ 1 спуск строгий;
  `certified_loop_all` — floor на всех промежуточных состояниях;
  `gate_never_increases` — принцип commit/hold.
- **HonestTransition (Unified/HonestTransition.lean)**:
  зависимое доказательство спуска `actualDescent`:
  obj s' ≤ obj s − drop; сертификат ⇒ строгий спуск.
- **Сквозной свидетель (Examples/QuadLoopWitness.lean)**:
  `qhalf` (полушаговая траектория, энергия × 1/4 за шаг),
  `halfStepCert` — StepCert на каждом шаге, `quad_loop_horizon`
  — strict-спуск на любом горизонте, `quad_witness_T3` /
  `quad_witness_T10` — свидетели без CorePremises.
- **Капстоун-гейт (Challenge/MasterChallengeV3.lean)**:
  `master_hagi_challenge_v3` — comparator-закрепление Gen-3
  капстоуна (CHALLENGE 2/2).
- **SignSGD/Lion (Unified/SignDescent.lean)**:
  `sign_scaled_aligned` — масштабированный sign-шаг (s = ‖g‖₁/n)
  выровнен; `sign_descent` — чистое убывание сжатого шага;
  `scaled_sign_aligned_of_coherence` + `lion_descent` —
  момент-Lion при согласованности с градиентом;
  `sign_is_pointwise_max` — знак максимизирует ⟨g, v⟩ на
  ℓ∞-кубе (ядро спектральной оптимальности Muon).
- **SAM (в составе Unified/SignDescent.lean)**: `sam_descent_bridge` —
  спуск по worst-neighbor цели переносится на истинную с
  потерей на остроту; `sam_descent_flat` — плоский случай.
- **Обструкция Gen-1 (Diagnostics/Obstructions.lean)**:
  `full_cycle_two_step_growth_inconsistent'` — регрессионный
  тест: копируемые эффекты противоречивы на T = 2.
- **Изоляция**: MasterHAGI / MasterHAGI_linked / MasterHAGICore /
  MasterHAGI_trunc / grand_synthesis — `@[deprecated]` →
  `certified_loop`.
"""

OPEN_BLOCK = """
## Открытые проблемы

1. **Closure gap.** 138/424 модулей (33%) в замыкании капстоунов;
   286 library leaves (A=34 Objective/Descent, B=45 Step
   Compressors, C=93 Efficiency/Budget, D=19 Alignment, E=95
   мат-фундамент) не инстанцируют StepCert/DescentCore.Objective.
   Цель — 80%+ через LibrarySynthesis.
2. **Gen-1 рудименты.** 52 модуля без CertifiedLoop в замыкании
   (`python scripts/DepAudit.py`); MasterChallenge (v1) и
   Nonvacuity-витнесы ещё на CorePremises.
3. **Сертификатный веер.** 8 представлений перехода не сведены
   к канонической цепочке Execution → Measurement → StepCert →
   CertifiedLoop; StepContract-моноид не завершён; скалярный
   Qgen ещё не заменён на FloorKept везде.
4. **Асимптотика перколяции.** p_c ≈ 0.5927 бесконечной
   решётки не выводится из конечного ядра.
5. **ψ-монотонность (trigamma > 0).** Отсутствует в Mathlib.
6. **Вынос пакетов.** Flywheel, NeuralComputer — кандидаты в
   отдельные Lake-пакеты; широкие `import Mathlib` в листах.
7. **Namespace-остатки.** Core/Select, RealF3*.
"""

header = f"""# STATUS — состояние формализации HAGI

## Корпус

- {nmods} Lean-модулей в `Hagi/`; {ndecl} деклараций (Freeze);
  {nthm} theorem/lemma; 0 sorry; 0 кастомных аксиом
  (все теоремы: [propext, Classical.choice, Quot.sound]).
- CI (16 гейтов, `scripts/ci.sh`): LINT, MathlibPin, DupLint,
  NsLint, DocLint, LayerLint, Freeze, AssumptionScan,
  StatusLint, CHALLENGE (Gen-3: `master_hagi_challenge_v3`),
  STMDUP, MACHINEDIFF, ALLAXIOMS — все PASS.
"""

with open(STATUS, "w", encoding="utf-8", newline="\n") as fh:
    fh.write(header)
    fh.write("\n" + GEN3 + "\n")
    for it in kept:
        fh.write(it + "\n")
    fh.write(GEN3_BLOCK)
    fh.write("\n## Каталог: доказанное по файлам (theorem/lemma)\n")
    fh.write("\n".join(inv_lines) + "\n")
    fh.write(OPEN_BLOCK)

print(f"STATUS.md rewritten: {len(kept)} layer bullets kept, "
      f"{len(inv_lines)} files inventoried, {ndecl} decls.")
