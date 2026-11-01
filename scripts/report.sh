#!/usr/bin/env bash
# Отчёты (не гейты): Metrics + ClosureReport — ручной запуск
python scripts/Metrics.py
python scripts/ClosureReport.py | head -1
