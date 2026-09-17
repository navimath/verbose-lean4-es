#!/usr/bin/env python3
"""Rewrite /-- info: ... -/ docstrings to match actual #guard_msgs output.

Usage: update_guards.py <source.lean> <lean-json-output>
Reads Lean's --json diagnostics, and for every failing #guard_msgs replaces the
docstring immediately above it with the message Lean actually produced.
"""
import json, sys

PREFIX = "❌️ Docstring on `#guard_msgs` does not match generated message:\n\n"

src, jsonout = sys.argv[1], sys.argv[2]

fixes = {}
with open(jsonout, encoding="utf-8") as f:
    for raw in f:
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        rec = json.loads(raw)
        if rec.get("severity") != "error":
            continue
        data = rec.get("data", "")
        if not data.startswith(PREFIX):
            continue
        fixes[rec["pos"]["line"]] = data[len(PREFIX):]

with open(src, encoding="utf-8") as f:
    lines = f.read().split("\n")

applied = skipped = 0
for guard_line in sorted(fixes, reverse=True):       # bottom-up keeps indices valid
    idx = guard_line - 1                              # 0-indexed #guard_msgs line
    if not lines[idx].lstrip().startswith("#guard_msgs"):
        print(f"  ! line {guard_line}: expected #guard_msgs, got {lines[idx]!r}")
        skipped += 1
        continue
    j = idx - 1
    stripped = lines[j].strip()
    if stripped.startswith("/--") and stripped.endswith("-/") and len(stripped) > 5:
        open_i = close_i = j                          # single-line docstring
    elif stripped == "-/":
        close_i = j
        open_i = None
        for k in range(j - 1, max(j - 400, -1), -1):
            if lines[k].strip().startswith("/--"):
                open_i = k
                break
        if open_i is None:
            print(f"  ! line {guard_line}: no opening /-- found")
            skipped += 1
            continue
    else:
        print(f"  ! line {guard_line}: unrecognized docstring end {stripped!r}")
        skipped += 1
        continue
    lines[open_i:close_i + 1] = ["/--"] + fixes[guard_line].split("\n") + ["-/"]
    applied += 1

with open(src, "w", encoding="utf-8") as f:
    f.write("\n".join(lines))

print(f"applied {applied}, skipped {skipped}, of {len(fixes)} failures")
