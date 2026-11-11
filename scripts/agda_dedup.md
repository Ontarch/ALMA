# `agda_dedup.py` Quick Reference

A single-file tool for auditing semantic equivalence and duplication in Agda codebases.

> **Prerequisites:** Requires Agda 2.8+ and Python 3. Standard library only, no `pip install` needed.

---

## 🚀 TL;DR (Basic Workflow)

Run from your project root (e.g., `/home/zgah/ALMA`):

```bash
# 1. Fast Scan (No compilation, finds candidates in seconds)
python3 agda_dedup.py scan --root . --filter /Real

# 2. Verify semantic equality (Compiles probes for same-file candidates)
python3 agda_dedup.py l1 --root . --filter /Real --jobs 3 --out l1_results.json

# 3. Test if a lemma can be replaced by an external one (Requires a JSON cases file)
python3 agda_dedup.py l2 --root . --cases my_cases.json --jobs 2

# 4. Cross-check against agda-stdlib
python3 agda_dedup.py cross --root . --filter /Real --drop-qualified
