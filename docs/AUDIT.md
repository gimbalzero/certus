# Audit reports

A proof checker's verdict is only as useful as your knowledge of *what* it accepted. `certus check --report FILE` writes that down: a JSON report you can read, diff, archive or check in CI.

```bash
certus check export.ndjson MyProject.main_theorem --report report.json
```

For the round-1 certificate of the [race](../benchmarks/race):

```json
{
  "format": "certus-report-v1",
  "checker": "cfae1106…",
  "export": { "blake3": "b9cc376d…", "format": "3.1.0", "lean_version": "4.36.0", "lean_githash": "611c117b…" },
  "verdict": "accepted",
  "declarations": 83,
  "from_cache": 0,
  "axioms": [ { "name": "propext", "class": "standard" } ],
  "unsafe_or_partial": [],
  "targets": [
    {
      "name": "sum_formula_explicit",
      "kind": "thm",
      "universe_params": [],
      "statement": "∀ (n : Nat), 2 * sumTo n = n * (n + 1)",
      "statement_hash": "becde10f…",
      "axioms": [ { "name": "propext", "class": "standard" } ],
      "unsafe_or_partial": [],
      "closure": 83
    }
  ]
}
```

## What it records

| Field | Meaning |
|---|---|
| `checker` | BLAKE3 hash of the `certus` executable that ran. Rebuilding Certus changes it. |
| `export.blake3` | BLAKE3 hash of the export file's bytes. This pins exactly what was checked. |
| `verdict` | `accepted`, `rejected` (the export is invalid; `message` says why) or `declined` (out of resources before a verdict). |
| `declarations` | How many declarations were checked: the targets' dependency closure, or the whole export if no targets were named. |
| `from_cache` | How many of those were admitted from the [verdict cache](CACHE.md) instead of being type-checked in this run. `--no-cache` makes it 0. |
| `axioms` | Every axiom among the declarations checked. `class` is `standard` (`propext`, `Classical.choice`, `Quot.sound`), `sorry` (`sorryAx`: an unfinished proof) or `non-standard` (review it). |
| `unsafe_or_partial` | Unsafe or partial declarations among those checked. |
| `targets` | Each declaration named on the command line, in that order. For each: its kind, universe parameters, statement printed with notation, `statement_hash` (the alpha-normal hash of its type from [spec v1](spec/certificate-v1.md): binder names do not matter, everything else does), the axioms and unsafe or partial declarations it depends on, and the size of its closure. |

A report is written whatever the verdict. With `--report`, the [whole-export cache shortcut](CACHE.md#unchanged-exports) is skipped, because the report needs the parsed export. The per-declaration cache is still used.

## Reproducible, byte for byte

A report holds no timings, paths, thread counts or other incidental data, and every list is in a fixed order. **The same build, checking the same export for the same targets with the same cache contents, writes the same report, byte for byte**, on any number of threads. `crates/certus-cli/tests/report.rs` checks this. To confirm a colleague's verdict, run the same `certus` build on the same export and compare the two files.

To check that a theorem still says what it said before, after a library update or a refactor, compare `statement_hash`. To make sure no proof uses `sorry` or an unexpected axiom, check `axioms`.
