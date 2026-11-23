# Differential mutation fuzzing

`fuzz.py` mutates a valid export at random and asks Certus and [nanoda](https://github.com/ammkrn/nanoda_lib) for a verdict on each mutant. It reports any mutant where they disagree, and any Certus crash. A mutant Certus accepts and nanoda rejects would be a soundness bug. One Certus rejects and nanoda accepts would be a false rejection.

```bash
cargo build --release
cargo install --locked --git https://github.com/ammkrn/nanoda_lib --rev 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929 --root /tmp/nanoda nanoda_lib
python3 -I tests/fuzz/fuzz.py target/release/certus /tmp/nanoda/bin/nanoda_bin \
    crates/certus-kernel/tests/fixtures/sum_explicit.cert.ndjson 1000 1 /tmp/mutants
```

It uses only the Python standard library. Mutations replace a subterm, a declaration's type or value, a universe level, a bound-variable index or a literal with another one defined earlier in the file. Both checkers get the same de-duplicated file (`dedup.py`), because nanoda refuses duplicate or sparse expression ids.

## Results so far

22 Nov 2026, on the fixtures `sum_explicit`, `nested`, `index_alias`, `string_literals` and `church-numerals`: about 12,000 mutants.

- **No disagreement** on any verdict.
- **One hang, fixed.** A definition whose value mentions itself (`Pred := … Pred …`) made the inductive checker unfold it forever. Phase 1 admits definitions before their values are checked. Checking telescopes is now bounded, and the file is rejected at `Pred` (`tests/index_alias.rs`).
