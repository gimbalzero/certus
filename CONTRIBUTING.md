# Contributing

Thanks for your interest. Certus is in Phase 0 (see [docs/PLAN.md](docs/PLAN.md)), and the most useful contributions right now are:

- **Measurements.** Run `certus stats` / `certus deps` on exports of real projects (Mathlib folders, large formalisations) and open an issue with the numbers.
- **Spec review.** Read [docs/spec/certificate-v0.md](docs/spec/certificate-v0.md) and point out ambiguities. Encoding ambiguities are treated as security issues.
- **Hostile inputs.** Find exports the reader should reject but accepts.
- **Scoreboard corrections.** If an assessment in [docs/SCOREBOARD.md](docs/SCOREBOARD.md) is wrong for your system, tell us, with a source.

## Development

```bash
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt
```

CI runs all three on every pull request.

## Ground rules
- **Fail closed.** Code that reads proofs must reject anything it does not fully understand.
- **Measure, don't guess.** Performance claims need a reproducible benchmark.
- **Keep the trusted part small.** The checker will have a strict line budget (Phase 2: under 5,000 lines).
- Contributions are licensed under Apache-2.0, the same as the project.
