# Plan

The goal is to be the best proof-checking system on all 44 axes in [SCOREBOARD.md](SCOREBOARD.md). We win them in waves, fastest wins first, and each phase earns the credibility for the next. **We work strictly in phase order.**

## Workstreams

| Workstream | Axes |
|---|---|
| **W1. Certificates and cache** | 1, 4, 8, 18, 19, 34, 41, 42, 43, 44 |
| **W2. Kernel and trust** | 2, 11, 12, 13, 14, 15, 16 |
| **W3. Build system and runtime** | 3, 5, 6, 7, 9, 10, 35, 40 |
| **W4. Statement audit** | 17 |
| **W5. Logic design** | 20, 21, 22, 23 |
| **W6. Front end and proof writing** | 24, 25, 26, 27, 28, 29, 30 |
| **W7. Library and compatibility** | 31, 32, 33, 39 |
| **W8. Community and governance** | 36, 37, 38 |

## Phases

### Phase 0: Foundation (now)
- [x] Public repo, Apache-2.0 licence, security policy, CI
- [x] Certificate spec v0: content hashing ([spec](spec/certificate-v0.md))
- [x] `certus` tool: strict export reader, content hashes, dependency closure, axiom audit
- [x] First benchmark: Lean vs Metamath on one theorem ([proof-bench](../benchmarks/proof-bench))
- [ ] Scoreboard with measured Lean and Metamath baselines on every measurable axis
- [ ] **E1 and E2 on Mathlib**, on a rented 32–64 core machine
- **Done when** the scoreboard has measured baselines and E1/E2 have settled H1.

### Phase 1: The fastest checker (months 1–4)
- Parallel Rust type checker for the Lean kernel, building on nanoda's design
- Per-declaration cache keyed by content hash: unchanged declarations are never re-checked
- Check only the dependency closure of the target
- All of Mathlib exported as certificates
- **Done when** it beats nanoda's 18 s on Lean's core library, re-checks any cached project in under 1 s, and agrees with Lean on all Lean Kernel Arena tests. Then post on the Lean Zulip.

### Phase 2: The most trusted (months 4–9)
- Kernel under 5,000 lines of Rust; start a formal correctness proof (Aeneas or Verus)
- Zero false acceptances on the Kernel Arena tests
- Full statement audit, and bit-for-bit reproducible verdicts
- Bug bounty
- **Done when** the RH formalisation is independently certified on modest hardware in hours, not days on 256 cores.

### Phase 3: The best build experience (months 9–18)
- Lake plugin: tactic lockfile, per-declaration scheduling, lazy imports
- Checker-only install under 100 MB, plus a WebAssembly build that verifies in the browser
- **Done when** an edit rebuild takes under 1 s, and a fresh check runs within 10× of Metamath per step.

### Phase 4: The best to write in (months 18–36)
AI-first front end work, upstream in Lean or our own:
- solver and AI automation whose results are always turned into certificates;
- readable structured proofs;
- error messages that explain the fix.

**Done when** it beats Sledgehammer on a public benchmark.

### Phase 5: The best ecosystem (years 3–5)
- Stability guarantee: checked certificates never break
- Verified code extraction
- Zero-knowledge proofs of checking, so anyone can verify on a phone
- Optional univalent mode
- Open foundation

## Biggest risks
1. **Explicit certificates get too large.** Measure early (E4); deduplication is the fix.
2. **The Lean FRO builds the same thing.** Then collaborate and contribute upstream. Winning the axes matters more than owning the code.
3. **Univalence conflicts with Mathlib compatibility.** Keep them as separate modes.
4. **Doing too much at once.** Hence the strict phase order.
