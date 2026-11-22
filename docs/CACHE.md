# The verdict cache

`certus check` remembers every declaration it accepts. When it checks an export again, a declaration whose content and dependencies are unchanged is not type-checked a second time. If everything is unchanged, nothing is type-checked at all, and if the export file itself is unchanged byte for byte, it is not even parsed: re-checking all of Lean's core library (348 MB) that way takes 0.4 s.

```bash
certus check export.ndjson                 # cache in $XDG_CACHE_HOME/certus or ~/.cache/certus
certus check export.ndjson --cache DIR     # cache in DIR
certus check export.ndjson --no-cache      # neither read nor write the cache
```

## Keys

A declaration's key is a Merkle hash over everything its verdict can depend on (`crates/certus-core/src/cache.rs`):

```text
key(d) = BLAKE3.derive_key("certus verdict cache v1 2026-11-22 declaration key") of
         checker || alpha_hash(d) || n || key(dep_1) || … || key(dep_n)
```

- **`checker`** is the BLAKE3 hash of the running `certus` executable. A different build of Certus, even one with a single changed line, never reuses verdicts from another build.
- **`alpha_hash(d)`** is the alpha-normal declaration hash of [spec v1](spec/certificate-v1.md). It covers everything in the declaration except binder names and binder info, which the kernel never looks at. So the key depends neither on the export order nor on which alpha-variant lean4export happened to write.
- **The dependencies** are the declarations whose constants `d` mentions, plus the ones the kernel uses implicitly: `Nat` for a natural-number literal, `String`, `String.ofList`/`String.mk`, `Char`, `Char.ofNat`, `List.nil` and `List.cons` for a string literal, and `Eq` for the quotient constants. Their keys are sorted.

Each key covers its dependencies' keys, so it covers the whole dependency closure. **Changing one declaration changes the keys of exactly that declaration and the declarations that depend on it**, directly or not. Everything else keeps its key and is not checked again. A test in `crates/certus-kernel/tests/soundness.rs` checks exactly this.

A declaration that mentions a constant not defined *before* it in the file gets no key. It is always checked, and fails just as it would without a cache. The same holds for everything that depends on it.

## What is stored, and what is trusted

The cache is a single file, `verdicts-v1.log`, with one line per accepted declaration: its key and a check value, `BLAKE3.derive_key("certus verdict cache v1 2026-11-22 entry check")` of `"accepted" || key`, both in hex. Only acceptances are stored, and only after the whole run has succeeded. Rejections and resource limits are never cached.

When it reads the file, Certus recomputes every key from the export in front of it. It never takes a key, a name or a position from the file. A line counts only if it is well formed and its check value matches. A truncated, corrupted or foreign line is ignored, which can only cause a re-check, never an acceptance.

The check value detects accidents, not attacks: anyone who can write to your cache directory can add entries. Treat the cache directory like the `certus` binary itself, or pass `--no-cache` when checking in an untrusted environment (CI on shared runners, someone else's machine). Benchmarks should also use `--no-cache`.

## How a cached declaration is used

A known-good definition, theorem, opaque or axiom is *admitted*. The kernel still runs every check that does not need the type checker: safety flags, universe parameters, and converting its terms. It then adds the declaration to the environment, so that later declarations can use it, but does not type-check it again. This is the same mechanism that multi-core checking uses for declarations checked by another thread (`certus_kernel::check_with`). Inductive types and quotients are re-checked in every run unless the whole export is known good, because their recursors and rules are rebuilt rather than stored.

## Unchanged exports

After a check succeeds, Certus also records one entry for the check as a whole. Its key is

```text
export_key = BLAKE3.derive_key("certus verdict cache v1 2026-11-22 export key") of
             checker || BLAKE3(export bytes) || n || len(name_1) || name_1 || … || len(name_n) || name_n
```

where the names are the declarations asked for on the command line, sorted and deduplicated (none means all of them). The next `certus check` first hashes the file, which takes about 1 s per GB. If that key is in the cache, it prints `OK: export unchanged since this build accepted it` and stops. It doesn't parse, hash declarations or type-check.

This is sound for the same reason as the per-declaration entries. The same bytes, checked by the same build for the same targets, always get the same verdict, and only acceptances are recorded. The hash that goes into the recorded key is computed from exactly the bytes the parser read, as it reads them. So a file that changes during a check cannot pair its old content with the new verdict. Any other change, such as one byte, a different target or a rebuilt `certus`, falls back to the per-declaration cache above. `crates/certus-cli/tests/cache.rs` checks these cases.

Measured on the Apple M2, 22 Nov 2026, on all of Lean's core library (`init.ndjson`, 348 MB, 58,547 declarations):

| Run | Wall time |
|---|---|
| `--no-cache`, 8 threads | 16.4 s (8.7 s of it type-checking) |
| One byte changed, every declaration known good | 6.2 s (parsing 2.8 s, keys 2.6 s) |
| Unchanged export | **0.4 s** |
