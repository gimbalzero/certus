# Certus certificate format, v1 (draft): alpha-normal hashing

Status: **draft.** Implemented in `certus-core` (`hash::hash_env_alpha`, `hash::Mode::AlphaNormal`) and pinned by tests. Everything not stated here is as in [v0](certificate-v0.md), which stays valid and unchanged: v1 adds a second hash mode, it does not replace the faithful one.

## 1. Why

Two terms that differ only in the names or binder info (`(x)`, `{x}`, `⦃x⦄`, `[x]`) of their bound variables are alpha-equivalent. The kernel treats them as the same term: binder names never affect type checking, and definitional equality ignores binder info. The v0 hash includes both, so the same term can get different v0 hashes. A content-addressed cache (issue #9) keyed on alpha-normal hashes can share a checked result between such terms.

## 2. Hash

```
key  = BLAKE3.derive_key("certus certificate v1-alpha 2026-11-21 alpha-normal node hash", "")
hash = BLAKE3.keyed_hash(key, tag || fields)
```

Tags, field encodings and field order are those of v0 §3, with three changes:

| Tag | Node | Fields, in order |
|---|---|---|
| 0x24 | lambda | type, body |
| 0x25 | pi | type, body |
| 0x26 | let | type, value, body |

That is, lambda and pi omit the binder name and binder info, and let omits its name and its `nondep` flag (the let's binder annotation, which the kernel also ignores).

Everything else is hashed as in v0, including declaration names, level-parameter names, constant names, and the structure name of `proj`. These are not bound variables: renaming them changes meaning. Because every node is hashed with the v1 key, no v1 hash equals a v0 hash, even for nodes with no binders.

Reference values (pinned in `crates/certus-core/tests/export.rs`):
- `tests/fixtures/tiny.ndjson`: root `3b4e75815a2e0ab06cd7b9733d8b6a2896501c6a041c1822b34733dabb5e8550`
- `tests/fixtures/alpha.ndjson`: root `68baf0795614185d7d75a6e5f71cf2fd8174a56810a48558e9bcaca296f0b77a`

## 3. Measured effect (Lean 4.36 core library)

On the 348 MB lean4export 3.1.0 export of `benchmarks/proof-bench/lean/Sum.lean` (Lean's core library plus one theorem; 6,138,037 expression nodes, of which 845,637, or 13.8%, are binders: 531,771 lambdas, 302,486 pis and 11,380 lets):

| Mode | Unique expressions | Saving |
|---|---|---|
| v0 faithful | 6,138,037 | none |
| v1 alpha-normal | 6,138,037 | **0 nodes (0.00%)** |

**Alpha-normal hashing gives no deduplication on lean4export output, so it does not shrink certificates.** The reason is that lean4export already shares terms up to alpha-equivalence *and binder info*. We observed this directly (below); it matches Lean's `BEq Expr` instance (`Expr.eqv`), which ignores binder names and binder info, presumably because the exporter's expression cache uses it. When two alpha-equivalent terms occur, only the first is written, and every later occurrence points at it, so it carries the first one's binder names and binder info. For example, exporting

```lean
theorem alphaT1 : ∀ (a : Nat), a = a := fun a => rfl
theorem alphaT2 : ∀ {b : Nat}, b = b := fun {b} => rfl
```

gives both theorems the same type and value records. In that order both say `(a : Nat)` with default binder info. In the opposite order both say `{b : Nat}`. (These exports are the test fixtures `alpha_order_12.ndjson` and `alpha_order_21.ndjson`.)

Consequences:
1. **Within one export, v0 and v1 identify exactly the same nodes.** Every lambda, pi and let in an export has a distinct (type, body) pair (or (type, value, body) triple), so dropping the binder name and info merges nothing.
2. **v0 is faithful to the export, not to the source.** The binder names and info that v0 hashes may come from a different declaration, and depend on the order in which the exporter visited declarations.
3. **Across exports, v1 is stable where v0 is not.** The same declaration can get different v0 hashes in two exports, depending on which alpha-variant each exporter saw first. Its v1 hash is the same in both (test `alpha_hash_does_not_depend_on_export_order`). This is the real reason to use v1: as the key of the shared, content-addressed cache (issue #9), so that results computed from one export are found again from another.

Further size reduction has to come from a denser encoding, not from more deduplication (scoreboard axis 42).

## 4. Open questions

- Should certificates carry binder names at all? The kernel does not need them, but error messages and pretty-printing do, and lean4export already makes them unreliable (§3).
- Should the v1 *declaration* hash also be insensitive to things that do not affect checking (for example `def` reducibility hints, which are performance advice)? Not in this draft: v1 changes only binders.
