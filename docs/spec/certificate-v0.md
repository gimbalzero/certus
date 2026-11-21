# Certus certificate format, v0 (draft)

Status: **draft, Phase 0.** Hashing (§3) is implemented in `certus-core` and pinned by a test. Chunking (§4) and hints (§5) are design only. Comments are welcome in GitHub issues.

## 1. Goals

A certificate is a published, finished proof that anyone can check without re-running Lean's elaborator or tactics.

1. **Search once, check forever.** The expensive search runs once, at the author's end. Everyone else only checks.
2. **Content-addressed.** Every name, level, expression and declaration has a hash of its content, so caches can be shared without trusting whoever filled them.
3. **Check only what you use.** A verifier can fetch and check just the dependency closure of the theorem it cares about.
4. **Splittable.** The work can be divided among many machines or volunteers.
5. **Fail closed.** Anything the checker does not understand is an error, never something it skips.

## 2. Input: lean4export NDJSON 3.x

v0 reads the output of [`lean4export`](https://github.com/leanprover/lean4export) format 3.x unchanged. Each line is one record:

| Record | Id field | Payload keys |
|---|---|---|
| meta | none | `meta` (must be line 1) |
| name | `in` | `str` {pre, str} or `num` {pre, i} |
| level | `il` | `succ`, `max`, `imax`, `param` |
| expression | `ie` | `bvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`, `proj`, `natVal`, `strVal` |
| declaration | none | `axiom`, `def`, `thm`, `opaque`, `quot`, `inductive` |

Name id 0 is the anonymous name and level id 0 is zero; neither is written. Expression ids start at 0. Ids are dense and increasing, and a record may refer only to ids defined before it.

A conforming reader **must reject**:
- unknown record kinds or fields;
- forward references and out-of-sequence ids;
- a constant defined twice;
- a natural-number literal that is not canonical decimal;
- a missing meta record, or a format version other than 3.x.

Readers **must canonicalise names by content**, so that dependency analysis cannot miss an edge if a name appears twice.

## 3. Content hashes

```
key  = BLAKE3.derive_key("certus certificate v0 2026-11-20 node hash", "")
hash = BLAKE3.keyed_hash(key, tag || fields)
```

Fields are encoded as follows:
- a child node is its 32-byte hash;
- an integer is a u64, little-endian;
- a boolean is one byte (0 or 1);
- a string or byte array is a u64 length followed by the bytes;
- a list is a u64 count followed by the items.

| Tag | Node | Fields, in order |
|---|---|---|
| 0x00 | anonymous name | none |
| 0x01 | string name | prefix, string |
| 0x02 | numeric name | prefix, u64 |
| 0x10 | level zero | none |
| 0x11 | succ | level |
| 0x12 | max | level, level |
| 0x13 | imax | level, level |
| 0x14 | param | name |
| 0x20 | bvar | u64 index |
| 0x21 | sort | level |
| 0x22 | const | name, list of levels |
| 0x23 | app | function, argument |
| 0x24 | lambda | binder name, binder info (u64: 0 default, 1 implicit, 2 strict implicit, 3 instance), type, body |
| 0x25 | pi | same as lambda |
| 0x26 | let | name, nondep (bool), type, value, body |
| 0x27 | nat literal | decimal string |
| 0x28 | string literal | string |
| 0x29 | proj | structure name, u64 index, expression |
| 0x30 | axiom | name, level params, type, isUnsafe |
| 0x31 | def | name, level params, type, value, hints (canonical JSON, sorted keys, no spaces), safety, all |
| 0x32 | thm | name, level params, type, value, all |
| 0x33 | opaque | name, level params, type, value, isUnsafe, all |
| 0x34 | quot | name, level params, type, kind |
| 0x35 | inductive block | types, then ctors, then recs: each a counted list with all fields in export order |
| 0x40 | environment root | counted list of declaration hashes, in file order |

**v0 hashes faithfully.** Binder names and binder info are included, so alpha-equivalent terms hash differently. This keeps the hash a fingerprint of exactly what was exported. Note that lean4export itself shares terms up to alpha-equivalence and binder info, so the binder names and info in an export can come from another occurrence of the same term. An alpha-normal hash, stable across exports, is defined in [v1 (draft)](certificate-v1.md).

Reference value: `crates/certus-core/tests/fixtures/tiny.ndjson` has root `dedd4861dc32db3cbfb519ce2d1a3aa417993fcf5981a96b92c21b00f0a44587`.

## 4. Chunks and manifest (design, v1)

- A certificate is a set of **chunks**. Each chunk holds a slice of declarations plus every expression node they need that no earlier chunk provides. Each chunk is named by its hash.
- The **manifest** lists, in dependency order, every chunk with its hash, size, and the declaration hashes it defines and imports.
- A verifier checks a theorem by fetching only the chunks in its dependency closure. A volunteer can check any chunk on its own, given the *statements* (types) of the declarations it imports.
- **Open question:** what chunk size balances download count, sharing and parallelism?

## 5. Hints (design, v1+)

The kernel spends time deciding *which* definitions to unfold when checking that two terms are equal. A certificate may carry **unfolding hints**, recorded while the author's machine checks the proof, so the verifier follows the hints instead of searching. Hints are untrusted. A bad hint can make checking fail, never make it accept something false. Measuring their size and speed effect is experiment E4.

## 6. Versioning

The context string, the tags and the field order are all part of the format. Any change bumps the version, and the pinned test in `certus-core` must change with it.
