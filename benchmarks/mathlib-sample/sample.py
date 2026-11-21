#!/usr/bin/env python3
"""Pick the random sample of Mathlib modules, and the share of it one shard runs.

    sample.py <mathlib-dir> --seed 12 --size 50 [--shard 3 --shards 20]

Modules are the imports of Mathlib.lean (CI keeps that file complete), sorted, then
sampled with Python's `random.Random(seed).sample`. The same seed, size and Mathlib
commit always give the same sample. With --shard, prints only modules i where
i % shards == shard (i is the position in the sample). Prints one module per line.
"""

import argparse
import os
import random
import re
import sys


def all_modules(mathlib):
    with open(os.path.join(mathlib, "Mathlib.lean")) as f:
        mods = re.findall(r"^\s*(?:public\s+)?import\s+(Mathlib\.\S+)", f.read(), re.M)
    return sorted(set(mods))


def sample(mathlib, seed, size):
    mods = all_modules(mathlib)
    return random.Random(seed).sample(mods, min(size, len(mods)))


def main():
    p = argparse.ArgumentParser()
    p.add_argument("mathlib")
    p.add_argument("--seed", type=int, required=True)
    p.add_argument("--size", type=int, required=True)
    p.add_argument("--shard", type=int)
    p.add_argument("--shards", type=int, default=1)
    a = p.parse_args()
    picked = sample(a.mathlib, a.seed, a.size)
    print(f"{len(picked)} of {len(all_modules(a.mathlib))} modules sampled (seed {a.seed})", file=sys.stderr)
    for i, m in enumerate(picked):
        if a.shard is None or i % a.shards == a.shard:
            print(m)


if __name__ == "__main__":
    main()
