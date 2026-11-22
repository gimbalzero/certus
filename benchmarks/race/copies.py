"""Shared by <system>/gen.py: N independent copies of the sum theorem.

Each Sum.* file is a template: a prelude, then the definition and theorem
between COPY and END COPY markers, then an epilogue. A copy renames the
definition to sumTo<i> and the theorem to t<i>, so every copy has its own
recursive definition, as in proof-bench/scripts/gen_lean.py.
"""

import re
import sys


def generate(src, start, end, names, header=None):
    """Print the template with its block repeated N times (N = argv[1]).

    names:  identifiers to rename, {old: "new{i}"}.
    header: (pattern, replacement) for the module/theory name, which gets
            argv[2] (default Gen<N>).
    """
    n = int(sys.argv[1])
    module = sys.argv[2] if len(sys.argv) > 2 else f"Gen{n}"
    with open(src, encoding="utf-8") as f:
        text = f.read()
    head, rest = text.split(start, 1)
    block, tail = rest.split(end, 1)
    if header:
        head = re.sub(header[0], header[1].format(module=module), head, count=1)
    out = [head]
    for i in range(n):
        copy = block
        for old, new in names.items():
            copy = re.sub(rf"(?<![\w-]){re.escape(old)}(?![\w-])", new.format(i=i), copy)
        out.append(copy)
    out.append(tail)
    sys.stdout.write("".join(out))
