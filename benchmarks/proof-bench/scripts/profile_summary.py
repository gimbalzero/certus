"""Sum Lean profiler output ('<category> took <t>ms|s') by category."""
import sys, re, collections
tot = collections.Counter()
for line in sys.stdin:
    m = re.match(r"\s*(.+?) took ([\d.]+)(ms|s)\s*$", line)
    if not m: continue
    cat = re.sub(r"^typeclass inference of .*", "typeclass inference", m.group(1))
    tot[cat] += float(m.group(2)) / (1000 if m.group(3) == "ms" else 1)
all_ = sum(tot.values())
for k, v in tot.most_common(8):
    print(f"  {k:32s} {v:8.3f}s  {100*v/all_:5.1f}%")
print(f"  {'TOTAL profiled':32s} {all_:8.3f}s")
