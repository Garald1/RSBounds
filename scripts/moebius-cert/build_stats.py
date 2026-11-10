"""Summarize lake build logs: module count, wall time, summed per-module CPU-ish time.

Lake prints `Built <module> (<time>)` per module; the per-module times are wall times of each
`lean` process, so their sum is the core time used (each process is single-threaded here, since
the segment modules set `Elab.async false`).
"""
import re, sys

def parse_time(t):
    t = t.strip()
    total = 0.0
    for val, unit in re.findall(r'([\d.]+)\s*(ms|s|m|h)', t):
        v = float(val)
        total += {'ms': v / 1000, 's': v, 'm': 60 * v, 'h': 3600 * v}[unit]
    return total

def main(paths):
    mods = {}
    for p in paths:
        for line in open(p, errors='replace'):
            m = re.search(r'Built (\S+) \(([^)]*)\)', line)
            if m:
                mods[m.group(1)] = parse_time(m.group(2))
    groups = {}
    for name, t in mods.items():
        key = '.'.join(name.split('.')[:2]) if name.startswith('MoebiusCert.') else name.split('.')[0]
        g = groups.setdefault(key, [0, 0.0])
        g[0] += 1; g[1] += t
    tot_n = sum(g[0] for g in groups.values()); tot_t = sum(g[1] for g in groups.values())
    for k in sorted(groups):
        print(f"{k:28s} {groups[k][0]:5d} modules  {groups[k][1]/3600:7.3f} core-h")
    print(f"{'TOTAL':28s} {tot_n:5d} modules  {tot_t/3600:7.3f} core-h")

if __name__ == '__main__':
    main(sys.argv[1:])
