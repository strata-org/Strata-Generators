import json, collections, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

src, outdir = sys.argv[1], sys.argv[2]
plt.rcParams.update({"font.family": "serif", "font.size": 8, "pdf.fonttype": 42,
                     "axes.edgecolor": "#52514e", "axes.labelcolor": "#0b0b0b",
                     "xtick.color": "#52514e", "ytick.color": "#0b0b0b"})
SERIES, GRID, INK2 = "#2a78d6", "#e4e3df", "#52514e"

by = collections.defaultdict(list)
for line in open(src):
    r = json.loads(line)
    if r["property"].startswith("dist: "):
        by[r["property"]].append(r["features"])

def shares(fs):
    tot = collections.Counter()
    for f in fs:
        for k, v in f.items():
            if k.startswith("n_"): tot[k[2:]] += v
    s = sum(tot.values())
    return {k: 100 * v / s for k, v in tot.items()}

def figure(family, kinds, labels, name, title):
    profiles = [p for p in by if p.startswith(f"dist: {family} [")]
    data = {p: shares(by[p]) for p in profiles}
    kinds = [k for k in kinds if any(data[p].get(k, 0) >= 0.5 for p in profiles)]
    n = len(profiles)
    fig, axes = plt.subplots(1, n, figsize=(1.45 * max(n, 4) + 0.6, 0.22 * len(kinds) + 0.7),
                             sharey=True, constrained_layout=True)
    for ax, p in zip(axes, profiles):
        vals = [data[p].get(k, 0) for k in kinds]
        y = range(len(kinds))
        ax.barh(y, vals, height=0.6, color=SERIES)
        for yi, v in zip(y, vals):
            if v >= 0.5:
                ax.text(v + 1.5, yi, f"{v:.0f}", va="center", fontsize=6.5, color=INK2)
        ax.set_title(p.split("[")[1].rstrip("]").replace(", closed", ""), fontsize=8)
        ax.set_xlim(0, 65)
        ax.set_xticks([0, 25, 50])
        ax.xaxis.grid(True, color=GRID, lw=0.6); ax.set_axisbelow(True)
        for s in ("top", "right"): ax.spines[s].set_visible(False)
        ax.tick_params(length=0)
    axes[0].set_yticks(range(len(kinds)), [labels.get(k, k) for k in kinds])
    axes[0].invert_yaxis()
    fig.supxlabel(title, fontsize=8, color=INK2)
    for ext in ("pdf", "png"):
        fig.savefig(f"{outdir}/{name}.{ext}", dpi=300)
    # table view
    with open(f"{outdir}/{name}.csv", "w") as f:
        f.write("kind," + ",".join(profiles) + "\n")
        for k in kinds:
            f.write(k + "," + ",".join(f"{data[p].get(k,0):.1f}" for p in profiles) + "\n")

figure("stmt", ["cmd", "call", "block", "ite_det", "ite_nondet", "loop", "exit", "funcDecl", "typeDecl"],
       {"ite_det": "ite", "ite_nondet": "ite (nondet)"}, "strata-stmt-tunings",
       "% of generated statement nodes (1000 samples per tuning)")
EXPR_KINDS = ["app", "op", "abs", "ite", "eq", "quant", "bvar", "fvar", "boolConst", "intConst",
              "strConst", "realConst", "bitvecConst"]
EXPR_LABELS = {"boolConst": "bool lit", "intConst": "int lit", "strConst": "string lit",
               "realConst": "real lit", "bitvecConst": "bitvec lit"}
for ty, slug in [("bool", "bool"), ("int", "int"), ("int → int", "int-arrow-int")]:
    figure(f"expr@{ty}", EXPR_KINDS, EXPR_LABELS, f"strata-expr-{slug}-tunings",
           f"% of generated expression nodes at target type {ty} (1000 samples per tuning)")
figure("cmd", ["init_det", "init_nondet", "set_det", "set_nondet", "assert", "assume", "cover"],
       {"init_det": "init", "init_nondet": "init (nondet)", "set_det": "set",
        "set_nondet": "set (nondet)"}, "strata-cmd-tunings",
       "% of generated commands (1000 chains of 4 per tuning)")
figure("expr", ["app", "op", "abs", "ite", "eq", "quant", "bvar", "fvar", "boolConst", "intConst",
                "strConst", "realConst", "bitvecConst"],
       {"boolConst": "bool lit", "intConst": "int lit", "strConst": "string lit",
        "realConst": "real lit", "bitvecConst": "bitvec lit"}, "strata-expr-tunings",
       "% of generated expression nodes (1000 samples per tuning)")

import math
def size_figure(family, name, what, binw):
    profiles = [p for p in by if p.startswith(f"dist: {family} [")]
    sizes = {p: [f["size"] for f in by[p]] for p in profiles}
    allv = sorted(v for p in profiles for v in sizes[p])
    cap = allv[int(0.99 * (len(allv) - 1))]
    cap = math.ceil(cap / binw) * binw
    edges = list(range(0, cap + binw + 1, binw))
    n = len(profiles)
    fig, axes = plt.subplots(1, n, figsize=(1.45 * max(n, 4) + 0.6, 1.9),
                             sharey=True, constrained_layout=True)
    for ax, p in zip(axes, profiles):
        vals = [min(v, cap) for v in sizes[p]]   # the last bin holds the 1% tail
        w = [100 / len(vals)] * len(vals)
        ax.hist(vals, bins=edges, weights=w, color=SERIES, edgecolor="white", linewidth=0.6)
        med = sorted(sizes[p])[len(sizes[p]) // 2]
        ax.axvline(med, color="#0b0b0b", lw=0.8, ls=(0, (2, 2)))
        lbl = p.split("[")[1].rstrip("]").replace(", closed", "")
        ax.set_title(f"{lbl}\nmedian {med}", fontsize=7.5)
        ax.set_xlim(0, cap + binw)
        ax.yaxis.grid(True, color=GRID, lw=0.6); ax.set_axisbelow(True)
        for s in ("top", "right"): ax.spines[s].set_visible(False)
        ax.tick_params(length=0)
    axes[0].set_ylabel("% of samples", fontsize=8, color=INK2)
    fig.supxlabel(f"{what}; 1000 samples per tuning, last bin = top 1%",
                  fontsize=8, color=INK2)
    for ext in ("pdf", "png"):
        fig.savefig(f"{outdir}/{name}.{ext}", dpi=300)
    with open(f"{outdir}/{name}.csv", "w") as f:
        f.write("profile,size\n")
        for p in profiles:
            for v in sizes[p]: f.write(f"\"{p}\",{v}\n")

size_figure("expr", "strata-expr-size-tunings", "Expression size (LExpr nodes)", 3)
size_figure("cmd", "strata-cmd-size-tunings", "Chain size (commands + expression nodes)", 5)
size_figure("stmt", "strata-stmt-size-tunings", "Statement-list size (statements + expression nodes)", 5)
