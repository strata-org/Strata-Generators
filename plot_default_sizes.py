import json, math, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager
import subprocess

# acmart's body font is Linux Libertine; use TeX Live's copy so the figure matches the text.
for f in ("LinLibertine_R.otf", "LinLibertine_RB.otf"):
    font_manager.fontManager.addfont(
        subprocess.run(["kpsewhich", f], capture_output=True, text=True, check=True).stdout.strip())

src, out = sys.argv[1], sys.argv[2]
plt.rcParams.update({"font.family": "Linux Libertine O", "font.size": 8, "pdf.fonttype": 42,
                     "axes.edgecolor": "#52514e", "xtick.color": "#52514e", "ytick.color": "#0b0b0b"})
SERIES, GRID, INK2 = "#2a78d6", "#e4e3df", "#52514e"
PANELS = [("dist: expr [(default), closed]", "Expressions", 3),
          ("dist: cmd [(default)]", "Commands", 5),
          ("dist: stmt [(default)]", "Statements", 5)]

sizes = {p: [] for p, *_ in PANELS}
for line in open(src):
    r = json.loads(line)
    if r["property"] in sizes:
        sizes[r["property"]].append(r["features"]["size"])

fig, axes = plt.subplots(1, 3, figsize=(6.3, 2.0), sharey=True, constrained_layout=True)
for ax, (p, title, binw) in zip(axes, PANELS):
    vs = sorted(sizes[p])
    cap = math.ceil(vs[int(0.99 * (len(vs) - 1))] / binw) * binw
    vals = [min(v, cap) for v in vs]  # the last bin holds the top 1%
    ax.hist(vals, bins=range(0, cap + binw + 1, binw), weights=[100 / len(vals)] * len(vals),
            color=SERIES, edgecolor="white", linewidth=0.6)
    med = vs[len(vs) // 2]
    ax.axvline(med, color="#0b0b0b", lw=0.8, ls=(0, (2, 2)))
    ax.set_title(title, fontsize=9)
    ax.set_xlabel("size", fontsize=8.5, color=INK2)
    ax.set_xlim(0, cap + binw)
    ax.yaxis.grid(True, color=GRID, lw=0.6); ax.set_axisbelow(True)
    for s in ("top", "right"): ax.spines[s].set_visible(False)
    ax.tick_params(length=0)
axes[0].set_ylabel("% of samples", color=INK2)
fig.savefig(out + ".pdf"); fig.savefig(out + ".png", dpi=300)
