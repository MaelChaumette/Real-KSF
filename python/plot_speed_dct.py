from matplotlib.lines import Line2D
import mlflow
import matplotlib.pyplot as plt
import matplotlib as mpl
import seaborn as sns


def set_style():
    """Apply the paper's LaTeX-matched, publication-ready style globally."""
    palette = ["#378ADD", "#D85A30",
               "#787878"]  # blockblue, blockorange, blockgray

    rc = {
        "text.usetex": True,
        "text.latex.preamble": "\n".join([
            r"\usepackage[T1]{fontenc}",
            r"\usepackage{amsmath}",
            r"\usepackage[cmintegrals]{newtxmath}",
            r"\usepackage{bm}",
            r"\renewcommand{\rmdefault}{ptm}",
            r"\renewcommand{\sfdefault}{phv}",
            r"\renewcommand{\ttdefault}{pcr}",
        ]),
        "font.family":       "serif",
        "font.size":         17,
        "axes.titlesize":    15,
        "axes.labelsize":    14,
        "xtick.labelsize":   13,
        "ytick.labelsize":   13,
        "legend.fontsize":   12.5,
        "legend.title_fontsize": 13,
        "axes.linewidth":    0.8,
        "grid.linewidth":    0.5,
        "grid.color":        "#CCCCCC",
        "grid.linestyle":    "--",
        "grid.alpha":        0.7,
        "figure.dpi":        150,
        "savefig.dpi":       300,
        "axes.spines.top":   False,
        "axes.spines.right": False,
    }

    sns.set_theme(style="ticks", palette=palette, rc=rc)


COLORS = {
    "complex128": "#378ADD",  # blockblue
    "float64": "#D85A30",     # blockorange
    "float16": "#787878",     # blockgray
    "bfloat16": "#4DBD33",    # blockgreen
}
MARKERS = {
    "complex128": "o",
    "float64": "s",
    "float16": "D",
    "bfloat16": "^",
}


def _load_times(df, device, dtypes):
    sub = df[(df["device"] == device)]
    n_values = sorted(sub["n"].unique())
    times = {dtype: [] for dtype in dtypes}
    for n in n_values:
        row = sub[sub["n"] == n].iloc[0]
        for dtype in dtypes:
            times[dtype].append(row[f"time_{dtype}"])
    return n_values, times


def plot_speed_dct():
    set_style()

    df = mlflow.search_runs(
        experiment_names=["Computational costs DCT methods"],
        filter_string=""
    )

    df["params.n"] = df["params.n"].astype(int)
    df["params.b"] = df["params.b"].astype(int)
    df = df.rename(columns={
        "params.n": "n",
        "params.b": "b",
        "params.device": "device",
        "metrics.time_complex128": "time_complex128",
        "metrics.time_float64": "time_float64",
        "metrics.time_float16": "time_float16",
        "metrics.time_bfloat16": "time_bfloat16",
    })

    dtypes = [
        "complex128",
        "float64",
        # "float16",
        # "bfloat16",
    ]
    dtypes = {
        "complex128": r"Complex FFT (\texttt{complex128})",
        "float64": r"Real KS Factorization (\texttt{float64})",
    }

    devices = {"cpu": ("-", "CPU"), "cuda": ("--", "GPU")}

    plt.figure(figsize=(10, 4))

    for device, (linestyle, _) in devices.items():
        n_values, times = _load_times(df[df["b"] == 1], device, dtypes)
        for dtype in dtypes:
            plt.plot(n_values, times[dtype],
                     color=COLORS[dtype],
                     marker=MARKERS[dtype],
                     linestyle=linestyle)

    dtype_handles = [
        Line2D([], [], color=COLORS[d], marker=MARKERS[d], linestyle="-",
               label=label)
        for d, label in dtypes.items()
    ]
    device_handles = [
        Line2D([], [], color="black", linestyle=ls, label=label)
        for ls, label in devices.values()
    ]

    plt.xlabel(r"$n$")
    plt.ylabel("Time (seconds)")
    plt.yscale("log")
    plt.xscale("log")
    ax = plt.gca()
    legend_dtype = ax.legend(handles=dtype_handles, title="Method",
                             loc="upper left", bbox_to_anchor=(0, 1))
    ax.add_artist(legend_dtype)
    ax.legend(handles=device_handles, title="Device",
              loc="upper left", bbox_to_anchor=(0.355, 1))
    plt.tight_layout()
    plt.savefig("speed_dct.pdf", dpi=300, bbox_inches="tight")
    plt.close()


def plot_speed_dct_batch():
    set_style()

    df = mlflow.search_runs(
        experiment_names=["Computational costs DCT methods"],
        filter_string=""
    )

    df["params.n"] = df["params.n"].astype(int)
    df["params.b"] = df["params.b"].astype(int)
    df = df.rename(columns={
        "params.n": "n",
        "params.b": "b",
        "params.device": "device",
        "metrics.time_complex128": "time_complex128",
        "metrics.time_float64": "time_float64",
        "metrics.time_float16": "time_float16",
        "metrics.time_bfloat16": "time_bfloat16",
    })

    plt.figure(figsize=(10, 4))
    for i, n in enumerate([1024, 4096, 16384]):
        plt.subplot(1, 3, i + 1)
        b_values = sorted(df["b"].unique())[1:]
        for dtype in ["float64", "bfloat16"]:
            times = []
            for b in b_values:
                row = df[(df["n"] == n) & (df["b"] == b) &
                         (df["device"] == "cuda")].iloc[0]
                times.append(row[f"time_{dtype}"])
            plt.plot(b_values, times,
                     color=COLORS[dtype],
                     marker=MARKERS[dtype],
                     linestyle="-",
                     label=rf"\texttt{{{dtype}}}")

        plt.xlabel(r"$b$")

        if i == 0:
            plt.ylabel("Time (seconds)")

        plt.yscale("log")
        plt.xscale("log")
        plt.title(fr"$n = {n}$")
        plt.tight_layout()
        plt.legend()
    plt.savefig(f"speed_dct_batch_b.pdf", dpi=300, bbox_inches="tight")
    plt.close()

    plt.figure(figsize=(10, 4))
    for i, b in enumerate([1, 1024, 16384]):
        plt.subplot(1, 3, i + 1)
        n_values, times = _load_times(
            df[df["b"] == b], "cuda", ["float64", "bfloat16"])
        for dtype in ["float64", "bfloat16"]:
            plt.plot(n_values, times[dtype],
                     color=COLORS[dtype],
                     marker=MARKERS[dtype],
                     linestyle="-",
                     label=rf"\texttt{{{dtype}}}")

        plt.xlabel(r"$n$")

        if i == 0:
            plt.ylabel("Time (seconds)")

        plt.yscale("log")
        plt.xscale("log")
        plt.title(fr"$b = {b}$")
        plt.tight_layout()
        plt.legend()
    plt.savefig(f"speed_dct_batch_n.pdf", dpi=300, bbox_inches="tight")
    plt.close()


if __name__ == "__main__":
    plot_speed_dct()
    plot_speed_dct_batch()
