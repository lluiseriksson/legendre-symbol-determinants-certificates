"""
Generate the 3 publication-grade figures for paper77-legendre-symbol-determinants-certificates
directly from live verify_file outputs and exact rational evaluations.
"""

from __future__ import annotations

import math
import pathlib
import sys
from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.legendre_det_verifier import _build_H_matrix, _det_Q, verify_file

CERTS_DIR = ROOT / "certificates"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.labelsize": 9.5,
    "legend.fontsize": 8.0,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "figure.dpi": 240,
})


def fig1_linear_H_collapse() -> None:
    """Figure 1: Exact affine H(x) collapse from Eq. (2.4) in Q[zeta_p] to Eq. (2.6) for p=13 (1 mod 4) & p=19 (3 mod 4)."""
    r09 = verify_file(CERTS_DIR / "C09_eq24_rational_collapse_p13.json")
    r10 = verify_file(CERTS_DIR / "C10_eq24_rational_collapse_p19.json")

    xs_13 = [-2.0, 0.0, 0.5, 1.0, 3.0]
    ys_13 = [n / d for (n, d) in r09["H_values"]]
    xs_19 = [-1.0, 0.0, 1.0, 5.0 / 3.0]
    ys_19 = [n / d for (n, d) in r10["H_values"]]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.55))

    x_line1 = [-2.3, 3.3]
    # p=13: (2/13)=-1, 2^5=32, a=3/2, b=1/2 => H(x) = -32*((13/2-3)x + (1-3/2)) = -32*(7/2*x - 1/2) = 16 - 112x
    ax1.plot(x_line1, [16.0 - 112.0 * x for x in x_line1], color="#1b5e9c", lw=1.8, label=r"Eq. (2.6): $H_{13}(x) = 16 - 112x$")
    ax1.scatter(xs_13, ys_13, color="#e6550d", s=55, zorder=5, label=r"Live $\mathbb{Q}[\zeta_{13}]$ Eq. (2.4) (C09)")
    ax1.axhline(0, color="#666", lw=0.7, ls="--")
    ax1.set_title(r"(a) Exact Rational Collapse for $p=13 \equiv 1\ (\mathrm{mod}\ 4)$")
    ax1.set_xlabel("Parameter $x$")
    ax1.set_ylabel(r"Exact determinant $H_{13}(x)$")
    ax1.legend(loc="upper right", frameon=True, framealpha=0.92)
    ax1.grid(alpha=0.25)

    x_line2 = [-1.3, 2.0]
    # p=19: 3 mod 4 => H(x) = -2^8*(1 + 2x) = -256 - 512x
    ax2.plot(x_line2, [-256.0 - 512.0 * x for x in x_line2], color="#238b45", lw=1.8, label=r"Eq. (2.6): $H_{19}(x) = -256(1+2x)$")
    ax2.scatter(xs_19, ys_19, color="#d95f02", s=55, zorder=5, label=r"Live $\mathbb{Q}[\zeta_{19}]$ Eq. (2.4) (C10)")
    ax2.axhline(0, color="#666", lw=0.7, ls="--")
    ax2.set_title(r"(b) Exact Rational Collapse for $p=19 \equiv 3\ (\mathrm{mod}\ 4)$")
    ax2.set_xlabel("Parameter $x$")
    ax2.set_ylabel(r"Exact determinant $H_{19}(x)$")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92)
    ax2.grid(alpha=0.25)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_linear_H_collapse.png")
    plt.close(fig)


def fig2_unit_growth_and_det_scaling() -> None:
    """Figure 2: Normalized determinant magnitude |H_p(0)|/2^{(p-3)/2} across primes p=5..41 & unit growth."""
    r11 = verify_file(CERTS_DIR / "C11_real_quad_units_p5_to_p41.json")
    r12 = verify_file(CERTS_DIR / "C12_real_quad_units_higher_h3_p229.json")

    primes_1mod4 = [5, 13, 17, 29, 37, 41]
    primes_3mod4 = [7, 11, 19, 23, 31]
    norm_1 = [abs(float(_det_Q(_build_H_matrix(p, Fraction(0, 1))))) / (2 ** ((p - 3) // 2)) for p in primes_1mod4]
    norm_3 = [abs(float(_det_Q(_build_H_matrix(p, Fraction(0, 1))))) / (2 ** ((p - 3) // 2)) for p in primes_3mod4]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.55))

    ax1.plot(primes_1mod4, norm_1, marker="o", ms=5.5, color="#1b5e9c", lw=1.8, label=r"$p\equiv 1\ (\mathrm{mod}\ 4)$: $|2b_p - a_p|$")
    ax1.plot(primes_3mod4, norm_3, marker="s", ms=5.0, color="#d95f02", lw=1.8, ls="--", label=r"$p\equiv 3\ (\mathrm{mod}\ 4)$: constant $1$")
    ax1.set_yscale("log")
    ax1.set_ylim(0.35, 45.0)
    ax1.set_title(r"(a) Normalized $|H_p(0)| / 2^{(p-3)/2}$ via Direct $\det_{\mathbb{Q}}$")
    ax1.set_xlabel("Odd prime $p$")
    ax1.set_ylabel(r"$|H_p(0)| / 2^{(p-3)/2}$ (log scale)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92)
    ax1.grid(alpha=0.25)

    # Panel (b): log10(eps_p^{h_p}) across all 10 certified primes in C11 & C12 (highlighting p=73 and p=229 h=3!)
    p_all = [5, 13, 17, 29, 37, 41, 53, 61, 73, 229]
    eps_h = [
        (1 + math.sqrt(5)) / 2,
        (3 + math.sqrt(13)) / 2,
        4 + math.sqrt(17),
        (5 + math.sqrt(29)) / 2,
        6 + math.sqrt(37),
        32 + 5 * math.sqrt(41),
        (7 + math.sqrt(53)) / 2,
        (39 + 5 * math.sqrt(61)) / 2,
        1068 + 125 * math.sqrt(73),
        ((15 + math.sqrt(229)) / 2) ** 3,
    ]
    logs = [math.log10(v) for v in eps_h]
    cols = ["#4292c6"] * 6 + ["#31a354"] * 3 + ["#e6550d"]
    bars = ax2.bar(range(len(p_all)), logs, color=cols, width=0.62)
    for bar, v in zip(bars, logs):
        ax2.text(bar.get_x() + bar.get_width() / 2.0, v + 0.08, f"{v:.2f}", ha="center", va="bottom", fontsize=7.0)
    ax2.set_xticks(range(len(p_all)))
    ax2.set_xticklabels([f"{p}" if p != 229 else "229\n($h=3$)" for p in p_all], fontsize=7.8)
    ax2.set_ylim(0.0, 4.15)
    ax2.set_ylabel(r"$\log_{10}(\varepsilon_p^{h_p})$")
    ax2.set_title(r"(b) Real Quadratic Regulator Growth (C11 & C12)")
    ax2.grid(axis="y", alpha=0.25)

    assert r11["direct_det_cross_checked"] == 6 and r12["primes_verified"] == 4
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_unit_growth_and_det_scaling.png")
    plt.close(fig)


def fig3_cyclotomic_workload_and_families() -> None:
    """Figure 3: Cyclotomic field degree phi(p)=p-1 & matrix dim n=(p-1)/2 across live Modes 1-4."""
    r01 = verify_file(CERTS_DIR / "C01_sun_conj32_p17_mod8_1.json")
    r02 = verify_file(CERTS_DIR / "C02_sun_conj32_p29_mod8_5.json")
    r05 = verify_file(CERTS_DIR / "C05_cyclotomic_vandermonde_p13.json")
    r06 = verify_file(CERTS_DIR / "C06_cyclotomic_vandermonde_p23.json")
    r07 = verify_file(CERTS_DIR / "C07_lagrange_forms_p11.json")
    r08 = verify_file(CERTS_DIR / "C08_lagrange_forms_p17.json")
    r13 = verify_file(CERTS_DIR / "C13_chapman_F_M1_p13.json")
    r14 = verify_file(CERTS_DIR / "C14_chapman_F_M1_p19.json")
    r15 = verify_file(CERTS_DIR / "C15_sun_part2_minus_p13.json")
    r16 = verify_file(CERTS_DIR / "C16_sun_part2_minus_p23.json")

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.55))

    # Panel (a): Matrix dimension n=(p-1)/2 and cyclotomic degree phi(p)=p-1 for live cyclotomic certs
    c_lbls = ["C07\n(p=11)", "C05/09/13\n(p=13)", "C08\n(p=17)", "C10/C14\n(p=19)", "C06\n(p=23)"]
    ps = [11, 13, 17, 19, 23]
    ns = [(p - 1) // 2 for p in ps]
    phis = [p - 1 for p in ps]
    x = list(range(len(ps)))
    w = 0.35
    b1 = ax1.bar([i - w / 2 for i in x], ns, width=w, color="#4292c6", label=r"Matrix dim $n=(p-1)/2$")
    b2 = ax1.bar([i + w / 2 for i in x], phis, width=w, color="#fd8d3c", label=r"Cyclotomic deg $\varphi(p)=p-1$")
    for bars in (b1, b2):
        for bar in bars:
            h = int(bar.get_height())
            ax1.text(bar.get_x() + bar.get_width() / 2.0, h + 0.5, str(h), ha="center", va="bottom", fontsize=7.5)
    ax1.set_xticks(x)
    ax1.set_xticklabels(c_lbls)
    ax1.set_ylim(0, 27)
    ax1.set_ylabel("Exact dimension / field degree")
    ax1.set_title("(a) Exact $\\mathbb{Q}[\\zeta_p]$ Certificates (Modes 2\u20134a)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92)
    ax1.grid(axis="y", alpha=0.25)

    # Panel (b): log10(|det|) comparison across Sun Part (i), Chapman F(x), and Sun Part (ii)
    f_lbls = ["C01\nThm 1.1(i)\n$p=17$", "C02\nThm 1.1(i)\n$p=29$", "C13\nChapman\n$p=13$", "C14\nChapman\n$p=19$", "C15\nThm 1.1(ii)\n$p=13$", "C16\nThm 1.1(ii)\n$p=23$"]
    vals_raw = [
        abs(r01["det_A"][0] / r01["det_A"][1]),
        abs(r02["det_A"][0] / r02["det_A"][1]),
        abs(r13["det_F"][0] / r13["det_F"][1]),
        abs(r14["det_F"][0] / r14["det_F"][1]),
        abs(r15["det_A_minus"][0] / r15["det_A_minus"][1]),
        abs(r16["det_A_minus"][0] / r16["det_A_minus"][1]),
    ]
    log_v = [math.log10(max(v, 1e-6)) for v in vals_raw]
    colors = ["#1b5e9c", "#08519c", "#238b45", "#006d2c", "#d95f02", "#a63603"]
    bars2 = ax2.bar(range(len(f_lbls)), log_v, color=colors, width=0.58)
    ax2.axhline(0.0, color="#555", lw=0.8)
    for bar, v in zip(bars2, log_v):
        y_txt = v + 0.14 if v >= 0 else v - 0.35
        ax2.text(bar.get_x() + bar.get_width() / 2.0, y_txt, f"{v:.2f}", ha="center", va="bottom", fontsize=7.3)
    ax2.set_xticks(range(len(f_lbls)))
    ax2.set_xticklabels(f_lbls, fontsize=7.5)
    ax2.set_ylim(-0.7, 5.4)
    ax2.set_ylabel(r"$\log_{10}(|\det|)$")
    ax2.set_title("(b) Certified Exact Determinants Across All Families")
    ax2.grid(axis="y", alpha=0.25)

    assert r05["eq15_eq23_eq25_verified"] and r06["eq15_eq23_eq25_verified"]
    assert r07["forms_and_quotients_verified"] and r08["forms_and_quotients_verified"]
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_cyclotomic_workload_and_families.png")
    plt.close(fig)


def main() -> int:
    fig1_linear_H_collapse()
    fig2_unit_growth_and_det_scaling()
    fig3_cyclotomic_workload_and_families()
    print(f"Generated 3 figures in {FIG_DIR}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
