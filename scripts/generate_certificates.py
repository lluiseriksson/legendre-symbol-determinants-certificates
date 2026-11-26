"""
Generate the 16 canonical LEGENDRE-DET-SYM-CERT-1.0 certificates (C01..C16) for
paper77-legendre-symbol-determinants-certificates and verify every single one.
"""

from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.legendre_det_verifier import SCHEMA_VERSION, verify_file

CERTS_DIR = ROOT / "certificates"


def _r(num: int, den: int = 1) -> list[int]:
    f = Fraction(num, den)
    return [f.numerator, f.denominator]


def _quad_pow(p: int, u0: Fraction, v0: Fraction, h: int) -> tuple[Fraction, Fraction]:
    ap, bp = Fraction(1, 1), Fraction(0, 1)
    for _ in range(h):
        ap, bp = ap * u0 + p * bp * v0, ap * v0 + bp * u0
    return ap, bp


def build_certificates() -> list[tuple[str, dict]]:
    certs: list[tuple[str, dict]] = []

    # ------------------------------------------------------------------
    # Mode 1a: sun_conjecture_direct_det (Thm. 1.1(i) Eq. (1.3) & Eq. (2.1))
    # ------------------------------------------------------------------
    # C01: p=17 (p = 1 mod 8, (2/17)=+1, eps_17 = 4 + sqrt(17), h_17 = 1)
    certs.append((
        "C01_sun_conj32_p17_mod8_1.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C01_sun_conj32_p17_mod8_1",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Thm. 1.1(i) & Eq. (2.1) at p=17",
            "mode": "matrix_reduction_and_det_lemma",
            "payload": {
                "submode": "sun_conjecture_direct_det",
                "prime_p": 17,
                "x": _r(3, 2),
                "y": _r(-1, 3),
                "z": _r(5, 4),
                "w": _r(2, 5),
                "a_p": _r(4, 1),
                "b_p": _r(1, 1),
            },
        },
    ))

    # C02: p=29 (p = 5 mod 8, (2/29)=-1, eps_29 = (5 + sqrt(29))/2, h_29 = 1) & p=31 (3 mod 4)
    # Use p=29 for C02 (non-trivial 14x14 matrix with half-integer unit!)
    certs.append((
        "C02_sun_conj32_p29_mod8_5.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C02_sun_conj32_p29_mod8_5",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Thm. 1.1(i) & Eq. (2.1) at p=29",
            "mode": "matrix_reduction_and_det_lemma",
            "payload": {
                "submode": "sun_conjecture_direct_det",
                "prime_p": 29,
                "x": _r(2, 3),
                "y": _r(1, 2),
                "z": _r(-3, 4),
                "w": _r(5, 2),
                "a_p": _r(5, 2),
                "b_p": _r(1, 2),
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 1b: rank2_matrix_det_lemma (Lemma 2.1 & Cyclotomic Eq. (2.2))
    # ------------------------------------------------------------------
    certs.append((
        "C03_lemma21_and_eq22_p11.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C03_lemma21_and_eq22_p11",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.1 Lemma 2.1 & Eq. (2.2) at p=11",
            "mode": "matrix_reduction_and_det_lemma",
            "payload": {
                "submode": "rank2_matrix_det_lemma",
                "dim_m": 4,
                "matrix_A": [
                    [_r(3), _r(1), _r(0), _r(1)],
                    [_r(1), _r(4), _r(1), _r(0)],
                    [_r(0), _r(1), _r(5), _r(2)],
                    [_r(1), _r(0), _r(2), _r(6)],
                ],
                "vec_u": [_r(1), _r(1), _r(1), _r(1)],
                "vec_v": [_r(1), _r(0), _r(0), _r(0)],
                "scalar_a": _r(5, 2),
                "scalar_b": _r(-11, 1),
                "prime_p": 11,
                "x": _r(3, 4),
            },
        },
    ))

    certs.append((
        "C04_lemma21_and_eq22_p13.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C04_lemma21_and_eq22_p13",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.1 Lemma 2.1 & Eq. (2.2) at p=13",
            "mode": "matrix_reduction_and_det_lemma",
            "payload": {
                "submode": "rank2_matrix_det_lemma",
                "dim_m": 3,
                "matrix_A": [
                    [_r(2), _r(-1), _r(1, 2)],
                    [_r(1), _r(3), _r(-1)],
                    [_r(0), _r(1, 2), _r(4)],
                ],
                "vec_u": [_r(1), _r(-2), _r(3)],
                "vec_v": [_r(2), _r(1), _r(-1)],
                "scalar_a": _r(3, 5),
                "scalar_b": _r(-7, 2),
                "prime_p": 13,
                "x": _r(-1, 2),
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 2a: gauss_sum_and_vandermonde_sq (Eq. (1.5)-(1.6), (2.3), (2.5))
    # ------------------------------------------------------------------
    # C05: p=13 (1 mod 4: a=3/2, b=1/2)
    certs.append((
        "C05_cyclotomic_vandermonde_p13.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C05_cyclotomic_vandermonde_p13",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.2 Eq. (1.5)-(1.6), (2.3), (2.5) at p=13",
            "mode": "cyclotomic_vandermonde_and_forms",
            "payload": {
                "submode": "gauss_sum_and_vandermonde_sq",
                "prime_p": 13,
                "a_p": _r(3, 2),
                "b_p": _r(1, 2),
            },
        },
    ))

    # C06: p=23 (3 mod 4, h_{-23} = 3 => (-1)^{(3+1)/2} = +1!)
    certs.append((
        "C06_cyclotomic_vandermonde_p23.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C06_cyclotomic_vandermonde_p23",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.2 Eq. (1.5)-(1.6), (2.3), (2.5) at p=23 (h_{-23}=3)",
            "mode": "cyclotomic_vandermonde_and_forms",
            "payload": {
                "submode": "gauss_sum_and_vandermonde_sq",
                "prime_p": 23,
                "sign_cp": 1,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 2b: lagrange_partial_fractions_forms (Sec. 2.3-2.5 alpha1, beta1, gamma1=delta1)
    # ------------------------------------------------------------------
    certs.append((
        "C07_lagrange_forms_p11.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C07_lagrange_forms_p11",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.3-2.5 Forms & Euclidean Quotients at p=11",
            "mode": "cyclotomic_vandermonde_and_forms",
            "payload": {
                "submode": "lagrange_partial_fractions_forms",
                "prime_p": 11,
            },
        },
    ))

    certs.append((
        "C08_lagrange_forms_p17.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C08_lagrange_forms_p17",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.3-2.5 Forms & Euclidean Quotients at p=17",
            "mode": "cyclotomic_vandermonde_and_forms",
            "payload": {
                "submode": "lagrange_partial_fractions_forms",
                "prime_p": 17,
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 3a: eq24_to_eq26_rational_collapse (Sec. 2.6 Eq. (2.4) -> Eq. (2.6))
    # ------------------------------------------------------------------
    certs.append((
        "C09_eq24_rational_collapse_p13.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C09_eq24_rational_collapse_p13",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.6 Eq. (2.4)->(2.6) at p=13",
            "mode": "final_evaluation_and_unit_norms",
            "payload": {
                "submode": "eq24_to_eq26_rational_collapse",
                "prime_p": 13,
                "x_values": [_r(-2), _r(0), _r(1, 2), _r(1), _r(3)],
            },
        },
    ))

    certs.append((
        "C10_eq24_rational_collapse_p19.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C10_eq24_rational_collapse_p19",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 2.6 Eq. (2.4)->(2.6) at p=19",
            "mode": "final_evaluation_and_unit_norms",
            "payload": {
                "submode": "eq24_to_eq26_rational_collapse",
                "prime_p": 19,
                "x_values": [_r(-1), _r(0), _r(1), _r(5, 3)],
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 3b: real_quadratic_unit_and_class_number (Pell Units + Direct Det Cross-Check)
    # ------------------------------------------------------------------
    units_a = [
        (5, Fraction(1, 2), Fraction(1, 2), 1),
        (13, Fraction(3, 2), Fraction(1, 2), 1),
        (17, Fraction(4, 1), Fraction(1, 1), 1),
        (29, Fraction(5, 2), Fraction(1, 2), 1),
        (37, Fraction(6, 1), Fraction(1, 1), 1),
        (41, Fraction(32, 1), Fraction(5, 1), 1),
    ]
    certs.append((
        "C11_real_quad_units_p5_to_p41.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C11_real_quad_units_p5_to_p41",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Eq. (1.1) & (2.6) Real Quadratic Units p<=41",
            "mode": "final_evaluation_and_unit_norms",
            "payload": {
                "submode": "real_quadratic_unit_and_class_number",
                "prime_units": [
                    {
                        "prime_p": p,
                        "fund_u": [u.numerator, u.denominator],
                        "fund_v": [v.numerator, v.denominator],
                        "class_number_h": h,
                        "a_p": [_quad_pow(p, u, v, h)[0].numerator, _quad_pow(p, u, v, h)[0].denominator],
                        "b_p": [_quad_pow(p, u, v, h)[1].numerator, _quad_pow(p, u, v, h)[1].denominator],
                    }
                    for (p, u, v, h) in units_a
                ],
            },
        },
    ))

    # C12: Larger primes including NON-TRIVIAL class number h_229 = 3!
    units_b = [
        (53, Fraction(7, 2), Fraction(1, 2), 1),
        (61, Fraction(39, 2), Fraction(5, 2), 1),
        (73, Fraction(1068, 1), Fraction(125, 1), 1),
        (229, Fraction(15, 2), Fraction(1, 2), 3),
    ]
    certs.append((
        "C12_real_quad_units_higher_h3_p229.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C12_real_quad_units_higher_h3_p229",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Eq. (1.1) Higher-Unit & Class-Number h_229=3",
            "mode": "final_evaluation_and_unit_norms",
            "payload": {
                "submode": "real_quadratic_unit_and_class_number",
                "prime_units": [
                    {
                        "prime_p": p,
                        "fund_u": [u.numerator, u.denominator],
                        "fund_v": [v.numerator, v.denominator],
                        "class_number_h": h,
                        "a_p": [_quad_pow(p, u, v, h)[0].numerator, _quad_pow(p, u, v, h)[0].denominator],
                        "b_p": [_quad_pow(p, u, v, h)[1].numerator, _quad_pow(p, u, v, h)[1].denominator],
                    }
                    for (p, u, v, h) in units_b
                ],
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 4a: chapman_determinant_M1 (Sec. 3 Chapman F(x) Alternative Proof)
    # ------------------------------------------------------------------
    certs.append((
        "C13_chapman_F_M1_p13.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C13_chapman_F_M1_p13",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 3 Chapman Determinant F(x) at p=13",
            "mode": "chapman_and_sun_companion_families",
            "payload": {
                "submode": "chapman_determinant_M1",
                "prime_p": 13,
                "x": _r(2, 3),
            },
        },
    ))

    certs.append((
        "C14_chapman_F_M1_p19.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C14_chapman_F_M1_p19",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Sec. 3 Chapman Determinant F(x) at p=19",
            "mode": "chapman_and_sun_companion_families",
            "payload": {
                "submode": "chapman_determinant_M1",
                "prime_p": 19,
                "x": _r(-1, 4),
            },
        },
    ))

    # ------------------------------------------------------------------
    # Mode 4b: sun_conjecture_part_ii_check (Thm. 1.1(ii) Eq. (1.4) i-j Family)
    # ------------------------------------------------------------------
    certs.append((
        "C15_sun_part2_minus_p13.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C15_sun_part2_minus_p13",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Thm. 1.1(ii) Eq. (1.4) at p=13 ((2/13)=-1, cubic unit)",
            "mode": "chapman_and_sun_companion_families",
            "payload": {
                "submode": "sun_conjecture_part_ii_check",
                "prime_p": 13,
                "x": _r(3, 5),
                "y": _r(2, 1),
                "z": _r(-1, 2),
                "w": _r(4, 3),
                "a_p": _r(3, 2),
                "b_p": _r(1, 2),
            },
        },
    ))

    certs.append((
        "C16_sun_part2_minus_p23.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C16_sun_part2_minus_p23",
            "paper_reference": "Le Lan-Liu (arXiv:2611.33667v1), Thm. 1.1(ii) Eq. (1.4) at p=23 (p=3 mod 4 => det=x)",
            "mode": "chapman_and_sun_companion_families",
            "payload": {
                "submode": "sun_conjecture_part_ii_check",
                "prime_p": 23,
                "x": _r(7, 11),
                "y": _r(-3, 2),
                "z": _r(5, 3),
                "w": _r(1, 7),
            },
        },
    ))

    return certs


def main() -> int:
    CERTS_DIR.mkdir(parents=True, exist_ok=True)
    certs = build_certificates()
    for fname, obj in certs:
        out_path = CERTS_DIR / fname
        out_path.write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")
        res = verify_file(out_path)
        print(f"[OK] {fname}: {res}")
    print(f"Generated and verified {len(certs)} certificates in {CERTS_DIR}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
