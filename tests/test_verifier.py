"""
Comprehensive unit, adversarial forgery, security, and zero-float AST audit tests
for LEGENDRE-DET-SYM-CERT-1.0 (src/legendre_det_verifier.py).
"""

from __future__ import annotations

import ast
import json
import pathlib
import sys

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.legendre_det_verifier import MAX_JSON_BYTES, SCHEMA_VERSION, VerificationError, main, verify_certificate, verify_file

CERTS_DIR = ROOT / "certificates"
VERIFIER_PATH = ROOT / "src" / "legendre_det_verifier.py"

CANONICAL_FILES = sorted(p.name for p in CERTS_DIR.glob("C*.json"))


def _load(name: str) -> dict:
    return json.loads((CERTS_DIR / name).read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# 1. Canonical 16-Certificate Verification + CLI
# ---------------------------------------------------------------------------

def test_canonical_count_is_16() -> None:
    assert len(CANONICAL_FILES) == 16


@pytest.mark.parametrize("fname", CANONICAL_FILES)
def test_canonical_certificate_verifies(fname: str) -> None:
    res = verify_file(CERTS_DIR / fname)
    assert res["status"] == "VERIFIED"
    assert res["certificate_id"] == fname.removesuffix(".json")


def test_cli_directory_mode_exits_zero() -> None:
    assert main([str(CERTS_DIR)]) == 0


def test_cli_no_args_and_empty_dir(tmp_path: pathlib.Path) -> None:
    assert main([]) == 2
    assert main([str(tmp_path)]) == 2


# ---------------------------------------------------------------------------
# 2. Zero-Float AST & Import Audit on Verifier Source
# ---------------------------------------------------------------------------

def test_verifier_has_zero_floats_no_truediv_no_math_numpy() -> None:
    src = VERIFIER_PATH.read_text(encoding="utf-8")
    tree = ast.parse(src)
    forbidden_mods = {"math", "cmath", "numpy", "scipy", "decimal"}
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            pytest.fail(f"Float literal found in verifier: {node.value}")
        if isinstance(node, ast.Div):
            pytest.fail("True division operator (/) found in verifier")
        if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Div):
            pytest.fail("In-place true division (/=) found in verifier")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float":
            pytest.fail("float() call found in verifier")
        if isinstance(node, ast.Import):
            for alias in node.names:
                assert alias.name.split(".")[0] not in forbidden_mods
        if isinstance(node, ast.ImportFrom) and node.module:
            assert node.module.split(".")[0] not in forbidden_mods


# ---------------------------------------------------------------------------
# 3. Schema, Security, Duplicate-Key, Float-Literal & Bounds Hardening
# ---------------------------------------------------------------------------

def test_reject_wrong_schema_and_unknown_modes() -> None:
    c = _load("C01_sun_conj32_p17_mod8_1.json")
    c["schema_version"] = "BAD-1.0"
    with pytest.raises(VerificationError, match="schema_version"):
        verify_certificate(c)

    c2 = _load("C01_sun_conj32_p17_mod8_1.json")
    c2["mode"] = "bogus_mode"
    with pytest.raises(VerificationError, match="Unknown mode"):
        verify_certificate(c2)

    for fn in (
        "C01_sun_conj32_p17_mod8_1.json",
        "C05_cyclotomic_vandermonde_p13.json",
        "C09_eq24_rational_collapse_p13.json",
        "C13_chapman_F_M1_p13.json",
    ):
        c3 = _load(fn)
        c3["payload"]["submode"] = "bogus_sub"
        with pytest.raises(VerificationError, match="Unknown Mode"):
            verify_certificate(c3)


def test_reject_float_nan_dup_oversize_dir_deep(tmp_path: pathlib.Path) -> None:
    p1 = tmp_path / "f.json"
    p1.write_text('{"x": 2.5}', encoding="utf-8")
    with pytest.raises(VerificationError, match="floating-point"):
        verify_file(p1)

    p2 = tmp_path / "n.json"
    p2.write_text('{"x": NaN}', encoding="utf-8")
    with pytest.raises(VerificationError, match="non-finite"):
        verify_file(p2)

    p3 = tmp_path / "d.json"
    p3.write_text('{"a": 1, "a": 2}', encoding="utf-8")
    with pytest.raises(VerificationError, match="Duplicate JSON key"):
        verify_file(p3)

    p4 = tmp_path / "big.json"
    p4.write_bytes(b" " * (MAX_JSON_BYTES + 10))
    with pytest.raises(VerificationError, match="MAX_JSON_BYTES"):
        verify_file(p4)

    with pytest.raises(VerificationError, match="not a readable file"):
        verify_file(tmp_path)

    p5 = tmp_path / "deep.json"
    p5.write_text("[" * 5000 + "]" * 5000, encoding="utf-8")
    with pytest.raises(VerificationError, match="Invalid JSON"):
        verify_file(p5)


def test_reject_unreduced_rational_and_bool() -> None:
    c = _load("C01_sun_conj32_p17_mod8_1.json")
    c["payload"]["x"] = [6, 4]
    with pytest.raises(VerificationError, match="lowest terms"):
        verify_certificate(c)

    c2 = _load("C01_sun_conj32_p17_mod8_1.json")
    c2["payload"]["prime_p"] = True
    with pytest.raises(VerificationError, match="Expected integer"):
        verify_certificate(c2)


# ---------------------------------------------------------------------------
# 4. Mode 1 Adversarial Forgeries
# ---------------------------------------------------------------------------

def test_mode1a_rejects_composite_p() -> None:
    c = _load("C01_sun_conj32_p17_mod8_1.json")
    c["payload"]["prime_p"] = 15
    with pytest.raises(VerificationError, match="not prime"):
        verify_certificate(c)


def test_mode1a_rejects_wrong_unit_norm() -> None:
    c = _load("C01_sun_conj32_p17_mod8_1.json")
    c["payload"]["a_p"] = [5, 1]  # 25 - 17 != -1
    with pytest.raises(VerificationError, match="Unit norm"):
        verify_certificate(c)


def test_mode1a_rejects_wrong_unit_power_with_valid_norm() -> None:
    # For p=17, eps_17^3 = (4+sqrt(17))^3 = 268 + 65*sqrt(17) has norm -1,
    # BUT h_17 = 1 so Theorem 1.1(i) Eq. (1.3) must REJECT it!
    c = _load("C01_sun_conj32_p17_mod8_1.json")
    c["payload"]["a_p"] = [268, 1]
    c["payload"]["b_p"] = [65, 1]
    with pytest.raises(VerificationError, match="Theorem 1.1\\(i\\)"):
        verify_certificate(c)


def test_mode1b_rejects_singular_matrix_A() -> None:
    c = _load("C04_lemma21_and_eq22_p13.json")
    c["payload"]["matrix_A"][2] = c["payload"]["matrix_A"][0]
    with pytest.raises(VerificationError, match="invertible"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 5. Mode 2 Adversarial Forgeries (Cyclotomic Q[zeta_p])
# ---------------------------------------------------------------------------

def test_mode2a_rejects_wrong_cp_sign_for_p23() -> None:
    # For p=23, h_{-23} = 3 => (-1)^2 = +1; flipping sign_cp to -1 must fail Eq. (2.5)!
    c = _load("C06_cyclotomic_vandermonde_p23.json")
    c["payload"]["sign_cp"] = -1
    with pytest.raises(VerificationError, match="Eq\\. \\(2\\.5\\)"):
        verify_certificate(c)


def test_mode2a_rejects_wrong_unit_for_p13() -> None:
    # eps_13^3 = (3/2 + 1/2*sqrt(13))^3 = 36/2 + 10/2*sqrt(13) = 18 + 5*sqrt(13) (norm 324-325=-1)
    c = _load("C05_cyclotomic_vandermonde_p13.json")
    c["payload"]["a_p"] = [18, 1]
    c["payload"]["b_p"] = [5, 1]
    with pytest.raises(VerificationError, match="Eq\\. \\(2\\.5\\)"):
        verify_certificate(c)


def test_mode2b_rejects_composite_prime() -> None:
    c = _load("C07_lagrange_forms_p11.json")
    c["payload"]["prime_p"] = 9
    with pytest.raises(VerificationError, match="not prime"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 6. Mode 3 Adversarial Forgeries
# ---------------------------------------------------------------------------

def test_mode3a_rejects_duplicate_x() -> None:
    c = _load("C09_eq24_rational_collapse_p13.json")
    c["payload"]["x_values"][1] = c["payload"]["x_values"][0]
    with pytest.raises(VerificationError, match="Duplicate x"):
        verify_certificate(c)


def test_mode3b_rejects_even_class_number() -> None:
    c = _load("C11_real_quad_units_p5_to_p41.json")
    c["payload"]["prime_units"][0]["class_number_h"] = 2
    with pytest.raises(VerificationError, match="must be odd"):
        verify_certificate(c)


def test_mode3b_rejects_p_3mod4_in_real_quad_units() -> None:
    c = _load("C11_real_quad_units_p5_to_p41.json")
    c["payload"]["prime_units"][0]["prime_p"] = 7
    with pytest.raises(VerificationError, match="1 mod 4"):
        verify_certificate(c)


def test_mode3b_rejects_forged_ap_bp() -> None:
    c = _load("C12_real_quad_units_higher_h3_p229.json")
    c["payload"]["prime_units"][-1]["a_p"] = [15, 2]  # h=3, not h=1!
    with pytest.raises(VerificationError, match="eps_p\\^h mismatch"):
        verify_certificate(c)


def test_mode3b_rejects_duplicate_prime() -> None:
    c = _load("C11_real_quad_units_p5_to_p41.json")
    c["payload"]["prime_units"][1] = c["payload"]["prime_units"][0]
    with pytest.raises(VerificationError, match="Duplicate prime"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 7. Mode 4 Adversarial Forgeries (Chapman F(x) & Sun Part (ii))
# ---------------------------------------------------------------------------

def test_mode4a_rejects_composite_p() -> None:
    c = _load("C13_chapman_F_M1_p13.json")
    c["payload"]["prime_p"] = 15
    with pytest.raises(VerificationError, match="not prime"):
        verify_certificate(c)


def test_mode4b_rejects_wrong_unit_in_part_ii() -> None:
    # For p=13, eps_13^3 = 18 + 5*sqrt(13) has norm -1, but passing it as (a_p, b_p) gives eps^9 instead of eps^3!
    c = _load("C15_sun_part2_minus_p13.json")
    c["payload"]["a_p"] = [18, 1]
    c["payload"]["b_p"] = [5, 1]
    with pytest.raises(VerificationError, match="Theorem 1\\.1\\(ii\\)"):
        verify_certificate(c)


def test_mode4b_exact_p23_equals_x() -> None:
    r16 = verify_file(CERTS_DIR / "C16_sun_part2_minus_p23.json")
    assert r16["det_A_minus"] == [7, 11]
