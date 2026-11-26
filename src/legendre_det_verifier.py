"""
LEGENDRE-DET-SYM-CERT-1.0: Zero-floating-point exact algebraic and cyclotomic verifier for
Roman Le Lan and Keqin Liu's "Symmetric identities and determinants for matrices composed
of Legendre symbols" (arXiv:2611.33667v1, November 25, 2026), resolving Sun's Conjecture 3.2(i).

Strictly zero floating-point literals, zero float() calls, zero true-division (/ or /=),
and zero math/numpy imports. All arithmetic uses exact Python int, fractions.Fraction,
and exact cyclotomic field arithmetic Q[zeta_p] = Q[X] / (Phi_p(X)).
"""

from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction
from typing import Any

SCHEMA_VERSION = "LEGENDRE-DET-SYM-CERT-1.0"
MAX_JSON_BYTES = 1_000_000
MAX_RAT_ABS = 10**18


class VerificationError(ValueError):
    """Raised whenever a certificate violates schema, bounds, or mathematical invariants."""


def _gcd(a: int, b: int) -> int:
    a = abs(a)
    b = abs(b)
    while b:
        a, b = b, a % b
    return a


def _req_int(val: Any, name: str, lo: int | None = None, hi: int | None = None) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise VerificationError(f"Expected integer for {name}, got {type(val).__name__}")
    if lo is not None and val < lo:
        raise VerificationError(f"{name}={val} below minimum {lo}")
    if hi is not None and val > hi:
        raise VerificationError(f"{name}={val} above maximum {hi}")
    return val


def _req_str(val: Any, name: str) -> str:
    if not isinstance(val, str) or not val.strip():
        raise VerificationError(f"Expected non-empty string for {name}")
    return val


def _req_list(val: Any, name: str, min_len: int = 0, max_len: int = 4096) -> list[Any]:
    if not isinstance(val, list):
        raise VerificationError(f"Expected list for {name}")
    if len(val) < min_len or len(val) > max_len:
        raise VerificationError(f"{name} length {len(val)} out of range [{min_len}, {max_len}]")
    return val


def _req_dict(val: Any, name: str) -> dict[str, Any]:
    if not isinstance(val, dict):
        raise VerificationError(f"Expected dict for {name}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if not isinstance(val, list) or len(val) != 2:
        raise VerificationError(f"Expected [num, den] rational pair for {name}")
    num = _req_int(val[0], f"{name}[0]", -MAX_RAT_ABS, MAX_RAT_ABS)
    den = _req_int(val[1], f"{name}[1]", 1, MAX_RAT_ABS)
    if _gcd(num, den) != 1:
        raise VerificationError(f"Rational {name}=[{num},{den}] not in lowest terms")
    return Fraction(num, den)


def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise VerificationError(f"Duplicate JSON key: {k}")
        out[k] = v
    return out


def _reject_json_constant(token: str) -> Any:
    raise VerificationError(f"Illegal non-finite JSON constant: {token}")


def _reject_json_float(token: str) -> Any:
    raise VerificationError(f"Illegal floating-point JSON literal: {token}")


# ---------------------------------------------------------------------------
# Number-Theoretic & Exact Linear Algebra Helpers
# ---------------------------------------------------------------------------

def _is_prime(p: int) -> bool:
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    d = 3
    while d * d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


def _legendre(a: int, p: int) -> int:
    a_mod = a % p
    if a_mod == 0:
        return 0
    r = pow(a_mod, (p - 1) // 2, p)
    return 1 if r == 1 else -1


def _det_Q(mat: list[list[Fraction]]) -> Fraction:
    """Exact determinant over Q via Gaussian elimination (zero floats)."""
    n = len(mat)
    A = [list(row) for row in mat]
    det = Fraction(1, 1)
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv == -1:
            return Fraction(0, 1)
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            det = -det
        pv = A[col][col]
        det *= pv
        inv_pv = Fraction(pv.denominator, pv.numerator)
        for r in range(col + 1, n):
            f = A[r][col] * inv_pv
            if f != 0:
                for c in range(col, n):
                    A[r][c] -= f * A[col][c]
    return det


def _inv_Q(mat: list[list[Fraction]]) -> list[list[Fraction]]:
    """Exact matrix inverse over Q via Gauss-Jordan elimination."""
    n = len(mat)
    aug = [list(mat[i]) + [Fraction(1 if i == j else 0, 1) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        if piv == -1:
            raise VerificationError("Matrix is singular over Q")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        inv_pv = Fraction(pv.denominator, pv.numerator)
        for c in range(2 * n):
            aug[col][c] *= inv_pv
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                for c in range(2 * n):
                    aug[r][c] -= f * aug[col][c]
    return [row[n:] for row in aug]


# ---------------------------------------------------------------------------
# Exact Cyclotomic Field Q[zeta_p] = Q[X] / (1 + X + ... + X^{p-1})
# ---------------------------------------------------------------------------

def _cyc_zero(p: int) -> list[Fraction]:
    return [Fraction(0, 1)] * (p - 1)


def _cyc_scalar(p: int, val: Fraction) -> list[Fraction]:
    out = _cyc_zero(p)
    out[0] = val
    return out


def _cyc_zeta(p: int, exp: int) -> list[Fraction]:
    r = exp % p
    if r < p - 1:
        out = _cyc_zero(p)
        out[r] = Fraction(1, 1)
        return out
    return [Fraction(-1, 1)] * (p - 1)


def _cyc_add(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    return [x + y for x, y in zip(a, b)]


def _cyc_sub(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    return [x - y for x, y in zip(a, b)]


def _cyc_neg(a: list[Fraction]) -> list[Fraction]:
    return [-x for x in a]


def _cyc_scale(a: list[Fraction], s: Fraction) -> list[Fraction]:
    return [x * s for x in a]


def _cyc_mul(p: int, a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    d = p - 1
    prod = [Fraction(0, 1)] * (2 * d - 1)
    for i in range(d):
        ai = a[i]
        if ai == 0:
            continue
        for j in range(d):
            bj = b[j]
            if bj != 0:
                prod[i + j] += ai * bj
    # Reduce modulo 1 + X + ... + X^{p-1}: X^{p-1} = -(1 + ... + X^{p-2}), X^p = 1, X^{p+k} = X^k
    out = list(prod[:d])
    if len(prod) > d - 1:
        c_pm1 = prod[d]  # X^{p-1}
        if c_pm1 != 0:
            for i in range(d):
                out[i] -= c_pm1
    for k in range(p, len(prod)):
        if prod[k] != 0:
            out[k - p] += prod[k]
    return out


def _cyc_pow(p: int, a: list[Fraction], e: int) -> list[Fraction]:
    res = _cyc_scalar(p, Fraction(1, 1))
    base = list(a)
    while e > 0:
        if e & 1:
            res = _cyc_mul(p, res, base)
        base = _cyc_mul(p, base, base)
        e >>= 1
    return res


def _poly_trim(poly: list[Fraction]) -> list[Fraction]:
    out = list(poly)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def _poly_divmod(num: list[Fraction], den: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    a = _poly_trim(num)
    b = _poly_trim(den)
    if b == [Fraction(0, 1)]:
        raise VerificationError("Polynomial division by zero")
    deg_b = len(b) - 1
    inv_lb = Fraction(b[-1].denominator, b[-1].numerator)
    if len(a) - 1 < deg_b:
        return [Fraction(0, 1)], a
    q = [Fraction(0, 1)] * (len(a) - deg_b)
    for k in range(len(a) - deg_b - 1, -1, -1):
        coeff = a[k + deg_b] * inv_lb
        q[k] = coeff
        if coeff != 0:
            for j in range(deg_b + 1):
                a[k + j] -= coeff * b[j]
    return _poly_trim(q), _poly_trim(a)


def _cyc_inv(p: int, a: list[Fraction]) -> list[Fraction]:
    """Exact inverse in Q[X] / (Phi_p(X)) via extended Euclidean algorithm."""
    phi = [Fraction(1, 1)] * p
    r0 = phi
    r1 = _poly_trim(a)
    if r1 == [Fraction(0, 1)]:
        raise VerificationError("Division by zero in Q[zeta_p]")
    t0 = [Fraction(0, 1)]
    t1 = [Fraction(1, 1)]
    while not (len(r1) == 1 and r1[0] == 0):
        q, r2 = _poly_divmod(r0, r1)
        # t2 = t0 - q * t1
        qt1 = [Fraction(0, 1)] * (len(q) + len(t1) - 1)
        for i, qi in enumerate(q):
            if qi != 0:
                for j, tj in enumerate(t1):
                    qt1[i + j] += qi * tj
        max_len = max(len(t0), len(qt1))
        t2 = [
            (t0[i] if i < len(t0) else Fraction(0, 1)) - (qt1[i] if i < len(qt1) else Fraction(0, 1))
            for i in range(max_len)
        ]
        r0, r1 = r1, r2
        t0, t1 = t1, _poly_trim(t2)
    if len(r0) != 1 or r0[0] == 0:
        raise VerificationError("Element not invertible in Q[zeta_p]")
    inv_c = Fraction(r0[0].denominator, r0[0].numerator)
    _, rem = _poly_divmod([c * inv_c for c in t0], phi)
    out = rem + [Fraction(0, 1)] * (p - 1 - len(rem))
    return out[: p - 1]


def _cyc_gauss_sum(p: int) -> list[Fraction]:
    """Exact tau_p = 1 + 2 * sum_{k=1}^{(p-1)/2} zeta^{k^2} in Q[zeta_p]."""
    n = (p - 1) // 2
    acc = _cyc_scalar(p, Fraction(1, 1))
    for k in range(1, n + 1):
        acc = _cyc_add(acc, _cyc_scale(_cyc_zeta(p, (k * k) % p), Fraction(2, 1)))
    return acc


def _cyc_cp(p: int) -> list[Fraction]:
    """Exact c_p = prod_{k=1}^{(p-1)/2} (1 - zeta^{k^2}) in Q[zeta_p]."""
    n = (p - 1) // 2
    one = _cyc_scalar(p, Fraction(1, 1))
    acc = list(one)
    for k in range(1, n + 1):
        acc = _cyc_mul(p, acc, _cyc_sub(one, _cyc_zeta(p, (k * k) % p)))
    return acc


def _cyc_solve(p: int, mat: list[list[list[Fraction]]], rhs: list[list[Fraction]]) -> list[list[Fraction]]:
    """Solve mat * x = rhs over Q[zeta_p] via exact Gauss-Jordan elimination."""
    n = len(mat)
    A = [[list(mat[i][j]) for j in range(n)] for i in range(n)]
    b = [list(rhs[i]) for i in range(n)]
    z0 = _cyc_zero(p)
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if A[r][col] != z0:
                piv = r
                break
        if piv == -1:
            raise VerificationError("Singular matrix over Q[zeta_p]")
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            b[col], b[piv] = b[piv], b[col]
        inv_pv = _cyc_inv(p, A[col][col])
        for c in range(col, n):
            A[col][c] = _cyc_mul(p, A[col][c], inv_pv)
        b[col] = _cyc_mul(p, b[col], inv_pv)
        for r in range(n):
            if r != col and A[r][col] != z0:
                f = A[r][col]
                for c in range(col, n):
                    A[r][c] = _cyc_sub(A[r][c], _cyc_mul(p, f, A[col][c]))
                b[r] = _cyc_sub(b[r], _cyc_mul(p, f, b[col]))
    return b


def _cyc_poly_mul(p: int, f: list[list[Fraction]], g: list[list[Fraction]]) -> list[list[Fraction]]:
    res = [_cyc_zero(p) for _ in range(len(f) + len(g) - 1)]
    for i, fi in enumerate(f):
        for j, gj in enumerate(g):
            res[i + j] = _cyc_add(res[i + j], _cyc_mul(p, fi, gj))
    return res


def _build_A_matrix(p: int, x: Fraction, y: Fraction, z: Fraction, w: Fraction) -> list[list[Fraction]]:
    n = (p - 1) // 2
    return [
        [
            x
            + Fraction(_legendre(i + j, p), 1)
            + Fraction(_legendre(i, p), 1) * y
            + Fraction(_legendre(j, p), 1) * z
            + Fraction(_legendre(i * j, p), 1) * w
            for j in range(n)
        ]
        for i in range(n)
    ]


def _build_H_matrix(p: int, x: Fraction) -> list[list[Fraction]]:
    n = (p - 1) // 2
    return [[x + Fraction(_legendre(i + j, p), 1) for j in range(n)] for i in range(n)]


# ---------------------------------------------------------------------------
# Mode 1: matrix_reduction_and_det_lemma (Thm. 1.1(i), Eq. (2.1), Lemma 2.1, Eq. (2.2))
# ---------------------------------------------------------------------------

def _verify_mode1(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "sun_conjecture_direct_det":
        p = _req_int(payload.get("prime_p"), "prime_p", 5, 43)
        if not _is_prime(p):
            raise VerificationError(f"p={p} is not prime")
        x = _parse_rat(payload.get("x"), "x")
        y = _parse_rat(payload.get("y"), "y")
        z = _parse_rat(payload.get("z"), "z")
        w = _parse_rat(payload.get("w"), "w")

        det_A = _det_Q(_build_A_matrix(p, x, y, z, w))
        H0 = _det_Q(_build_H_matrix(p, Fraction(0, 1)))
        H1 = _det_Q(_build_H_matrix(p, Fraction(1, 1)))

        # Verify Eq. (2.1): A(x,y,z,w) = x*H(1) + (1 - x + y + z + yz - wx)*H(0)
        eq21_rhs = x * H1 + (1 - x + y + z + y * z - w * x) * H0
        if det_A != eq21_rhs:
            raise VerificationError(f"Eq. (2.1) failed for p={p}: det_A={det_A} != {eq21_rhs}")

        v = w * x - (y + 1) * (z + 1)
        pow2 = Fraction(1 << ((p - 3) // 2), 1)
        if p % 4 == 1:
            ap = _parse_rat(payload.get("a_p"), "a_p")
            bp = _parse_rat(payload.get("b_p"), "b_p")
            if ap <= 0 or bp <= 0:
                raise VerificationError("a_p and b_p must be strictly positive for eps_p^{h_p} > 1")
            if ap * ap - p * bp * bp != -1:
                raise VerificationError(f"Unit norm identity a_p^2 - p*b_p^2 == -1 failed for p={p}")
            leg2 = _legendre(2, p)
            expected = Fraction(leg2, 1) * pow2 * ((p * bp - 2 * ap) * x + (ap - 2 * bp) * v)
        else:
            expected = pow2 * (v - 2 * x)

        if det_A != expected:
            raise VerificationError(f"Theorem 1.1(i) Eq. (1.3) failed for p={p}: det_A={det_A} != {expected}")

        return {
            "mode": "matrix_reduction_and_det_lemma",
            "submode": submode,
            "prime_p": p,
            "matrix_dim": (p - 1) // 2,
            "det_A": [det_A.numerator, det_A.denominator],
            "H0": [H0.numerator, H0.denominator],
            "H1": [H1.numerator, H1.denominator],
        }

    if submode == "rank2_matrix_det_lemma":
        # Verify Lemma 2.1 on explicit rational matrix A + a*u*u^T + b*v*v^T,
        # AND verify Eq. (2.2) matrix identity in Q[zeta_p] for prime p!
        m = _req_int(payload.get("dim_m"), "dim_m", 2, 8)
        A_raw = _req_list(payload.get("matrix_A"), "matrix_A", m, m)
        A = [[_parse_rat(c, f"A[{i}][{j}]") for j, c in enumerate(_req_list(A_raw[i], f"A[{i}]", m, m))] for i in range(m)]
        u = [_parse_rat(c, f"u[{i}]") for i, c in enumerate(_req_list(payload.get("vec_u"), "vec_u", m, m))]
        v = [_parse_rat(c, f"v[{i}]") for i, c in enumerate(_req_list(payload.get("vec_v"), "vec_v", m, m))]
        a_sc = _parse_rat(payload.get("scalar_a"), "scalar_a")
        b_sc = _parse_rat(payload.get("scalar_b"), "scalar_b")

        detA = _det_Q(A)
        if detA == 0:
            raise VerificationError("Matrix A must be invertible for Lemma 2.1")
        Ainv = _inv_Q(A)

        def bform(vec1: list[Fraction], vec2: list[Fraction]) -> Fraction:
            return sum(vec1[i] * Ainv[i][j] * vec2[j] for i in range(m) for j in range(m))

        alpha = bform(u, u)
        beta = bform(v, v)
        gamma = bform(u, v)
        delta = bform(v, u)
        rhs_lem21 = detA * ((1 + a_sc * alpha) * (1 + b_sc * beta) - a_sc * b_sc * gamma * delta)

        pert = [[A[i][j] + a_sc * u[i] * u[j] + b_sc * v[i] * v[j] for j in range(m)] for i in range(m)]
        lhs_lem21 = _det_Q(pert)
        if lhs_lem21 != rhs_lem21:
            raise VerificationError(f"Lemma 2.1 failed: {lhs_lem21} != {rhs_lem21}")

        # Verify Eq. (2.2) exact cyclotomic entrywise identity for prime p and rational x
        p = _req_int(payload.get("prime_p"), "prime_p", 5, 19)
        if not _is_prime(p):
            raise VerificationError(f"p={p} is not prime")
        x = _parse_rat(payload.get("x"), "x")
        n = (p - 1) // 2
        tau = _cyc_gauss_sum(p)
        M = [[_cyc_zeta(p, (i * (j + 1) * (j + 1)) % p) for j in range(n)] for i in range(n)]
        x_tau_plus_1 = _cyc_add(_cyc_scale(tau, x), _cyc_scalar(p, Fraction(1, 1)))
        for i in range(n):
            for j in range(n):
                lhs = _cyc_scale(tau, x + Fraction(_legendre(i + j, p), 1))
                mmt = _cyc_zero(p)
                for k in range(n):
                    mmt = _cyc_add(mmt, _cyc_mul(p, M[i][k], M[j][k]))
                rhs = _cyc_add(_cyc_scale(mmt, Fraction(2, 1)), x_tau_plus_1)
                if i == 0 and j == 0:
                    rhs = _cyc_sub(rhs, _cyc_scalar(p, Fraction(p, 1)))
                if lhs != rhs:
                    raise VerificationError(f"Eq. (2.2) cyclotomic entry mismatch at ({i},{j}) for p={p}")

        return {
            "mode": "matrix_reduction_and_det_lemma",
            "submode": submode,
            "lemma21_det": [lhs_lem21.numerator, lhs_lem21.denominator],
            "prime_p": p,
            "eq22_entries_verified": n * n,
        }

    raise VerificationError(f"Unknown Mode 1 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 2: cyclotomic_vandermonde_and_forms (Sec. 2.2-2.5 Eq. (1.5)-(1.6), (2.3), alpha1..delta1)
# ---------------------------------------------------------------------------

def _verify_mode2(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")
    p = _req_int(payload.get("prime_p"), "prime_p", 5, 23)
    if not _is_prime(p):
        raise VerificationError(f"p={p} is not prime")
    n = (p - 1) // 2
    tau = _cyc_gauss_sum(p)
    cp = _cyc_cp(p)

    if submode == "gauss_sum_and_vandermonde_sq":
        # 1. Verify Eq. (1.5): tau_p^2 == (-1)^((p-1)/2) * p
        expected_tau_sq = Fraction(p if p % 4 == 1 else -p, 1)
        if _cyc_mul(p, tau, tau) != _cyc_scalar(p, expected_tau_sq):
            raise VerificationError(f"Gauss sum square Eq. (1.5) failed for p={p}")

        # 2. Verify Eq. (1.6) Galois identity for ALL m = 1..p-1
        for m in range(1, p):
            s_m = _cyc_scalar(p, Fraction(1, 1))
            for k in range(1, n + 1):
                s_m = _cyc_add(s_m, _cyc_scale(_cyc_zeta(p, (m * k * k) % p), Fraction(2, 1)))
            lhs = _cyc_scale(tau, Fraction(_legendre(m, p), 1))
            if lhs != s_m:
                raise VerificationError(f"Eq. (1.6) failed at m={m} for p={p}")

        # 3. Compute exact det(M)^2 = prod_{1 <= i < j <= n} (zeta^{j^2} - zeta^{i^2})^2 in Q[zeta_p]
        detM = _cyc_scalar(p, Fraction(1, 1))
        for i in range(1, n + 1):
            zi = _cyc_zeta(p, (i * i) % p)
            for j in range(i + 1, n + 1):
                zj = _cyc_zeta(p, (j * j) % p)
                detM = _cyc_mul(p, detM, _cyc_sub(zj, zi))
        detM_sq = _cyc_mul(p, detM, detM)

        # 4. Verify Eq. (2.3) and Eq. (2.5) in Q[zeta_p]!
        if p % 4 == 1:
            ap = _parse_rat(payload.get("a_p"), "a_p")
            bp = _parse_rat(payload.get("b_p"), "b_p")
            if ap <= 0 or bp <= 0 or ap * ap - p * bp * bp != -1:
                raise VerificationError("Invalid (a_p, b_p) unit coordinates")
            # eps_p^{h_p} = a_p + b_p * tau_p (since tau_p = +sqrt(p) in embedding)
            # Note: In abstract Q[zeta_p], tau_p^2 = p, and c_p = b_p*p - a_p*tau_p (or with sign of tau_p matching Galois!).
            # Verify BOTH exact sign consistency: c_p == b_p*p - a_p*tau_p (with canonical tau_p = sum (m/p) zeta^m = +sqrt(p))!
            exp_cp = _cyc_sub(_cyc_scalar(p, bp * p), _cyc_scale(tau, ap))
            if cp != exp_cp:
                raise VerificationError(f"Eq. (2.5) failed for p={p}")
            eps_h = _cyc_add(_cyc_scalar(p, ap), _cyc_scale(tau, bp))
            # det(M)^2 = (2/p) * p^{(p-3)/4} * eps_p^{h_p} where p^{(p-3)/4} = p^{(p-5)/4} * sqrt(p) = p^{(p-5)/4} * tau_p!
            p_pow = Fraction(p ** ((p - 5) // 4), 1)
            leg2 = Fraction(_legendre(2, p), 1)
            exp_detM_sq = _cyc_scale(_cyc_mul(p, tau, eps_h), leg2 * p_pow)
            if detM_sq != exp_detM_sq:
                raise VerificationError(f"Eq. (2.3) failed for p={p}")
        else:
            # p = 3 mod 4: det(M)^2 = (-p)^{(p-3)/4} (exact rational!), and c_p = sign * tau_p!
            sign_cp = _req_int(payload.get("sign_cp"), "sign_cp", -1, 1)
            if sign_cp not in (-1, 1):
                raise VerificationError("sign_cp must be -1 or 1")
            if cp != _cyc_scale(tau, Fraction(sign_cp, 1)):
                raise VerificationError(f"Eq. (2.5) failed for p={p} (check sign_cp)")
            exp_detM_sq = _cyc_scalar(p, Fraction((-p) ** ((p - 3) // 4), 1))
            if detM_sq != exp_detM_sq:
                raise VerificationError(f"Eq. (2.3) failed for p={p}")

        return {
            "mode": "cyclotomic_vandermonde_and_forms",
            "submode": submode,
            "prime_p": p,
            "galois_checks": p - 1,
            "eq15_eq23_eq25_verified": True,
        }

    if submode == "lagrange_partial_fractions_forms":
        # Verify exact Euclidean divisions P_1 = (X + tau_p)*Q_1 + R_1 and P_2 = (X + tau_p - 1)*Q_2 + R_2,
        # AND solve M*a = u, M*b = v over Q[zeta_p] to verify alpha1, beta1, gamma1 = delta1 identically!
        M = [[_cyc_zeta(p, (i * (j + 1) * (j + 1)) % p) for j in range(n)] for i in range(n)]
        one = _cyc_scalar(p, Fraction(1, 1))
        zero = _cyc_zero(p)
        u = [list(one) for _ in range(n)]
        v = [list(one)] + [list(zero) for _ in range(n - 1)]

        a_vec = _cyc_solve(p, M, u)
        b_vec = _cyc_solve(p, M, v)

        def dot_cyc(v1: list[list[Fraction]], v2: list[list[Fraction]]) -> list[Fraction]:
            acc = _cyc_zero(p)
            for c1, c2 in zip(v1, v2):
                acc = _cyc_add(acc, _cyc_mul(p, c1, c2))
            return acc

        alpha1 = dot_cyc(a_vec, a_vec)
        beta1 = dot_cyc(b_vec, b_vec)
        gamma1 = dot_cyc(a_vec, b_vec)

        inv_p = Fraction(1, p)
        cp_sq = _cyc_mul(p, cp, cp)
        exp_alpha1 = _cyc_sub(_cyc_scale(_cyc_mul(p, cp_sq, _cyc_add(one, tau)), inv_p), one)
        exp_beta1 = _cyc_scale(tau, inv_p)
        sign_n = Fraction(1 if n % 2 == 0 else -1, 1)
        exp_gamma1 = _cyc_scale(_cyc_mul(p, cp, tau), sign_n * inv_p)

        if alpha1 != exp_alpha1:
            raise VerificationError(f"alpha1 closed form failed for p={p}")
        if beta1 != exp_beta1:
            raise VerificationError(f"beta1 closed form failed for p={p}")
        if gamma1 != exp_gamma1:
            raise VerificationError(f"gamma1=delta1 closed form failed for p={p}")

        # Verify Euclidean division quotients of P_1 by Q_1 (X + tau_p) and P_2 by Q_2 (X + tau_p - 1) in Q[zeta_p][X]!
        # Q_1 = Q_2 = prod_{k=1}^n (X - zeta^{k^2})
        # P_1 = X * prod_{i in N} (X - zeta^i), P_2 = (X - 1) * prod_{i in N} (X - zeta^i)
        Q_poly = [one]
        for k in range(1, n + 1):
            Q_poly = _cyc_poly_mul(p, Q_poly, [_cyc_neg(_cyc_zeta(p, (k * k) % p)), one])

        N_nonres = [i for i in range(1, p) if _legendre(i, p) == -1]
        prod_N = [one]
        for nr in N_nonres:
            prod_N = _cyc_poly_mul(p, prod_N, [_cyc_neg(_cyc_zeta(p, nr)), one])

        P1_poly = [zero] + prod_N
        P2_poly = _cyc_poly_mul(p, [_cyc_neg(one), one], prod_N)

        # Check deg(P_1 - (X + tau_p)*Q_1) < n and deg(P_2 - (X + tau_p - 1)*Q_1) < n!
        q1_Q = _cyc_poly_mul(p, [tau, one], Q_poly)
        q2_Q = _cyc_poly_mul(p, [_cyc_sub(tau, one), one], Q_poly)
        for deg in (n, n + 1):
            if _cyc_sub(P1_poly[deg], q1_Q[deg]) != zero:
                raise VerificationError(f"Euclidean quotient (X + tau_p) failed at degree {deg} for p={p}")
            if _cyc_sub(P2_poly[deg], q2_Q[deg]) != zero:
                raise VerificationError(f"Euclidean quotient (X + tau_p - 1) failed at degree {deg} for p={p}")

        return {
            "mode": "cyclotomic_vandermonde_and_forms",
            "submode": submode,
            "prime_p": p,
            "dim_n": n,
            "forms_and_quotients_verified": True,
        }

    raise VerificationError(f"Unknown Mode 2 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 3: final_evaluation_and_unit_norms (Sec. 2.6 Eq. (2.4)-(2.6) & Pell Units)
# ---------------------------------------------------------------------------

def _verify_mode3(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "eq24_to_eq26_rational_collapse":
        p = _req_int(payload.get("prime_p"), "prime_p", 5, 19)
        if not _is_prime(p):
            raise VerificationError(f"p={p} is not prime")
        xs_raw = _req_list(payload.get("x_values"), "x_values", 2, 12)
        xs = [_parse_rat(r, f"x_values[{i}]") for i, r in enumerate(xs_raw)]
        if len(set(xs)) != len(xs):
            raise VerificationError("Duplicate x value in x_values")

        n = (p - 1) // 2
        tau = _cyc_gauss_sum(p)
        tau2 = _cyc_mul(p, tau, tau)
        tau_n_inv = _cyc_inv(p, _cyc_pow(p, tau, n))
        cp = _cyc_cp(p)
        cp2 = _cyc_mul(p, cp, cp)
        detM = _cyc_scalar(p, Fraction(1, 1))
        for i in range(1, n + 1):
            zi = _cyc_zeta(p, (i * i) % p)
            for j in range(i + 1, n + 1):
                detM = _cyc_mul(p, detM, _cyc_sub(_cyc_zeta(p, (j * j) % p), zi))
        detM_sq = _cyc_mul(p, detM, detM)

        # Prefactor: 2^n * det(M)^2 / (tau_p^n * 4*p)
        pref = _cyc_scale(_cyc_mul(p, detM_sq, tau_n_inv), Fraction(1 << n, 4 * p))
        checked_vals: list[list[int]] = []
        for x in xs:
            # Eq. (2.4) numerator: 2*c_p^2*tau*x + 2*c_p^2 + c_p^2*tau^2*x + c_p^2*tau + 2*p - 2*p*tau*x - p*tau + p*tau^2*x
            num = _cyc_zero(p)
            num = _cyc_add(num, _cyc_scale(_cyc_mul(p, cp2, tau), 2 * x + 1))
            num = _cyc_add(num, _cyc_scale(cp2, Fraction(2, 1)))
            num = _cyc_add(num, _cyc_scale(_cyc_mul(p, cp2, tau2), x))
            num = _cyc_add(num, _cyc_scalar(p, Fraction(2 * p, 1)))
            num = _cyc_sub(num, _cyc_scale(tau, Fraction(p, 1) * (2 * x + 1)))
            num = _cyc_add(num, _cyc_scale(tau2, Fraction(p, 1) * x))
            H_cyc = _cyc_mul(p, pref, num)

            # Verify H_cyc collapses to a PURE RATIONAL in Q and matches direct det(H(x))!
            det_H = _det_Q(_build_H_matrix(p, x))
            if H_cyc != _cyc_scalar(p, det_H):
                raise VerificationError(f"Eq. (2.4) cyclotomic collapse failed at x={x} for p={p}")
            checked_vals.append([det_H.numerator, det_H.denominator])

        return {
            "mode": "final_evaluation_and_unit_norms",
            "submode": submode,
            "prime_p": p,
            "x_count": len(xs),
            "H_values": checked_vals,
        }

    if submode == "real_quadratic_unit_and_class_number":
        # Verify exact Pell unit arithmetic eps_p^{h_p} = a_p + b_p*sqrt(p) and cross-check H(0), H(1) for p = 1 mod 4!
        entries_raw = _req_list(payload.get("prime_units"), "prime_units", 2, 12)
        seen_p: set[int] = set()
        direct_det_checked = 0
        for idx, er in enumerate(entries_raw):
            ed = _req_dict(er, f"prime_units[{idx}]")
            p = _req_int(ed.get("prime_p"), f"p[{idx}]", 5, 257)
            if not _is_prime(p) or p % 4 != 1:
                raise VerificationError(f"p={p} must be a prime congruent to 1 mod 4")
            if p in seen_p:
                raise VerificationError(f"Duplicate prime p={p}")
            seen_p.add(p)
            u0 = _parse_rat(ed.get("fund_u"), f"u0[{idx}]")
            v0 = _parse_rat(ed.get("fund_v"), f"v0[{idx}]")
            h_p = _req_int(ed.get("class_number_h"), f"h[{idx}]", 1, 15)
            if h_p % 2 != 1:
                raise VerificationError(f"Class number h_p={h_p} must be odd for prime p=1 mod 4")
            if u0 <= 0 or v0 <= 0 or u0 * u0 - p * v0 * v0 != -1:
                raise VerificationError(f"Fundamental unit norm N(eps_{p}) != -1")

            # Compute (u0 + v0*sqrt(p))^{h_p} exactly in Q(sqrt(p))
            ap, bp = Fraction(1, 1), Fraction(0, 1)
            for _ in range(h_p):
                ap, bp = ap * u0 + p * bp * v0, ap * v0 + bp * u0
            if ap * ap - p * bp * bp != -1:
                raise VerificationError(f"Power norm N(eps_{p}^{h_p}) != -1")

            exp_ap = _parse_rat(ed.get("a_p"), f"a_p[{idx}]")
            exp_bp = _parse_rat(ed.get("b_p"), f"b_p[{idx}]")
            if ap != exp_ap or bp != exp_bp:
                raise VerificationError(f"eps_p^h mismatch for p={p}: ({ap},{bp}) != ({exp_ap},{exp_bp})")

            # Cross-check H(0) and H(1) directly via exact Q determinant for p <= 41!
            if p <= 41:
                H0 = _det_Q(_build_H_matrix(p, Fraction(0, 1)))
                H1 = _det_Q(_build_H_matrix(p, Fraction(1, 1)))
                scale = Fraction(_legendre(2, p), 1) * Fraction(1 << ((p - 3) // 2), 1)
                if H0 != scale * (2 * bp - ap):
                    raise VerificationError(f"Eq. (2.6) H(0) mismatch for p={p}")
                if H1 != scale * ((p * bp - 2 * ap) + (2 * bp - ap)):
                    raise VerificationError(f"Eq. (2.6) H(1) mismatch for p={p}")
                direct_det_checked += 1

        return {
            "mode": "final_evaluation_and_unit_norms",
            "submode": submode,
            "primes_verified": len(seen_p),
            "direct_det_cross_checked": direct_det_checked,
        }

    raise VerificationError(f"Unknown Mode 3 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 4: chapman_and_sun_companion_families (Sec. 3 Chapman F(x) & Thm. 1.1(ii))
# ---------------------------------------------------------------------------

def _verify_mode4(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "chapman_determinant_M1":
        # Verify Sec. 3: tau_p^n * F(x) = 2^(n-1) * det(M_1)^2 * (2 + (tau_p*x + 1)*(M_1^{-1} u)^T (M_1^{-1} u))
        p = _req_int(payload.get("prime_p"), "prime_p", 5, 19)
        if not _is_prime(p):
            raise VerificationError(f"p={p} is not prime")
        x = _parse_rat(payload.get("x"), "x")
        n = (p - 1) // 2
        tau = _cyc_gauss_sum(p)

        # Direct determinant F(x) = det[x + ((i+j)/p)]_{1 <= i, j <= n}
        F_mat = [[x + Fraction(_legendre(i + j, p), 1) for j in range(1, n + 1)] for i in range(1, n + 1)]
        det_F = _det_Q(F_mat)

        # Exact M_1 = [zeta^{i * j^2}]_{1 <= i, j <= n} in Q[zeta_p]
        M1 = [[_cyc_zeta(p, (i * j * j) % p) for j in range(1, n + 1)] for i in range(1, n + 1)]
        one = _cyc_scalar(p, Fraction(1, 1))
        u = [list(one) for _ in range(n)]
        a_m1 = _cyc_solve(p, M1, u)
        alpha_m1 = _cyc_zero(p)
        for c in a_m1:
            alpha_m1 = _cyc_add(alpha_m1, _cyc_mul(p, c, c))

        # Exact det(M_1) = (prod_{j=1}^n zeta^{j^2}) * det(M) = 1 * det(M) since sum_{j=1}^n j^2 = 0 mod p for p > 3!
        detM1 = _cyc_scalar(p, Fraction(1, 1))
        for j in range(1, n + 1):
            detM1 = _cyc_mul(p, detM1, _cyc_zeta(p, (j * j) % p))
        for i in range(1, n + 1):
            zi = _cyc_zeta(p, (i * i) % p)
            for j in range(i + 1, n + 1):
                detM1 = _cyc_mul(p, detM1, _cyc_sub(_cyc_zeta(p, (j * j) % p), zi))
        detM1_sq = _cyc_mul(p, detM1, detM1)

        K = _cyc_add(_cyc_scale(tau, x), one)
        inner = _cyc_add(_cyc_scalar(p, Fraction(2, 1)), _cyc_mul(p, K, alpha_m1))
        rhs = _cyc_scale(_cyc_mul(p, detM1_sq, inner), Fraction(1 << (n - 1), 1))
        lhs = _cyc_scale(_cyc_pow(p, tau, n), det_F)
        if lhs != rhs:
            raise VerificationError(f"Sec. 3 Chapman identity failed for p={p}, x={x}")

        return {
            "mode": "chapman_and_sun_companion_families",
            "submode": submode,
            "prime_p": p,
            "det_F": [det_F.numerator, det_F.denominator],
            "sec3_identity_verified": True,
        }

    if submode == "sun_conjecture_part_ii_check":
        # Verify Theorem 1.1(ii) Eq. (1.4) (the i-j matrix of Liu-Sun-Wang [6]) via exact Q determinant!
        p = _req_int(payload.get("prime_p"), "prime_p", 5, 37)
        if not _is_prime(p):
            raise VerificationError(f"p={p} is not prime")
        x = _parse_rat(payload.get("x"), "x")
        y = _parse_rat(payload.get("y"), "y")
        z = _parse_rat(payload.get("z"), "z")
        w = _parse_rat(payload.get("w"), "w")
        n = (p - 1) // 2
        mat_minus = [
            [
                x
                + Fraction(_legendre(i - j, p), 1)
                + Fraction(_legendre(i, p), 1) * y
                + Fraction(_legendre(j, p), 1) * z
                + Fraction(_legendre(i * j, p), 1) * w
                for j in range(n)
            ]
            for i in range(n)
        ]
        det_minus = _det_Q(mat_minus)
        v = w * x - (y + 1) * (z + 1)

        if p % 4 == 1:
            ap = _parse_rat(payload.get("a_p"), "a_p")
            bp = _parse_rat(payload.get("b_p"), "b_p")
            if ap <= 0 or bp <= 0 or ap * ap - p * bp * bp != -1:
                raise VerificationError("Invalid (a_p, b_p) unit coordinates")
            leg2 = _legendre(2, p)
            exp_mult = 2 - leg2  # 1 if (2/p)=1, 3 if (2/p)=-1
            ap_prime, bp_prime = Fraction(1, 1), Fraction(0, 1)
            for _ in range(exp_mult):
                ap_prime, bp_prime = ap_prime * ap + p * bp_prime * bp, ap_prime * bp + bp_prime * ap
            expected = -ap_prime * x - Fraction(leg2, 1) * bp_prime * v
        else:
            expected = x

        if det_minus != expected:
            raise VerificationError(f"Theorem 1.1(ii) Eq. (1.4) failed for p={p}: {det_minus} != {expected}")

        return {
            "mode": "chapman_and_sun_companion_families",
            "submode": submode,
            "prime_p": p,
            "det_A_minus": [det_minus.numerator, det_minus.denominator],
        }

    raise VerificationError(f"Unknown Mode 4 submode: {submode}")


# ---------------------------------------------------------------------------
# Entry Points
# ---------------------------------------------------------------------------

def verify_certificate(cert: Any) -> dict[str, Any]:
    d = _req_dict(cert, "certificate")
    if d.get("schema_version") != SCHEMA_VERSION:
        raise VerificationError(f"Expected schema_version={SCHEMA_VERSION}, got {d.get('schema_version')}")
    _req_str(d.get("certificate_id"), "certificate_id")
    _req_str(d.get("paper_reference"), "paper_reference")
    mode = _req_str(d.get("mode"), "mode")
    payload = _req_dict(d.get("payload"), "payload")

    if mode == "matrix_reduction_and_det_lemma":
        res = _verify_mode1(payload)
    elif mode == "cyclotomic_vandermonde_and_forms":
        res = _verify_mode2(payload)
    elif mode == "final_evaluation_and_unit_norms":
        res = _verify_mode3(payload)
    elif mode == "chapman_and_sun_companion_families":
        res = _verify_mode4(payload)
    else:
        raise VerificationError(f"Unknown mode: {mode}")

    res["certificate_id"] = d["certificate_id"]
    res["status"] = "VERIFIED"
    return res


def verify_file(path: pathlib.Path | str) -> dict[str, Any]:
    p = pathlib.Path(path)
    if not p.is_file():
        raise VerificationError(f"Certificate path is not a readable file: {p}")
    if p.stat().st_size > MAX_JSON_BYTES:
        raise VerificationError(f"Certificate {p.name} exceeds MAX_JSON_BYTES={MAX_JSON_BYTES}")
    raw = p.read_bytes()
    if len(raw) > MAX_JSON_BYTES:
        raise VerificationError(f"Certificate {p.name} exceeds MAX_JSON_BYTES={MAX_JSON_BYTES}")
    try:
        data = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_no_dup_pairs,
            parse_constant=_reject_json_constant,
            parse_float=_reject_json_float,
        )
    except VerificationError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise VerificationError(f"Invalid JSON in {p.name}: {exc}") from exc
    return verify_certificate(data)


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if not args:
        print("Usage: python -m src.legendre_det_verifier <file-or-dir> [...]", file=sys.stderr)
        return 2
    files: list[pathlib.Path] = []
    for a in args:
        p = pathlib.Path(a)
        if p.is_dir():
            files.extend(sorted(p.glob("*.json")))
        else:
            files.append(p)
    if not files:
        print("No certificate files found.", file=sys.stderr)
        return 2
    verified = 0
    for f in files:
        res = verify_file(f)
        print(f"[VERIFIED] {f.name}: {res['mode']} ({res['submode']})")
        verified += 1
    print(f"Verified {verified}/{len(files)} certificates under {SCHEMA_VERSION}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
