# Exact Cyclotomic and Constructive Lean 4 Certificates for Symmetric Identities and Determinants of Legendre-Symbol Matrices

Independent companion verification artifact (`LEGENDRE-DET-SYM-CERT-1.0`) for Roman Le Lan and Keqin Liu's preprint *"Symmetric identities and determinants for matrices composed of Legendre symbols"* (`arXiv:2611.33667v1`, November 25, 2026), resolving Zhi-Wei Sun's Conjecture 3.2(i).

## Contents
- `lean/LegendreDetSymCert.lean`: 18 constructive Lean 4.35.0 theorems (0 `sorry`, 0 custom axioms, 0 `Classical.choice`, 0 Mathlib) formalizing the Eq. (2.1) parameter reduction, Lemma 2.1 Schur rank-2 factorization, Eq. (2.2) to Eq. (2.4) cyclotomic numerator expansion, Eq. (2.4) to Eq. (2.6) exact rational collapse for both $p \equiv 1, 3 \pmod 4$, quadratic-field norm multiplicativity, fundamental unit norms, cubic Pell powers for Part (ii), and Chapman's rank-1 scaling identity.
- `src/legendre_det_verifier.py`: Strictly zero-floating-point Python verifier performing exact rational and exact cyclotomic field arithmetic in $\mathbb{Q}[\zeta_p] \cong \mathbb{Q}[X]/(\Phi_p(X))$ across four verification modes (eight submodes).
- `certificates/C01..C16`: 16 canonical JSON certificates spanning primes $p \in [5, 229]$ (including non-trivial class numbers $h_{-23}=3$ and $h_{229}=3$).
- `tests/test_verifier.py`: Unit, adversarial forgery, security, and zero-float AST audit tests.
- `paper/main.pdf`: 4-page companion verification manuscript.

## Quick Verification
```bash
cd lean && lake build
cd ..
python -m src.legendre_det_verifier certificates
pytest -q
```

## Licensing & Attribution
Code, Lean 4 formalization, and JSON certificates: MIT License. Manuscript and figures: CC-BY-4.0. All primary mathematical theorems belong to Roman Le Lan and Keqin Liu (`arXiv:2611.33667v1`).
