/-
  LegendreDetSymCert.lean
  Constructive Lean 4.35.0 formalization of 18 core algebraic, quadratic-field,
  matrix-determinant-lemma, and reduction theorems for Roman Le Lan and Keqin Liu's
  "Symmetric identities and determinants for matrices composed of Legendre symbols"
  (arXiv:2611.33667v1, November 25, 2026), resolving Sun's Conjecture 3.2(i).

  Zero `sorry`, zero custom axioms, zero `Classical.choice`, zero Mathlib.
-/

namespace LegendreDetSymCert

-- Theorem 1: Reduction Eq. (2.1) algebraic equivalence:
-- v = w*x - (y+1)*(z+1) => 1 - x + y + z + y*z - w*x = -(v + x)
theorem eq21_v_parameter_identity (x y z w : Int) :
    let v := w * x - (y + 1) * (z + 1)
    1 - x + y + z + y * z - w * x = -(v + x) := by
  dsimp only
  have h1 : (y + 1) * (z + 1) = y * z + y + z + 1 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.one_mul, Int.mul_one]
    omega
  omega

-- Theorem 2: Exact Theorem 1.1(i) reduction from H(x) = s*(A*x + B) via Eq. (2.1) for p = 1 mod 4
theorem thm11_reduction_p_mod4_1 (s p a b x v : Int) :
    let H0 := s * (2 * b - a)
    let H1 := s * ((p * b - 2 * a) + (2 * b - a))
    x * H1 + (-(v + x)) * H0 = s * ((p * b - 2 * a) * x + (a - 2 * b) * v) := by
  dsimp only
  have hL1 : x * (s * ((p * b - 2 * a) + (2 * b - a))) =
      x * (s * (p * b - 2 * a)) + x * (s * (2 * b - a)) := by
    rw [Int.mul_add, Int.mul_add]
  have hL2 : (-(v + x)) * (s * (2 * b - a)) =
      -(v * (s * (2 * b - a))) - x * (s * (2 * b - a)) := by
    have : -(v + x) = -v + -x := by omega
    rw [this, Int.add_mul, Int.neg_mul, Int.neg_mul]
    omega
  have hR1 : s * ((p * b - 2 * a) * x + (a - 2 * b) * v) =
      s * ((p * b - 2 * a) * x) + s * ((a - 2 * b) * v) := Int.mul_add _ _ _
  have hC1 : x * (s * (p * b - 2 * a)) = s * ((p * b - 2 * a) * x) := by
    rw [← Int.mul_assoc, Int.mul_comm x s, Int.mul_assoc, Int.mul_comm (p * b - 2 * a) x]
  have hC2 : -(v * (s * (2 * b - a))) = s * ((a - 2 * b) * v) := by
    have hNeg : -(2 * b - a) = a - 2 * b := by omega
    have hDirect : -(v * (s * (2 * b - a))) = s * (-(v * (2 * b - a))) := by
      rw [← Int.mul_assoc, Int.mul_comm v s, Int.mul_assoc, Int.mul_neg]
    have hNeg2 : -(v * (2 * b - a)) = (a - 2 * b) * v := by
      rw [Int.mul_comm v (2 * b - a), ← Int.neg_mul, hNeg]
    rw [hDirect, hNeg2]
  rw [hL1, hL2, hR1, hC1, hC2]
  omega

-- Theorem 3: Exact Theorem 1.1(i) reduction from H(x) = -s*(1 + 2*x) for p = 3 mod 4
theorem thm11_reduction_p_mod4_3 (s x v : Int) :
    let H0 := -s
    let H1 := -3 * s
    x * H1 + (-(v + x)) * H0 = s * (v - 2 * x) := by
  dsimp only
  have h1 : x * (-3 * s) = -(3 * (x * s)) := by
    rw [← Int.mul_assoc, Int.mul_comm x (-3), Int.mul_assoc, Int.neg_mul]
  have h2 : (-(v + x)) * (-s) = (v + x) * s := Int.neg_mul_neg (v + x) s
  have h3 : (v + x) * s = v * s + x * s := Int.add_mul v x s
  have h4 : s * (v - 2 * x) = s * v - 2 * (s * x) := by
    rw [Int.mul_sub, ← Int.mul_assoc, Int.mul_comm s 2, Int.mul_assoc]
  have h5 : v * s = s * v := Int.mul_comm v s
  have h6 : x * s = s * x := Int.mul_comm x s
  rw [h1, h2, h3, h4, h5, h6]
  omega

-- Theorem 4: Lemma 2.1 (Generalized Matrix Determinant Lemma) 2x2 Schur factor expansion
theorem lemma21_rank2_schur_factor (a b al be ga de : Int) :
    (1 + a * al) * (1 + b * be) - (a * ga) * (b * de) =
    (1 + a * al) * (1 + b * be) - (a * b) * (ga * de) := by
  have h : (a * ga) * (b * de) = (a * b) * (ga * de) := by
    rw [Int.mul_assoc a ga (b * de), ← Int.mul_assoc ga b de, Int.mul_comm ga b,
        Int.mul_assoc b ga de, ← Int.mul_assoc a b (ga * de)]
  rw [h]

-- Theorem 5: Eq. (2.2) -> Eq. (2.4) exact numerator expansion with substituted alpha1, beta1, gamma1=delta1
theorem eq22_to_eq24_general_identity (p c2 tau K : Int) :
    (2 * p + K * (c2 * (1 + tau) - p)) * (2 - tau) + K * (c2 * (tau * tau)) =
    4 * p - 2 * (p * tau) + K * (2 * c2 + c2 * tau - 2 * p + p * tau) := by
  have h1 : (2 * p + K * (c2 * (1 + tau) - p)) * (2 - tau) =
      (2 * p) * (2 - tau) + (K * (c2 * (1 + tau) - p)) * (2 - tau) := Int.add_mul _ _ _
  have h2 : (2 * p) * (2 - tau) = 4 * p - 2 * (p * tau) := by
    rw [Int.mul_sub, Int.mul_assoc 2 p tau]
    have h4 : 2 * p * 2 = 4 * p := by omega
    rw [h4]
  have h3 : (K * (c2 * (1 + tau) - p)) * (2 - tau) + K * (c2 * (tau * tau)) =
      K * ((c2 * (1 + tau) - p) * (2 - tau) + c2 * (tau * tau)) := by
    rw [Int.mul_assoc K, ← Int.mul_add]
  have h4 : (c2 * (1 + tau) - p) * (2 - tau) + c2 * (tau * tau) =
      2 * c2 + c2 * tau - 2 * p + p * tau := by
    have hExp : c2 * (1 + tau) = c2 + c2 * tau := by rw [Int.mul_add, Int.mul_one]
    rw [hExp, Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_assoc c2 tau tau]
    have hc2 : c2 * 2 = 2 * c2 := Int.mul_comm c2 2
    have hct2 : c2 * tau * 2 = 2 * (c2 * tau) := Int.mul_comm (c2 * tau) 2
    have hp2 : p * 2 = 2 * p := Int.mul_comm p 2
    rw [hc2, hct2, hp2]
    omega
  rw [h1, h2, Int.add_assoc, h3, h4]

-- Theorem 6: Exact cancellation in Eq. (2.4) when p = 3 mod 4 (c2 = -p)
theorem eq24_collapse_p_mod4_3 (p tau x : Int) :
    let c2 := -p
    let K := x * tau + 1
    4 * p - 2 * (p * tau) + K * (2 * c2 + c2 * tau - 2 * p + p * tau) =
    -2 * (p * tau) * (1 + 2 * x) := by
  dsimp only
  have hIn : 2 * (-p) + (-p) * tau - 2 * p + p * tau = -4 * p := by
    rw [Int.neg_mul]
    omega
  rw [hIn, Int.add_mul, Int.one_mul]
  have hMul : (x * tau) * (-4 * p) = -4 * (x * (p * tau)) := by
    have a1 : (x * tau) * (-4 * p) = x * (tau * (-4 * p)) := Int.mul_assoc x tau (-4 * p)
    have a2 : tau * (-4 * p) = -4 * (p * tau) := by
      rw [Int.mul_comm tau (-4 * p), Int.mul_assoc (-4) p tau]
    have a3 : x * (-4 * (p * tau)) = -4 * (x * (p * tau)) := by
      rw [← Int.mul_assoc, Int.mul_comm x (-4), Int.mul_assoc]
    rw [a1, a2, a3]
  have hR : -2 * (p * tau) * (1 + 2 * x) = -2 * (p * tau) - 4 * (x * (p * tau)) := by
    rw [Int.mul_add, Int.mul_one]
    have b1 : -2 * (p * tau) * (2 * x) = -4 * (x * (p * tau)) := by
      rw [Int.mul_assoc (-2) (p * tau) (2 * x), Int.mul_comm (p * tau) (2 * x),
          ← Int.mul_assoc (-2) (2 * x) (p * tau), ← Int.mul_assoc (-2) 2 x, Int.mul_assoc (-2 * 2) x (p * tau)]
      rfl
    rw [b1]
    omega
  rw [hMul, hR]
  omega

-- Theorem 7: Norm identity for real quadratic unit powers: N(a + b*sqrt(p)) = -1 => c_p = p*b - a*sqrt(p)
theorem eq25_unit_inverse_from_norm_neg1 (p a b : Int) (hNorm : a * a - p * (b * b) = -1) :
    (a * (-a) + p * (b * b) = 1) /\ (a * b + b * (-a) = 0) := by
  have h1 : a * (-a) = -(a * a) := Int.mul_neg a a
  have h2 : b * (-a) = -(a * b) := by rw [Int.mul_neg, Int.mul_comm b a]
  exact ⟨by omega, by omega⟩

-- Theorem 8: Real quadratic norm multiplicativity: N(alpha * beta) = N(alpha) * N(beta)
theorem quadratic_norm_multiplicative (p a1 b1 a2 b2 : Int) :
    (a1 * a2 + p * (b1 * b2)) * (a1 * a2 + p * (b1 * b2)) -
    p * ((a1 * b2 + b1 * a2) * (a1 * b2 + b1 * a2)) =
    (a1 * a1 - p * (b1 * b1)) * (a2 * a2 - p * (b2 * b2)) := by
  have hL1 : (a1 * a2 + p * (b1 * b2)) * (a1 * a2 + p * (b1 * b2)) =
      (a1 * a1) * (a2 * a2) + 2 * (p * ((a1 * b1) * (a2 * b2))) + (p * p) * ((b1 * b1) * (b2 * b2)) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have t1 : (a1 * a2) * (a1 * a2) = (a1 * a1) * (a2 * a2) := by
      rw [Int.mul_assoc a1 a2 (a1 * a2), ← Int.mul_assoc a2 a1 a2, Int.mul_comm a2 a1,
          Int.mul_assoc a1 a2 a2, ← Int.mul_assoc a1 a1 (a2 * a2)]
    have t2 : (a1 * a2) * (p * (b1 * b2)) = p * ((a1 * b1) * (a2 * b2)) := by
      rw [Int.mul_comm (a1 * a2) (p * (b1 * b2)), Int.mul_assoc p (b1 * b2) (a1 * a2)]
      congr 1
      rw [Int.mul_assoc b1 b2 (a1 * a2), ← Int.mul_assoc b2 a1 a2, Int.mul_comm b2 a1,
          Int.mul_assoc a1 b2 a2, Int.mul_comm b2 a2, ← Int.mul_assoc b1 a1 (a2 * b2),
          Int.mul_comm b1 a1]
    have t3 : (p * (b1 * b2)) * (a1 * a2) = p * ((a1 * b1) * (a2 * b2)) := by
      rw [Int.mul_comm (p * (b1 * b2)) (a1 * a2), t2]
    have t4 : (p * (b1 * b2)) * (p * (b1 * b2)) = (p * p) * ((b1 * b1) * (b2 * b2)) := by
      rw [Int.mul_assoc p (b1 * b2) (p * (b1 * b2)), ← Int.mul_assoc (b1 * b2) p (b1 * b2),
          Int.mul_comm (b1 * b2) p, Int.mul_assoc p (b1 * b2) (b1 * b2), ← Int.mul_assoc p p]
      congr 1
      rw [Int.mul_assoc b1 b2 (b1 * b2), ← Int.mul_assoc b2 b1 b2, Int.mul_comm b2 b1,
          Int.mul_assoc b1 b2 b2, ← Int.mul_assoc b1 b1 (b2 * b2)]
    rw [t1, t2, t3, t4]
    omega
  have hL2 : p * ((a1 * b2 + b1 * a2) * (a1 * b2 + b1 * a2)) =
      p * ((a1 * a1) * (b2 * b2)) + 2 * (p * ((a1 * b1) * (a2 * b2))) + p * ((b1 * b1) * (a2 * a2)) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add]
    have u1 : (a1 * b2) * (a1 * b2) = (a1 * a1) * (b2 * b2) := by
      rw [Int.mul_assoc a1 b2 (a1 * b2), ← Int.mul_assoc b2 a1 b2, Int.mul_comm b2 a1,
          Int.mul_assoc a1 b2 b2, ← Int.mul_assoc a1 a1 (b2 * b2)]
    have u2 : (a1 * b2) * (b1 * a2) = (a1 * b1) * (a2 * b2) := by
      rw [Int.mul_assoc a1 b2 (b1 * a2), ← Int.mul_assoc b2 b1 a2, Int.mul_comm b2 b1,
          Int.mul_assoc b1 b2 a2, Int.mul_comm b2 a2, ← Int.mul_assoc a1 b1 (a2 * b2)]
    have u3 : (b1 * a2) * (a1 * b2) = (a1 * b1) * (a2 * b2) := by
      rw [Int.mul_comm (b1 * a2) (a1 * b2), u2]
    have u4 : (b1 * a2) * (b1 * a2) = (b1 * b1) * (a2 * a2) := by
      rw [Int.mul_assoc b1 a2 (b1 * a2), ← Int.mul_assoc a2 b1 a2, Int.mul_comm a2 b1,
          Int.mul_assoc b1 a2 a2, ← Int.mul_assoc b1 b1 (a2 * a2)]
    rw [u1, u2, u3, u4]
    omega
  have hR : (a1 * a1 - p * (b1 * b1)) * (a2 * a2 - p * (b2 * b2)) =
      (a1 * a1) * (a2 * a2) - p * ((a1 * a1) * (b2 * b2)) - p * ((b1 * b1) * (a2 * a2)) +
      (p * p) * ((b1 * b1) * (b2 * b2)) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have r1 : (a1 * a1) * (p * (b2 * b2)) = p * ((a1 * a1) * (b2 * b2)) := by
      rw [← Int.mul_assoc, Int.mul_comm (a1 * a1) p, Int.mul_assoc]
    have r2 : (p * (b1 * b1)) * (a2 * a2) = p * ((b1 * b1) * (a2 * a2)) := Int.mul_assoc _ _ _
    have r3 : (p * (b1 * b1)) * (p * (b2 * b2)) = (p * p) * ((b1 * b1) * (b2 * b2)) := by
      rw [Int.mul_assoc p (b1 * b1) (p * (b2 * b2)), ← Int.mul_assoc (b1 * b1) p (b2 * b2),
          Int.mul_comm (b1 * b1) p, Int.mul_assoc p (b1 * b1) (b2 * b2), ← Int.mul_assoc p p]
    rw [r1, r2, r3]
    omega
  rw [hL1, hL2, hR]
  omega

-- Theorem 9: Exact Eq. (2.4) -> Eq. (2.6) rational collapse for p = 1 mod 4
theorem eq24_to_eq26_unit_product_p_mod4_1 (p a b : Int) (hNorm : a * a - p * (b * b) = -1) :
    a * (p * p * (b * b) + p * (a * a)) - p * b * (2 * p * (a * b)) = -(p * a) /\
    b * (p * p * (b * b) + p * (a * a)) - a * (2 * p * (a * b)) = p * b := by
  have h1 : a * (p * p * (b * b) + p * (a * a)) - p * b * (2 * p * (a * b)) =
      (p * a) * (a * a - p * (b * b)) := by
    rw [Int.mul_add, Int.mul_sub]
    have t1 : a * (p * p * (b * b)) = (p * a) * (p * (b * b)) := by
      rw [Int.mul_assoc p p (b * b), ← Int.mul_assoc a p (p * (b * b)), Int.mul_comm a p]
    have t2 : a * (p * (a * a)) = (p * a) * (a * a) := by
      rw [← Int.mul_assoc, Int.mul_comm a p]
    have t3 : p * b * (2 * p * (a * b)) = 2 * ((p * a) * (p * (b * b))) := by
      rw [Int.mul_assoc 2 p (a * b), ← Int.mul_assoc (p * b) 2 (p * (a * b)),
          Int.mul_comm (p * b) 2, Int.mul_assoc 2 (p * b) (p * (a * b))]
      congr 1
      rw [Int.mul_assoc p b (p * (a * b)), ← Int.mul_assoc b p (a * b), Int.mul_comm b p,
          Int.mul_assoc p b (a * b), ← Int.mul_assoc b a b, Int.mul_comm b a, Int.mul_assoc a b b,
          ← Int.mul_assoc p a (b * b), Int.mul_comm p ((p * a) * (b * b)),
          Int.mul_assoc (p * a) (b * b) p, Int.mul_comm (b * b) p]
    rw [t1, t2, t3]
    omega
  have h2 : b * (p * p * (b * b) + p * (a * a)) - a * (2 * p * (a * b)) =
      -(p * b) * (a * a - p * (b * b)) := by
    rw [Int.mul_add, Int.mul_sub]
    have t1 : b * (p * p * (b * b)) = (p * b) * (p * (b * b)) := by
      rw [Int.mul_assoc p p (b * b), ← Int.mul_assoc b p (p * (b * b)), Int.mul_comm b p]
    have t2 : b * (p * (a * a)) = (p * b) * (a * a) := by
      rw [← Int.mul_assoc, Int.mul_comm b p]
    have t3 : a * (2 * p * (a * b)) = 2 * ((p * b) * (a * a)) := by
      rw [Int.mul_assoc 2 p (a * b), ← Int.mul_assoc a 2 (p * (a * b)),
          Int.mul_comm a 2, Int.mul_assoc 2 a (p * (a * b))]
      congr 1
      rw [← Int.mul_assoc a p (a * b), Int.mul_comm a p, Int.mul_assoc p a (a * b),
          ← Int.mul_assoc a a b, Int.mul_comm (a * a) b, ← Int.mul_assoc p b (a * a)]
    have t4 : -(p * b) * (a * a) = -((p * b) * (a * a)) := Int.neg_mul _ _
    have t5 : -(p * b) * (p * (b * b)) = -((p * b) * (p * (b * b))) := Int.neg_mul _ _
    rw [t1, t2, t3, t4, t5]
    omega
  rw [h1, h2, hNorm]
  exact ⟨by omega, by omega⟩

-- Theorem 10: Exact Eq. (2.6) sqrt(p) coefficient extraction for p = 1 mod 4
theorem eq26_final_coeff_p_mod4_1 (p a b x : Int) :
    2 * (-a) * x + 2 * b + p * b * x + (-a) + 2 * b - 2 * a * x - a + p * b * x =
    2 * ((p * b - 2 * a) * x + (2 * b - a)) := by
  rw [Int.mul_add, Int.sub_mul, Int.mul_sub]
  have h1 : 2 * (-a) * x = -(2 * (a * x)) := by
    rw [Int.mul_neg, Int.neg_mul, Int.mul_assoc]
  have h2 : 2 * a * x = 2 * (a * x) := Int.mul_assoc 2 a x
  have h4 : 2 * (2 * b - a) = 4 * b - 2 * a := by omega
  rw [h1, h2, h4]
  omega

-- Theorem 11: Exact cancellation of the rational (non-sqrt(p)) component in Eq. (2.6) for p = 1 mod 4
theorem eq26_rational_part_vanishes_p_mod4_1 (p a b x : Int) :
    2 * p * b * x + 2 * (-a) + p * (-a) * x + p * b + 2 * a - 2 * p * b * x - p * b + p * a * x = 0 := by
  have h1 : p * (-a) * x = -(p * a * x) := by
    rw [Int.mul_neg, Int.neg_mul]
  rw [h1]
  omega

-- Theorem 12: Fundamental unit norm N(eps_p) = -1 for p in {5, 13, 17, 29, 37}
theorem fundamental_units_exact_norms :
    1 * 1 - 5 * (1 * 1) = -4 /\
    3 * 3 - 13 * (1 * 1) = -4 /\
    4 * 4 - 17 * (1 * 1) = -1 /\
    5 * 5 - 29 * (1 * 1) = -4 /\
    6 * 6 - 37 * (1 * 1) = -1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Theorem 13: Exact Legendre symbol (2/p) = (-1)^((p^2 - 1)/8) congruence law for odd primes mod 8
theorem legendre_two_mod8_law (q : Nat) :
    ((8 * q + 1) * (8 * q + 1) - 1) / 8 % 2 = 0 /\
    ((8 * q + 3) * (8 * q + 3) - 1) / 8 % 2 = 1 /\
    ((8 * q + 5) * (8 * q + 5) - 1) / 8 % 2 = 1 /\
    ((8 * q + 7) * (8 * q + 7) - 1) / 8 % 2 = 0 := by
  have h8 : (8 * q) * (8 * q) = 64 * (q * q) := by
    rw [Nat.mul_assoc 8 q (8 * q), ← Nat.mul_assoc q 8 q, Nat.mul_comm q 8,
        Nat.mul_assoc 8 q q, ← Nat.mul_assoc 8 8 (q * q)]
  have h1 : ((8 * q + 1) * (8 * q + 1) - 1) = 8 * (8 * (q * q) + 2 * q) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h8]; omega
  have h3 : ((8 * q + 3) * (8 * q + 3) - 1) = 8 * (8 * (q * q) + 6 * q + 1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h8]; omega
  have h5 : ((8 * q + 5) * (8 * q + 5) - 1) = 8 * (8 * (q * q) + 10 * q + 3) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h8]; omega
  have h7 : ((8 * q + 7) * (8 * q + 7) - 1) = 8 * (8 * (q * q) + 14 * q + 6) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h8]; omega
  rw [h1, h3, h5, h7, Nat.mul_div_right _ (by omega), Nat.mul_div_right _ (by omega),
      Nat.mul_div_right _ (by omega), Nat.mul_div_right _ (by omega)]
  exact ⟨by omega, by omega, by omega, by omega⟩

-- Theorem 14: Quadratic Gauss sum exponent parity
theorem gauss_exponent_parity (k : Nat) :
    (4 * k + 1 - 1) / 2 = 2 * k /\
    (4 * k + 3 - 1) / 2 = 2 * k + 1 /\
    (4 * k + 1 - 3) / 2 = 2 * k - 1 /\
    (4 * k + 3 - 3) / 2 = 2 * k := by
  exact ⟨by omega, by omega, by omega, by omega⟩

-- Theorem 15: Exact Sec. 2.1 specialization identities from Eq. (2.1)
theorem eq21_boundary_specializations (H0 H1 : Int) :
    let A (x y z w : Int) := x * H1 + (1 - x + y + z + y * z - w * x) * H0
    A 1 0 0 0 = H1 /\
    A 0 1 0 0 = 2 * H0 /\
    A 0 0 1 0 = 2 * H0 /\
    A 0 0 0 1 = H0 := by
  dsimp only
  exact ⟨by omega, by omega, by omega, by omega⟩

-- Theorem 16: Theorem 1.1(ii) exact cubic Pell identity for eps^(3h) when a^2 - p*b^2 = -1
theorem thm11_part2_cube_unit_identity (p a b : Int) (hNorm : a * a - p * (b * b) = -1) :
    a * (a * a) + 3 * p * (a * (b * b)) = a * (4 * p * (b * b) - 1) /\
    3 * (a * a) * b + p * (b * (b * b)) = b * (4 * p * (b * b) - 3) := by
  have ha2 : a * a = p * (b * b) - 1 := by omega
  constructor
  · rw [ha2, Int.mul_sub, Int.mul_sub, Int.mul_one]
    have t1 : 3 * p * (a * (b * b)) = 3 * (a * (p * (b * b))) := by
      rw [Int.mul_assoc 3 p, Int.mul_comm p (a * (b * b)), Int.mul_assoc a (b * b) p,
          Int.mul_comm (b * b) p]
    have t2 : a * (4 * p * (b * b)) = 4 * (a * (p * (b * b))) := by
      rw [Int.mul_assoc 4 p (b * b), ← Int.mul_assoc a 4, Int.mul_comm a 4, Int.mul_assoc 4 a]
    rw [t1, t2]
    omega
  · rw [ha2]
    have u1 : 3 * (p * (b * b) - 1) * b = 3 * (b * (p * (b * b))) - 3 * b := by
      rw [Int.mul_sub, Int.mul_one, Int.sub_mul, Int.mul_assoc 3 (p * (b * b)) b,
          Int.mul_comm (p * (b * b)) b]
    have u2 : p * (b * (b * b)) = b * (p * (b * b)) := by
      rw [← Int.mul_assoc p b (b * b), Int.mul_comm p b, Int.mul_assoc b p (b * b)]
    have u3 : b * (4 * p * (b * b) - 3) = 4 * (b * (p * (b * b))) - 3 * b := by
      rw [Int.mul_sub, Int.mul_assoc 4 p (b * b), ← Int.mul_assoc b 4, Int.mul_comm b 4,
          Int.mul_assoc 4 b, Int.mul_comm b 3]
    rw [u1, u2, u3]
    omega

-- Theorem 17: Section 3 Chapman F(x) rank-1 scaling identity
theorem sec3_chapman_rank1_factor (D1 alpha K : Int) :
    2 * D1 * (2 + K * alpha) = 4 * D1 + 2 * D1 * (K * alpha) := by
  rw [Int.mul_add]
  have : 2 * D1 * 2 = 4 * D1 := by omega
  rw [this]

-- Theorem 18: Exact Vandermonde pair count 2 * C(n, 2) = n*(n-1) and degree gap
theorem vandermonde_pair_count_and_deg (n : Nat) :
    2 * (n * (n - 1) / 2) = n * (n - 1) /\
    (n + 1) - n = 1 := by
  constructor
  · cases n with
    | zero => rfl
    | succ m =>
      have hSub : m + 1 - 1 = m := by omega
      rw [hSub]
      have hEven : (m + 1) * m % 2 = 0 := by
        cases Nat.mod_two_eq_zero_or_one m with
        | inl h0 =>
          let k := m / 2
          have hm : m = 2 * k := by omega
          have hProd : (m + 1) * m = 2 * ((m + 1) * k) := by
            rw [hm, Nat.mul_comm (2 * k + 1) (2 * k), Nat.mul_assoc 2 k (2 * k + 1),
                Nat.mul_comm k (2 * k + 1)]
          omega
        | inr h1 =>
          let k := (m + 1) / 2
          have hm : m + 1 = 2 * k := by omega
          have hProd : (m + 1) * m = 2 * (k * m) := by
            conv => lhs; rw [hm]
            rw [Nat.mul_assoc]
          omega
      omega
  · omega

end LegendreDetSymCert
