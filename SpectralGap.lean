/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!

# A spectral gap gives exponential decay of the connected correlation

## i. Overview

For a symmetric matrix `T` (a transfer matrix) with eigenvalues `μ_j`, `x ⬝ Tᵏ x = ∑_j μ_jᵏ c_j²`
with `c_j = ⟨e_j, x⟩`. If the vacuum `j₀` is separated from the rest, `0 ≤ μ_j ≤ λ₁ < μ_{j₀}`
for `j ≠ j₀`, then the connected part `x ⬝ Tᵏ x - μ_{j₀}ᵏ c_{j₀}²` lies in `[0, λ₁ᵏ ‖x_⊥‖²]`:
it decays as `exp (-Δ k)` relative to `μ_{j₀}ᵏ`, with the gap `Δ = log (μ_{j₀} / λ₁)`.

This is the Hilbert space half of the passage from correlations to a mass gap; it says nothing about
which `T` has such a gap.

## ii. Key results

- `SpectralGap.quad_pow` : `x ⬝ Tᵏ x = ∑_j μ_jᵏ c_j²`.
- `SpectralGap.connected_le` : the connected part is at most `λ₁ᵏ (‖x‖² - c_{j₀}²)`.
- `SpectralGap.connected_nonneg` : and it is nonnegative.

## iii. Table of contents

- A. The spectral expansion
- B. The gap

## iv. References

-/

open Matrix Finset

namespace SpectralGap

variable {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}

/-! ## A. The spectral expansion -/

/-- The coefficient of a vector `x` on the `j`-th eigenvector of `T`. -/
noncomputable def coeff (hT : T.IsHermitian) (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (hT.eigenvectorBasis j) i * x i

lemma pow_mulVec_eigen (hT : T.IsHermitian) (j : Fin n) (k : ℕ) :
    (T ^ k) *ᵥ (hT.eigenvectorBasis j) = (hT.eigenvalues j) ^ k • (hT.eigenvectorBasis j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hT.mulVec_eigenvectorBasis, Matrix.mulVec_smul, ih,
      smul_smul, pow_succ]
    ring_nf

/-- A vector is the sum of its components on the eigenvectors. -/
lemma sum_coeff_smul (hT : T.IsHermitian) (x : Fin n → ℝ) :
    ∑ j, coeff hT j x • (hT.eigenvectorBasis j : Fin n → ℝ) = x := by
  have h := (hT.eigenvectorBasis).sum_repr' (WithLp.toLp 2 x)
  have h2 := congrArg WithLp.ofLp h
  ext i
  have := congrFun h2 i
  simpa [coeff, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using this

/-- **The spectral expansion**: `x ⬝ Tᵏ x = ∑_j μ_jᵏ c_j²`. -/
theorem quad_pow (hT : T.IsHermitian) (k : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((T ^ k) *ᵥ x) = ∑ j, hT.eigenvalues j ^ k * coeff hT j x ^ 2 := by
  have hx := sum_coeff_smul hT x
  have h1 : (T ^ k) *ᵥ x = ∑ j, (coeff hT j x * hT.eigenvalues j ^ k) •
      (hT.eigenvectorBasis j : Fin n → ℝ) := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, pow_mulVec_eigen, smul_smul]
  rw [h1, dotProduct_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  have : x ⬝ᵥ (hT.eigenvectorBasis j : Fin n → ℝ) = coeff hT j x := by
    simp only [coeff, dotProduct]
    exact sum_congr rfl fun i _ => mul_comm _ _
  rw [this]
  ring

/-- Parseval: `∑_j c_j² = x ⬝ x`. -/
lemma sum_coeff_sq (hT : T.IsHermitian) (x : Fin n → ℝ) :
    ∑ j, coeff hT j x ^ 2 = x ⬝ᵥ x := by
  have := quad_pow hT 0 x
  simpa using this.symm

/-! ## B. The gap -/

/-- **The connected part is between `0` and `λ₁ᵏ ‖x_⊥‖²`**: if every eigenvalue other than the
vacuum `i₀` lies in `[0, λ₁]`, then
`0 ≤ x ⬝ Tᵏ x - μ_{i₀}ᵏ c_{i₀}² ≤ λ₁ᵏ (x ⬝ x - c_{i₀}²)`. -/
theorem connected_bounds (hT : T.IsHermitian) (i0 : Fin n) {l1 : ℝ}
    (hlow : ∀ j, j ≠ i0 → 0 ≤ hT.eigenvalues j ∧ hT.eigenvalues j ≤ l1) (k : ℕ)
    (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ ((T ^ k) *ᵥ x) - hT.eigenvalues i0 ^ k * coeff hT i0 x ^ 2 ∧
      x ⬝ᵥ ((T ^ k) *ᵥ x) - hT.eigenvalues i0 ^ k * coeff hT i0 x ^ 2 ≤
        l1 ^ k * (x ⬝ᵥ x - coeff hT i0 x ^ 2) := by
  rw [quad_pow, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), add_sub_cancel_left]
  have hpar : x ⬝ᵥ x - coeff hT i0 x ^ 2 = ∑ j ∈ univ.erase i0, coeff hT j x ^ 2 := by
    rw [← sum_coeff_sq hT x, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    ring
  rw [hpar, Finset.mul_sum]
  constructor
  · exact sum_nonneg fun j hj =>
      mul_nonneg (pow_nonneg (hlow j (Finset.ne_of_mem_erase hj)).1 _) (sq_nonneg _)
  · refine sum_le_sum fun j hj => ?_
    have h := hlow j (Finset.ne_of_mem_erase hj)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.1 h.2 k) (sq_nonneg _)

/-- **The connected correlation decays exponentially with the gap**: with `0 < λ₁ < μ_{i₀}` and
`Δ = log (μ_{i₀} / λ₁)`, the connected part of `x ⬝ Tᵏ x`, relative to `μ_{i₀}ᵏ`, is at most
`exp (-Δ k) ‖x‖²`. -/
theorem connected_le_exp (hT : T.IsHermitian) (i0 : Fin n) {l1 : ℝ} (hl1 : 0 < l1)
    (hgap : l1 < hT.eigenvalues i0)
    (hlow : ∀ j, j ≠ i0 → 0 ≤ hT.eigenvalues j ∧ hT.eigenvalues j ≤ l1) (k : ℕ)
    (x : Fin n → ℝ) :
    (x ⬝ᵥ ((T ^ k) *ᵥ x) - hT.eigenvalues i0 ^ k * coeff hT i0 x ^ 2) / hT.eigenvalues i0 ^ k ≤
      Real.exp (-(Real.log (hT.eigenvalues i0 / l1) * k)) * (x ⬝ᵥ x) := by
  have hμ : 0 < hT.eigenvalues i0 := hl1.trans hgap
  have h := (connected_bounds hT i0 hlow k x).2
  have hxx : x ⬝ᵥ x - coeff hT i0 x ^ 2 ≤ x ⬝ᵥ x := by nlinarith [sq_nonneg (coeff hT i0 x)]
  have hpow : 0 < hT.eigenvalues i0 ^ k := pow_pos hμ k
  rw [div_le_iff₀ hpow]
  have hexp : Real.exp (-(Real.log (hT.eigenvalues i0 / l1) * k)) =
      (l1 / hT.eigenvalues i0) ^ k := by
    have h' : -(Real.log (hT.eigenvalues i0 / l1) * k) = (k : ℝ) * Real.log (l1 / hT.eigenvalues i0) := by
      rw [Real.log_div hl1.ne' hμ.ne', Real.log_div hμ.ne' hl1.ne']
      ring
    rw [h', Real.exp_nat_mul, Real.exp_log (div_pos hl1 hμ)]
  rw [hexp]
  calc _ ≤ l1 ^ k * (x ⬝ᵥ x - coeff hT i0 x ^ 2) := h
    _ ≤ l1 ^ k * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left hxx (pow_nonneg hl1.le _)
    _ = (l1 / hT.eigenvalues i0) ^ k * (x ⬝ᵥ x) * hT.eigenvalues i0 ^ k := by
        rw [div_pow]; field_simp

end SpectralGap
