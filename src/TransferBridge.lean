/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava Hernandez
-/
import SpectralGap
import SurgeryGapClosure

/-!
# Bridge between the Transfer Matrix and the Wilson Loop Area Law

This file proves the transfer matrix spectral bound derived from the Wilson loop area law.

## Main results

- `single_le_quad_pow`: for a PSD Hermitian matrix, each eigenvalue term `μ_j^k c_j²` is
  bounded above by `x ⬝ T^k x`.
- `transfer_eigenvalue_le`: if `x ⬝ T^k x ≤ C · α^k · μ_0^k ‖x‖²`, then the eigenvalue
  `μ_j` coupled to `x` (`c_j ≠ 0`) satisfies `μ_j ≤ α · μ_0`.
- `transfer_spectral_gap_ge`: the resulting spectral gap `log(μ_0 / μ_j)` is bounded below by
  `- log α`.
- `transfer_spectral_gap_wilson`: for the area law bound with perimeter factor
  `α = (t/t')^R · (1+a)^8`, the gap is at least `R · log(t'/t) - 8 · log(1+a)`.
-/

open Matrix Finset SpectralGap SurgeryGapClosure

namespace TransferBridge

variable {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
variable (hT : T.IsHermitian) (hPSD : ∀ i : Fin n, 0 ≤ hT.eigenvalues i)
include hPSD

/-- In a positive semi-definite matrix, each spectral component `μ_j^k · c_j²` is
at most the quadratic form `x ⬝ (T^k x)`. -/
lemma single_le_quad_pow (k : ℕ) (x : Fin n → ℝ) (j : Fin n) :
    hT.eigenvalues j ^ k * coeff hT j x ^ 2 ≤ x ⬝ᵥ ((T ^ k) *ᵥ x) := by
  rw [quad_pow hT k x]
  exact Finset.single_le_sum (f := fun i => hT.eigenvalues i ^ k * coeff hT i x ^ 2)
    (fun i _ => mul_nonneg (pow_nonneg (hPSD i) k) (sq_nonneg _))
    (Finset.mem_univ j)

/-- **The Transfer Eigenvalue Bound**:
If the expectation value of `T^k` on state `x` decays as `C · α^k · μ_0^k`,
then any eigenvalue `μ_j` with non-zero overlap `coeff hT j x ≠ 0` satisfies
`μ_j ≤ α · μ_0`. -/
theorem transfer_eigenvalue_le {μ0 α C : ℝ} (hμ0 : 0 ≤ μ0) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (x : Fin n → ℝ) (j : Fin n) (hj : coeff hT j x ≠ 0)
    (h_decay : ∀ k : ℕ, x ⬝ᵥ ((T ^ k) *ᵥ x) ≤ C * α ^ k * (μ0 ^ k * (x ⬝ᵥ x))) :
    hT.eigenvalues j ≤ α * μ0 := by
  have hc2_pos : 0 < coeff hT j x ^ 2 := sq_pos_of_ne_zero hj
  have hxx_nonneg : 0 ≤ x ⬝ᵥ x := by
    rw [← sum_coeff_sq hT x]
    exact sum_nonneg fun _ _ => sq_nonneg _
  set C' := C * (x ⬝ᵥ x) / coeff hT j x ^ 2 with hC'_def
  have hC' : 0 ≤ C' := div_nonneg (mul_nonneg hC hxx_nonneg) hc2_pos.le
  have h_pow : ∀ k : ℕ, hT.eigenvalues j ^ k ≤ C' * (α * μ0) ^ k := by
    intro k
    have h1 := (single_le_quad_pow hT hPSD k x j).trans (h_decay k)
    have heq : C * α ^ k * (μ0 ^ k * (x ⬝ᵥ x)) = (C * (x ⬝ᵥ x)) * (α * μ0) ^ k := by
      rw [mul_pow]
      ring
    rw [heq] at h1
    rw [hC'_def, div_mul_eq_mul_div, le_div_iff₀ hc2_pos]
    exact h1
  exact eigenvalue_le_of_pow_bound (hPSD j) (mul_nonneg hα hμ0) hC' h_pow

/-- **The Spectral Gap Lower Bound**:
From `μ_j ≤ α · μ_0`, the spectral gap `log(μ_0 / μ_j)` is bounded below by `- log α`. -/
theorem transfer_spectral_gap_ge {μ0 α C : ℝ} (hμ0 : 0 < μ0) (hα : 0 < α) (hC : 0 ≤ C)
    (x : Fin n → ℝ) (j : Fin n) (hj : coeff hT j x ≠ 0) (hμj_pos : 0 < hT.eigenvalues j)
    (h_decay : ∀ k : ℕ, x ⬝ᵥ ((T ^ k) *ᵥ x) ≤ C * α ^ k * (μ0 ^ k * (x ⬝ᵥ x))) :
    - Real.log α ≤ Real.log (μ0 / hT.eigenvalues j) := by
  have h_le := transfer_eigenvalue_le hT hPSD hμ0.le hα.le hC x j hj h_decay
  have h_div : hT.eigenvalues j / μ0 ≤ α := (div_le_iff₀ hμ0).mpr h_le
  have h_log := Real.log_le_log (div_pos hμj_pos hμ0) h_div
  have h_inv : Real.log (μ0 / hT.eigenvalues j) = - Real.log (hT.eigenvalues j / μ0) := by
    rw [← Real.log_inv, inv_div]
  rw [h_inv]
  linarith

/-- **Spectral Gap with Perimeter Factor**:
Under the Wilson area law with perimeter factor `α = (t/t')^R · (1+a)^8`,
the spectral gap satisfies:
`log(μ_0 / μ_j) ≥ R · log(t'/t) - 8 · log(1+a)`. -/
theorem transfer_spectral_gap_wilson {μ0 t t' a C : ℝ} (hμ0 : 0 < μ0)
    (ht : 0 < t) (htt' : t < t') (ha : 0 ≤ a) (hC : 0 ≤ C) (R : ℕ)
    (x : Fin n → ℝ) (j : Fin n) (hj : coeff hT j x ≠ 0) (hμj_pos : 0 < hT.eigenvalues j)
    (h_decay : ∀ k : ℕ, x ⬝ᵥ ((T ^ k) *ᵥ x) ≤
      C * ((t / t') ^ R * (1 + a) ^ 8) ^ k * (μ0 ^ k * (x ⬝ᵥ x))) :
    (R : ℝ) * Real.log (t' / t) - 8 * Real.log (1 + a) ≤ Real.log (μ0 / hT.eigenvalues j) := by
  have ht' : 0 < t' := ht.trans htt'
  have h1a : 0 < 1 + a := by linarith
  have hq : 0 < (t / t') ^ R * (1 + a) ^ 8 :=
    mul_pos (pow_pos (div_pos ht ht') R) (pow_pos h1a 8)
  have h_gap := transfer_spectral_gap_ge hT hPSD hμ0 hq hC x j hj hμj_pos h_decay
  have h_log_split : Real.log ((t / t') ^ R * (1 + a) ^ 8) =
      (R : ℝ) * Real.log (t / t') + 8 * Real.log (1 + a) := by
    rw [Real.log_mul (pow_pos (div_pos ht ht') R).ne' (pow_pos h1a 8).ne',
      Real.log_pow, Real.log_pow]
    all_goals norm_num
  have h_neg_log : - Real.log ((t / t') ^ R * (1 + a) ^ 8) =
      (R : ℝ) * Real.log (t' / t) - 8 * Real.log (1 + a) := by
    have h_inv : Real.log (t / t') = - Real.log (t' / t) := by
      rw [← Real.log_inv, inv_div]
    rw [h_log_split, h_inv]
    ring
  rwa [h_neg_log] at h_gap

end TransferBridge
