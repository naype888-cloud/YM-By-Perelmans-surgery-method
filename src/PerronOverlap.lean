/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import SpectralGap

/-!
# A positive vector overlaps the top eigenspace of a symmetric matrix with nonnegative entries

If `T` is symmetric with nonnegative entries and `v` has positive entries, then `v` has a nonzero
component on some eigenvector of the largest eigenvalue `μ₀`.

Proof. Let `e` be a unit eigenvector for `μ₀` and `a = |e|` (entrywise). Since `T ≥ 0` entrywise,
`aᵀ T a ≥ eᵀ T e = μ₀`, while `aᵀ T a ≤ μ₀ ‖a‖² = μ₀` by the spectral expansion, so `a` has no
component outside the top eigenspace. Then `0 < v ⬝ a = ∑_j c_j(v) c_j(a)` forces some
`c_j(v) ≠ 0` with `μ_j = μ₀`.

## Main results

- `PerronOverlap.top_overlap` : `∃ j, μ_j = μ₀ ∧ c_j(v) ≠ 0`.
-/

open Matrix Finset SpectralGap

namespace PerronOverlap

variable {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}

lemma dot_eigen_self (hT : T.IsHermitian) (j : Fin n) :
    (hT.eigenvectorBasis j : Fin n → ℝ) ⬝ᵥ (hT.eigenvectorBasis j : Fin n → ℝ) = 1 := by
  have h := hT.eigenvectorBasis.orthonormal.1 j
  have h2 : inner ℝ (hT.eigenvectorBasis j) (hT.eigenvectorBasis j) = 1 := by
    rw [real_inner_self_eq_norm_sq, h]; norm_num
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
  simpa [star_trivial] using h2

/-- The Rayleigh quotient is at most the largest eigenvalue. -/
lemma rayleigh_le (hT : T.IsHermitian) {μ0 : ℝ} (hmax : ∀ j, hT.eigenvalues j ≤ μ0)
    (x : Fin n → ℝ) : x ⬝ᵥ (T *ᵥ x) ≤ μ0 * (x ⬝ᵥ x) := by
  have h1 := quad_pow hT 1 x
  have h0 := quad_pow hT 0 x
  simp only [pow_one, pow_zero, one_mulVec, one_mul] at h1 h0
  rw [h1, h0, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hmax j) (sq_nonneg _)

theorem top_overlap (hT : T.IsHermitian) (hnn : ∀ i j, 0 ≤ T i j) {μ0 : ℝ}
    (hmax : ∀ j, hT.eigenvalues j ≤ μ0) (hex : ∃ j, hT.eigenvalues j = μ0)
    (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ j, hT.eigenvalues j = μ0 ∧ coeff hT j v ≠ 0 := by
  obtain ⟨j0, hj0⟩ := hex
  set e : Fin n → ℝ := (hT.eigenvectorBasis j0 : Fin n → ℝ) with he
  have hee : e ⬝ᵥ e = 1 := dot_eigen_self hT j0
  have hTe : T *ᵥ e = μ0 • e := by
    rw [he, hT.mulVec_eigenvectorBasis, hj0]
  have heTe : e ⬝ᵥ (T *ᵥ e) = μ0 := by
    rw [hTe, dotProduct_smul, hee, smul_eq_mul, mul_one]
  set a : Fin n → ℝ := fun i => |e i| with ha
  have haa : a ⬝ᵥ a = 1 := by
    rw [← hee]
    simp only [dotProduct, ha]
    exact Finset.sum_congr rfl fun i _ => by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
  have haT_ge : e ⬝ᵥ (T *ᵥ e) ≤ a ⬝ᵥ (T *ᵥ a) := by
    simp only [dotProduct, mulVec, ha]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : e i * e j ≤ |e i| * |e j| := by
      rw [← abs_mul]; exact le_abs_self _
    nlinarith [hnn i j]
  have haT_eq : a ⬝ᵥ (T *ᵥ a) = μ0 := by
    have hle := rayleigh_le hT hmax a
    rw [haa, mul_one] at hle
    linarith
  -- `a` has no component outside the top eigenspace
  have hzero : ∀ j, (μ0 - hT.eigenvalues j) * coeff hT j a ^ 2 = 0 := by
    have h1 := quad_pow hT 1 a
    have h0 := quad_pow hT 0 a
    simp only [pow_one, pow_zero, one_mulVec] at h1 h0
    have hsum : ∑ j, (μ0 - hT.eigenvalues j) * coeff hT j a ^ 2 = 0 := by
      have : ∑ j, (μ0 - hT.eigenvalues j) * coeff hT j a ^ 2 =
          μ0 * (a ⬝ᵥ a) - a ⬝ᵥ (T *ᵥ a) := by
        rw [h1, h0, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, haa, haT_eq]; ring
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hmax j)) (sq_nonneg _)).mp hsum j (Finset.mem_univ j)
  have hoff : ∀ j, hT.eigenvalues j ≠ μ0 → coeff hT j a = 0 := by
    intro j hj
    have hne : μ0 - hT.eigenvalues j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
    have := hzero j
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  -- the pairing `v ⬝ a` is positive
  have hpair : v ⬝ᵥ a = ∑ j, coeff hT j v * coeff hT j a := by
    conv_lhs => rw [← sum_coeff_smul hT v]
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_dotProduct, smul_eq_mul]
    congr 1
  have hpos : 0 < v ⬝ᵥ a := by
    have hex' : ∃ i, e i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : e ⬝ᵥ e = 0 := by simp [dotProduct, hcon]
      linarith
    obtain ⟨i0, hi0⟩ := hex'
    simp only [dotProduct, ha]
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hv i).le (abs_nonneg _)) ⟨i0, Finset.mem_univ _, ?_⟩
    exact mul_pos (hv i0) (abs_pos.mpr hi0)
  by_contra hcon
  push Not at hcon
  have : v ⬝ᵥ a = 0 := by
    rw [hpair]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : hT.eigenvalues j = μ0
    · rw [hcon j hj, zero_mul]
    · rw [hoff j hj, mul_zero]
  linarith

end PerronOverlap
