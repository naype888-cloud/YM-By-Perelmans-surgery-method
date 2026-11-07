/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import SpectralGap

/-!
# The infinite-time limit: a bound uniform in the time extent passes to the top eigenspace

For a positive semidefinite `T` with eigenvalues `μ_j ≤ μ₀` and a vector `v`, let `c_j` be the
components of `v` on the eigenvectors `e_j` and `top = {j | μ_j = μ₀}`. If a matrix `Y`
(think of `X T^k X`, the loop inserted at two times) satisfies, for every `N`,

`(T^N v) ⬝ Y (T^N v) ≤ D · v ⬝ T^{2N+k} v`

(this is the finite-volume Wilson bound, with the time extent `2N + k` going to infinity), then
`∑_{i,l ∈ top} c_i c_l (e_i ⬝ Y e_l) ≤ D μ₀^k ∑_{j ∈ top} c_j²`, that is `w ⬝ Y w ≤ D μ₀^k ‖w‖²`
for `w = ∑_{j ∈ top} c_j e_j`.

## Main results

- `SlabLimit.pow_mulVec_expand` : `T^k x = ∑_j (c_j μ_j^k) e_j`.
- `SlabLimit.bilinear_expand` : `(T^a x) ⬝ Y (T^b x) = ∑_{i,l} c_i μ_i^a c_l μ_l^b (e_i ⬝ Y e_l)`.
- `SlabLimit.top_limit` : the limit inequality above.

## Scope

Pure linear algebra. That `v` overlaps the top eigenspace (Perron–Frobenius for positive entries)
and that the Wilson loop of the box has the form used in the hypothesis are NOT proved here.
-/

open Matrix Finset Filter Topology SpectralGap

namespace SlabLimit

variable {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}

/-- `T^k x = ∑_j (c_j μ_j^k) e_j`. -/
lemma pow_mulVec_expand (hT : T.IsHermitian) (k : ℕ) (x : Fin n → ℝ) :
    (T ^ k) *ᵥ x = ∑ j, (coeff hT j x * hT.eigenvalues j ^ k) •
      (hT.eigenvectorBasis j : Fin n → ℝ) := by
  have hx := sum_coeff_smul hT x
  conv_lhs => rw [← hx]
  rw [Matrix.mulVec_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, pow_mulVec_eigen, smul_smul]

/-- The bilinear spectral expansion. -/
lemma bilinear_expand (hT : T.IsHermitian) (Y : Matrix (Fin n) (Fin n) ℝ) (a b : ℕ)
    (x : Fin n → ℝ) :
    ((T ^ a) *ᵥ x) ⬝ᵥ (Y *ᵥ ((T ^ b) *ᵥ x)) =
      ∑ i, ∑ l, (coeff hT i x * hT.eigenvalues i ^ a) * (coeff hT l x * hT.eigenvalues l ^ b) *
        ((hT.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ (Y *ᵥ (hT.eigenvectorBasis l : Fin n → ℝ))) := by
  rw [pow_mulVec_expand hT a, pow_mulVec_expand hT b, Matrix.mulVec_sum, sum_dotProduct]
  refine sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- `r^N → 1` if `r = 1`, and `→ 0` if `0 ≤ r < 1`. -/
lemma tendsto_pow_ind {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Tendsto (fun N : ℕ => r ^ N) atTop (𝓝 (if r = 1 then 1 else 0)) := by
  by_cases hr : r = 1
  · simp [hr]
  · rw [if_neg hr]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one h0 (lt_of_le_of_ne h1 hr)

/-- **The limit inequality on the top eigenspace.** -/
theorem top_limit (hT : T.IsHermitian) (hPSD : ∀ j, 0 ≤ hT.eigenvalues j) {μ0 : ℝ} (hμ0 : 0 < μ0)
    (hmax : ∀ j, hT.eigenvalues j ≤ μ0) (Y : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (D : ℝ)
    (k : ℕ)
    (hlaw : ∀ N : ℕ, ((T ^ N) *ᵥ v) ⬝ᵥ (Y *ᵥ ((T ^ N) *ᵥ v)) ≤
      D * (v ⬝ᵥ ((T ^ (2 * N + k)) *ᵥ v))) :
    ∑ i ∈ univ.filter (fun j => hT.eigenvalues j = μ0),
      ∑ l ∈ univ.filter (fun j => hT.eigenvalues j = μ0),
        coeff hT i v * coeff hT l v *
          ((hT.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ (Y *ᵥ (hT.eigenvectorBasis l : Fin n → ℝ))) ≤
      D * μ0 ^ k * ∑ j ∈ univ.filter (fun j => hT.eigenvalues j = μ0), coeff hT j v ^ 2 := by
  set μ := hT.eigenvalues with hμ
  set c := fun j => coeff hT j v with hc
  set G := fun i l => (hT.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ
    (Y *ᵥ (hT.eigenvectorBasis l : Fin n → ℝ)) with hG
  set r := fun j => μ j / μ0 with hr
  have hr0 : ∀ j, 0 ≤ r j := fun j => div_nonneg (hPSD j) hμ0.le
  have hr1 : ∀ j, r j ≤ 1 := fun j => (div_le_one hμ0).mpr (hmax j)
  have hrμ : ∀ j, μ j = r j * μ0 := fun j => by simp [hr, div_mul_cancel₀ _ hμ0.ne']
  have hr_eq : ∀ j, r j = 1 ↔ μ j = μ0 := fun j => by
    simp only [hr]; exact div_eq_one_iff_eq hμ0.ne'
  -- the scaled sequences
  set f : ℕ → ℝ := fun N => ∑ i, ∑ l, (r i ^ N * r l ^ N) * (c i * c l * G i l) with hf
  set g : ℕ → ℝ := fun N =>
    D * μ0 ^ k * ∑ j, (r j ^ N * r j ^ N * r j ^ k) * c j ^ 2 with hg
  have hfg : ∀ N, f N ≤ g N := by
    intro N
    have h := hlaw N
    rw [bilinear_expand hT Y N N v, quad_pow hT] at h
    have hL : ∑ i, ∑ l, (c i * μ i ^ N) * (c l * μ l ^ N) * G i l = μ0 ^ (2 * N) * f N := by
      simp only [hf, Finset.mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
      rw [hrμ i, hrμ l]
      simp only [mul_pow, pow_mul, two_mul, pow_add]
      ring
    have hR : D * ∑ j, μ j ^ (2 * N + k) * c j ^ 2 = μ0 ^ (2 * N) * g N := by
      simp only [hg, Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [hrμ j]
      simp only [mul_pow, pow_add, pow_mul, two_mul]
      ring
    rw [hL, hR] at h
    exact le_of_mul_le_mul_left h (pow_pos hμ0 _)
  -- the limits
  have hpow : ∀ j, Tendsto (fun N : ℕ => r j ^ N) atTop (𝓝 (if r j = 1 then 1 else 0)) :=
    fun j => tendsto_pow_ind (hr0 j) (hr1 j)
  have hf_lim : Tendsto f atTop (𝓝 (∑ i, ∑ l, ((if r i = 1 then (1 : ℝ) else 0) *
      (if r l = 1 then 1 else 0)) * (c i * c l * G i l))) := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun l _ => ?_
    exact ((hpow i).mul (hpow l)).mul tendsto_const_nhds
  have hg_lim : Tendsto g atTop (𝓝 (D * μ0 ^ k * ∑ j,
      ((if r j = 1 then (1 : ℝ) else 0) * (if r j = 1 then 1 else 0) * r j ^ k) * c j ^ 2)) := by
    refine Tendsto.const_mul _ (tendsto_finset_sum _ fun j _ => ?_)
    exact (((hpow j).mul (hpow j)).mul tendsto_const_nhds).mul tendsto_const_nhds
  have hle := le_of_tendsto_of_tendsto' hf_lim hg_lim hfg
  -- identify the limits with sums over the top eigenspace
  have e1 : (∑ i, ∑ l, ((if r i = 1 then (1 : ℝ) else 0) * (if r l = 1 then 1 else 0)) *
      (c i * c l * G i l)) =
      ∑ i ∈ univ.filter (fun j => μ j = μ0), ∑ l ∈ univ.filter (fun j => μ j = μ0),
        c i * c l * G i l := by
    rw [Finset.sum_filter]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
    by_cases hi : μ i = μ0
    · simp only [hi, if_true, (hr_eq i).mpr hi]
      refine sum_congr rfl fun l _ => ?_
      by_cases hl : μ l = μ0 <;> simp [hl, (hr_eq l).mpr, hr_eq]
    · simp [hi, mt (hr_eq i).mp hi]
  have e2 : (∑ j, ((if r j = 1 then (1 : ℝ) else 0) * (if r j = 1 then 1 else 0) * r j ^ k) *
      c j ^ 2) = ∑ j ∈ univ.filter (fun j => μ j = μ0), c j ^ 2 := by
    rw [Finset.sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : μ j = μ0
    · simp [hj, (hr_eq j).mpr hj]
    · simp [hj, mt (hr_eq j).mp hj]
  rw [e1, e2] at hle
  exact hle

end SlabLimit
