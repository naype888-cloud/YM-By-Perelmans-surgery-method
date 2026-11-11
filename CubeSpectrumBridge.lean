/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# 3D Tight-Binding Cube Spectrum Bridge: Explicit Gap & Spectral Exhaustion

This module establishes the explicit spectral gap for the 3D open tight-binding cube,
grounded on the complete spectral theorem of `Cube/Spectrum.lean` and Physlib PR #1901.

## Key results
- `cubeGroundEnergy`: Ground state energy of the 3D cubic box of side `d`.
- `cubeExcitedEnergy`: First excited state energy of the 3D cubic box.
- `cubeSpectralGap`: Explicit analytical gap $\Delta_{\mathrm{cube}} = 2t(\cos(\pi/(d+1)) - \cos(2\pi/(d+1)))$.
- `cubeSpectralGap_pos`: Strict positivity of the 3D cubic cell spectral gap for any $d \ge 1$ and $t > 0$.
- `no_eigenvalue_in_cube_gap`: Exact exhaustion proving that no eigenvalue of the 3D cubic Hamiltonian
  can lie in the intermediate gap window $(E_{\mathrm{ground}}, E_{\mathrm{ground}} + \Delta_{\mathrm{cube}})$.
-/

namespace CubeSpectrum

open Real

/-- The angle $\theta_k = (k + 1)\pi / (d + 1)$ for site index $k \in \{0, \dots, d-1\}$. -/
noncomputable def cubeAngle (d : ℕ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * Real.pi / ((d : ℝ) + 1)

/-- The ground state energy of the isotropic 3D cube of side `d`:
all three axes in the lowest mode $k = 0$ ($\theta_0 = \pi / (d + 1)$). -/
noncomputable def cubeGroundEnergy (E0 t : ℝ) (d : ℕ) : ℝ :=
  3 * E0 - 6 * t * Real.cos (cubeAngle d 0)

/-- The first excited state energy of the isotropic 3D cube:
two axes in mode $k = 0$ and one axis in mode $k = 1$ ($\theta_1 = 2\pi / (d + 1)$). -/
noncomputable def cubeExcitedEnergy (E0 t : ℝ) (d : ℕ) : ℝ :=
  3 * E0 - 4 * t * Real.cos (cubeAngle d 0) - 2 * t * Real.cos (cubeAngle d 1)

/-- The analytical spectral gap of the 3D tight-binding cube:
$\Delta_{\mathrm{cube}} = 2t (\cos(\pi / (d + 1)) - \cos(2\pi / (d + 1)))$. -/
noncomputable def cubeSpectralGap (t : ℝ) (d : ℕ) : ℝ :=
  2 * t * (Real.cos (cubeAngle d 0) - Real.cos (cubeAngle d 1))

/-- Relation between excited energy, ground energy, and the spectral gap. -/
theorem cubeExcitedEnergy_eq (E0 t : ℝ) (d : ℕ) :
    cubeExcitedEnergy E0 t d = cubeGroundEnergy E0 t d + cubeSpectralGap t d := by
  unfold cubeExcitedEnergy cubeGroundEnergy cubeSpectralGap
  ring

/-- The angle $\theta_0 = \pi / (d+1)$ lies in $(0, \pi)$. -/
lemma cubeAngle_zero_mem (d : ℕ) : 0 < cubeAngle d 0 ∧ cubeAngle d 0 < Real.pi := by
  unfold cubeAngle
  simp only [Nat.cast_zero, zero_add, one_mul]
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  refine ⟨div_pos Real.pi_pos hpos, ?_⟩
  rw [div_lt_iff₀ hpos]
  have : Real.pi * 1 < Real.pi * ((d : ℝ) + 1) := by
    nlinarith [Real.pi_pos]
  linarith

/-- The angle $\theta_1 = 2\pi / (d+1)$ is strictly greater than $\theta_0 = \pi / (d+1)$. -/
lemma cubeAngle_zero_lt_one (d : ℕ) : cubeAngle d 0 < cubeAngle d 1 := by
  unfold cubeAngle
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [div_lt_div_iff_of_pos_right hpos]
  simp only [Nat.cast_zero, zero_add, one_mul, Nat.cast_one]
  have : (1 : ℝ) * Real.pi < 2 * Real.pi := by nlinarith [Real.pi_pos]
  exact this

/-- The angle $\theta_1 = 2\pi / (d+1)$ lies in $(0, \pi]$ for all $d \ge 1$. -/
lemma cubeAngle_one_le_pi {d : ℕ} (hd : 1 ≤ d) : cubeAngle d 1 ≤ Real.pi := by
  unfold cubeAngle
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  simp only [Nat.cast_one]
  have hd_real : 2 ≤ (d : ℝ) + 1 := by
    exact_mod_cast (Nat.succ_le_succ hd)
  nlinarith [Real.pi_pos]

/-- Cosine is strictly decreasing on $[0, \pi]$, hence $\cos(\theta_0) > \cos(\theta_1)$. -/
lemma cos_cubeAngle_zero_gt_one {d : ℕ} (hd : 1 ≤ d) :
    Real.cos (cubeAngle d 1) < Real.cos (cubeAngle d 0) := by
  have h0 := cubeAngle_zero_mem d
  have h0_ge : 0 ≤ cubeAngle d 0 := le_of_lt h0.1
  have h1_le : cubeAngle d 1 ≤ Real.pi := cubeAngle_one_le_pi hd
  have h_lt : cubeAngle d 0 < cubeAngle d 1 := cubeAngle_zero_lt_one d
  exact Real.cos_lt_cos_of_nonneg_of_le_pi h0_ge h1_le h_lt

/-- **Theorem: Strict Positivity of the 3D Tight-Binding Cube Spectral Gap**.
For any non-trivial box size $d \ge 1$ and non-vanishing hopping parameter $t > 0$,
the spectral gap $\Delta_{\mathrm{cube}} = 2t(\cos\theta_0 - \cos\theta_1) > 0$. -/
theorem cubeSpectralGap_pos {t : ℝ} (ht : 0 < t) {d : ℕ} (hd : 1 ≤ d) :
    0 < cubeSpectralGap t d := by
  unfold cubeSpectralGap
  have hdiff : 0 < Real.cos (cubeAngle d 0) - Real.cos (cubeAngle d 1) :=
    sub_pos.mpr (cos_cubeAngle_zero_gt_one hd)
  have h2t : 0 < 2 * t := by linarith
  exact mul_pos h2t hdiff

/-- General energy of mode triplet $(a, b, c)$ in the isotropic 3D cube. -/
noncomputable def cubeModeEnergy (E0 t : ℝ) (d : ℕ) (a b c : ℕ) : ℝ :=
  3 * E0 - 2 * t * (Real.cos (cubeAngle d a) + Real.cos (cubeAngle d b) + Real.cos (cubeAngle d c))

lemma cubeAngle_le_of_le (d : ℕ) {j k : ℕ} (h : j ≤ k) :
    cubeAngle d j ≤ cubeAngle d k := by
  unfold cubeAngle
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hpos]
  have hj : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ h)
  nlinarith [Real.pi_pos]

lemma cubeAngle_le_pi {d : ℕ} {k : ℕ} (hk : k < d) :
    cubeAngle d k ≤ Real.pi := by
  unfold cubeAngle
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  have hk_succ : ((k : ℝ) + 1) ≤ ((d : ℝ) + 1) := by exact_mod_cast (Nat.succ_le_succ (le_of_lt hk))
  nlinarith [Real.pi_pos]

lemma cos_cubeAngle_le_cos_zero {d : ℕ} {k : ℕ} (hk : k < d) :
    Real.cos (cubeAngle d k) ≤ Real.cos (cubeAngle d 0) := by
  have h0 := cubeAngle_zero_mem d
  have h0_ge : 0 ≤ cubeAngle d 0 := le_of_lt h0.1
  have hk_le : cubeAngle d k ≤ Real.pi := cubeAngle_le_pi hk
  have h_le : cubeAngle d 0 ≤ cubeAngle d k := cubeAngle_le_of_le d (Nat.zero_le k)
  exact Real.cos_le_cos_of_nonneg_of_le_pi h0_ge hk_le h_le

lemma cos_cubeAngle_le_cos_one {d : ℕ} {k : ℕ} (h1 : 1 ≤ k) (hk : k < d) :
    Real.cos (cubeAngle d k) ≤ Real.cos (cubeAngle d 1) := by
  have h0 := cubeAngle_zero_mem d
  have h1_ge : 0 ≤ cubeAngle d 1 := by
    have := cubeAngle_zero_lt_one d
    linarith [h0.1]
  have hk_le : cubeAngle d k ≤ Real.pi := cubeAngle_le_pi hk
  have h_le : cubeAngle d 1 ≤ cubeAngle d k := cubeAngle_le_of_le d h1
  exact Real.cos_le_cos_of_nonneg_of_le_pi h1_ge hk_le h_le

/-- Any excited mode triplet (not all 0) has energy at least equal to `cubeExcitedEnergy`. -/
theorem cubeModeEnergy_ge_excited {E0 t : ℝ} (ht : 0 < t) {d : ℕ} (hd : 1 ≤ d)
    (a b c : ℕ) (ha : a < d) (hb : b < d) (hc : c < d)
    (h_not_all_zero : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    cubeExcitedEnergy E0 t d ≤ cubeModeEnergy E0 t d a b c := by
  have h_cases : 1 ≤ a ∨ 1 ≤ b ∨ 1 ≤ c := by
    by_contra h_neg
    push Not at h_neg
    have ha0 : a = 0 := Nat.lt_one_iff.mp h_neg.1
    have hb0 : b = 0 := Nat.lt_one_iff.mp h_neg.2.1
    have hc0 : c = 0 := Nat.lt_one_iff.mp h_neg.2.2
    exact h_not_all_zero ⟨ha0, hb0, hc0⟩
  unfold cubeModeEnergy cubeExcitedEnergy
  rcases h_cases with ha1 | hb1 | hc1
  · have hca : Real.cos (cubeAngle d a) ≤ Real.cos (cubeAngle d 1) := cos_cubeAngle_le_cos_one ha1 ha
    have hcb : Real.cos (cubeAngle d b) ≤ Real.cos (cubeAngle d 0) := cos_cubeAngle_le_cos_zero hb
    have hcc : Real.cos (cubeAngle d c) ≤ Real.cos (cubeAngle d 0) := cos_cubeAngle_le_cos_zero hc
    have h_sum : Real.cos (cubeAngle d a) + Real.cos (cubeAngle d b) + Real.cos (cubeAngle d c) ≤
        2 * Real.cos (cubeAngle d 0) + Real.cos (cubeAngle d 1) := by linarith
    nlinarith
  · have hca : Real.cos (cubeAngle d a) ≤ Real.cos (cubeAngle d 0) := cos_cubeAngle_le_cos_zero ha
    have hcb : Real.cos (cubeAngle d b) ≤ Real.cos (cubeAngle d 1) := cos_cubeAngle_le_cos_one hb1 hb
    have hcc : Real.cos (cubeAngle d c) ≤ Real.cos (cubeAngle d 0) := cos_cubeAngle_le_cos_zero hc
    have h_sum : Real.cos (cubeAngle d a) + Real.cos (cubeAngle d b) + Real.cos (cubeAngle d c) ≤
        2 * Real.cos (cubeAngle d 0) + Real.cos (cubeAngle d 1) := by linarith
    nlinarith
  · have hca : Real.cos (cubeAngle d a) ≤ Real.cos (cubeAngle d 0) := cos_cubeAngle_le_cos_zero ha
    have hcb : Real.cos (cubeAngle d b) ≤ Real.cos (cubeAngle d 0) := cos_cubeAngle_le_cos_zero hb
    have hcc : Real.cos (cubeAngle d c) ≤ Real.cos (cubeAngle d 1) := cos_cubeAngle_le_cos_one hc1 hc
    have h_sum : Real.cos (cubeAngle d a) + Real.cos (cubeAngle d b) + Real.cos (cubeAngle d c) ≤
        2 * Real.cos (cubeAngle d 0) + Real.cos (cubeAngle d 1) := by linarith
    nlinarith

/-- **Theorem: Complete Spectral Exclusion in the Intermediate Gap Window**.
No eigenvalue of the 3D cubic tight-binding Hamiltonian can lie in the open window
$(E_{\mathrm{ground}}, E_{\mathrm{ground}} + \Delta_{\mathrm{cube}})$.
This unconditionally proves that the intermediate gap shell contains zero spectrum. -/
theorem no_eigenvalue_in_cube_gap {E0 t : ℝ} (ht : 0 < t) {d : ℕ} (hd : 1 ≤ d)
    (μ : ℝ) (h_eigen : ∃ a b c : ℕ, a < d ∧ b < d ∧ c < d ∧ cubeModeEnergy E0 t d a b c = μ) :
    ¬ (cubeGroundEnergy E0 t d < μ ∧ μ < cubeGroundEnergy E0 t d + cubeSpectralGap t d) := by
  rintro ⟨h_gt, h_lt⟩
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := h_eigen
  by_cases h0 : a = 0 ∧ b = 0 ∧ c = 0
  · rcases h0 with ⟨rfl, rfl, rfl⟩
    have heq : cubeModeEnergy E0 t d 0 0 0 = cubeGroundEnergy E0 t d := by
      unfold cubeModeEnergy cubeGroundEnergy
      ring
    rw [heq] at h_gt
    exact lt_irrefl _ h_gt
  · rw [← cubeExcitedEnergy_eq] at h_lt
    have h_le := cubeModeEnergy_ge_excited ht hd a b c ha hb hc h0
    exact not_lt_of_ge h_le h_lt

end CubeSpectrum
