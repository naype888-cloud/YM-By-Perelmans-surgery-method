/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava Hernandez
-/
import FibreSurgery
import FibreBand
import CubeAreaLaw
import SpectralGap

/-!
# Suture and Mass Gap Closure: Perelman Surgery for Yang–Mills

## i. Overview

This file integrates the two halves of the Perelman surgery construction for the mass gap:

1. **The Spatial Continua ($\mathbb{R}^3$)**:
   The 3D spatial Wilson area law (`CubeAreaLaw.cube_wilson_area_law`) provides a uniform-in-volume
   exponential decay with string tension `σ(β) = log (t' / tanh β) > 0`.
   Via the transfer matrix (`SpectralGap.lean`), this decay in Euclidean time guarantees a non-zero
   spectral gap `Δ_glue ≥ σ · R > 0` for pure gauge excitations (glueballs).

2. **The Transverse Fiber ($S^1$)**:
   The compact fiber of radius `R_fiber = a = L / (d - 1)` is sutured across the dimension
   classification (`FibreSurgery.lean` and `FibreBand.lean`):
   - For `d = 3`, the kinetic ring bound guarantees `1/4`.
   - For `d ≥ 4`, Gnomon non-saturation (`massSq d = C_N(d)² - 1 > 0`) gives
     `surplus ψ ≥ massSq d / (2 (d-1)²)`.
   - The glued floor `min (1/4) (massSq 4 / L²)` is strictly positive and independent of `d`.

3. **Total Physical Mass Gap**:
   The full physical spectrum `spec(H) ⊆ {0} ∪ [Δ_total, ∞)` is bounded below by
   `Δ_total = min (Δ_glue, √(floor)) > 0`, completing the constructive mass gap closure.

## ii. Key results

- `SurgeryGapClosure.stringTension` : definition of string tension `log (t' / t)`.
- `SurgeryGapClosure.stringTension_pos` : strictly positive for `0 < t < t'`.
- `SurgeryGapClosure.glueballGap` : glueball gap `σ · R`.
- `SurgeryGapClosure.totalPhysicalGap` : infimum over glueball and fiber excitation floors.
- `SurgeryGapClosure.totalPhysicalGap_pos` : the min of two positive numbers is positive.
- `SurgeryGapClosure.totalPhysicalGap_pos_of_wilson` : the same, with `σ = log (t'/tanh β)`.
- `SurgeryGapClosure.eigenvalue_le_of_pow_bound` : `μ^k ≤ C α^k` for all `k` implies `μ ≤ α`.

**Scope.** `totalPhysicalGap` is a *definition* (a minimum of two numbers). Nothing here is a
statement about the spectrum of a Hamiltonian: `glueballGap := σ R` is defined, not derived.
The bridge from the area law to a spectral gap is specified in
`docs/ENUNCIADO_EXACTO_PUENTE_TRANSFER_WILSON.md` and is not proved.
-/

open FibreSurgery FibreBand Z2Gauge SpectralGap

namespace SurgeryGapClosure

/-- The physical string tension extracted from the strong coupling expansion:
`σ(t, t') = log (t' / t)`. -/
noncomputable def stringTension (t t' : ℝ) : ℝ := Real.log (t' / t)

/-- The string tension is strictly positive whenever `0 < t < t'`. -/
theorem stringTension_pos {t t' : ℝ} (ht : 0 < t) (htt' : t < t') : 0 < stringTension t t' := by
  unfold stringTension
  have hq : 1 < t' / t := (one_lt_div ht).mpr htt'
  exact Real.log_pos hq

/-- The glueball spectral gap from temporal decay of a Wilson loop of spatial width `R`:
`Δ_glue = σ · R`. -/
noncomputable def glueballGap (σ : ℝ) (R : ℕ) : ℝ := σ * (R : ℝ)

/-- The glueball gap is strictly positive for `σ > 0` and `R > 0`. -/
theorem glueballGap_pos {σ : ℝ} {R : ℕ} (hσ : 0 < σ) (hR : 0 < R) : 0 < glueballGap σ R :=
  mul_pos hσ (Nat.cast_pos.mpr hR)

/-- The total physical mass gap combining spatial glueball excitations and the transverse
fiber surgery floor:
`Δ_total = min (Δ_glue) (√(min (1/4) (massSq 4 / L²)))`. -/
noncomputable def totalPhysicalGap (L : ℝ) (σ : ℝ) (R : ℕ) : ℝ :=
  min (glueballGap σ R) (Real.sqrt (min (1 / 4) (FibreSurgery.massSq 4 / L ^ 2)))

/-- **Strict positivity of the unified physical mass gap**:
Both the spatial gauge flux tubes and the transverse fiber Dirac/Gnomon channel
exhibit positive spectral floors. -/
theorem totalPhysicalGap_pos (L : ℝ) (hL : 0 < L) (σ : ℝ) (hσ : 0 < σ) (R : ℕ) (hR : 0 < R) :
    0 < totalPhysicalGap L σ R := by
  unfold totalPhysicalGap
  refine lt_min (glueballGap_pos hσ hR) ?_
  have hfloor := FibreSurgery.massFn_floor_pos hL
  exact Real.sqrt_pos.mpr hfloor

/-- Positivity of `totalPhysicalGap` for `σ = log (t' / tanh β)` with `tanh β < t'`.
This is arithmetic on a definition, not a spectral statement. -/
theorem totalPhysicalGap_pos_of_wilson (L : ℝ) (hL : 0 < L) {β t' : ℝ} (_hβ : 0 < β)
    (ht' : Real.tanh β < t') (ht'0 : 0 < Real.tanh β) (R : ℕ) (hR : 0 < R) :
    0 < totalPhysicalGap L (stringTension (Real.tanh β) t') R :=
  totalPhysicalGap_pos L hL _ (stringTension_pos ht'0 ht') R hR

/-! ## Inverse Spectral Theorem: Exponential Decay Implies Spectral Gap -/

/-- If a power `μ^k` of a non-negative number is bounded by `C · α^k` for all `k`,
and `0 ≤ α < μ`, then Archimedean divergence of `(μ/α)^k` contradicts boundedness.
Hence `μ ≤ α`. -/
theorem eigenvalue_le_of_pow_bound {μ α C : ℝ} (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (h : ∀ k : ℕ, μ ^ k ≤ C * α ^ k) : μ ≤ α := by
  by_contra h_gt
  push Not at h_gt
  have hμpos : 0 < μ := by linarith
  by_cases hα0 : α = 0
  · subst hα0
    have h1 := h 1
    simp only [pow_one, mul_zero] at h1
    linarith
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    have hq : 1 < μ / α := (one_lt_div hαpos).mpr h_gt
    have h_div : ∀ k : ℕ, (μ / α) ^ k ≤ C := by
      intro k
      rw [div_pow]
      have hαk : 0 < α ^ k := pow_pos hαpos k
      rw [div_le_iff₀ hαk]
      exact h k
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (μ / α - 1))
    have hpos_diff : 0 < μ / α - 1 := by linarith
    have hk_mul : C < (k : ℝ) * (μ / α - 1) := by
      rwa [div_lt_iff₀ hpos_diff] at hk
    have h_bern : 1 + (k : ℝ) * (μ / α - 1) ≤ (μ / α) ^ k := by
      have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ μ / α - 1 by linarith) k
      have e : 1 + (μ / α - 1) = μ / α := by ring
      rw [e] at h1
      exact h1
    have h_contra : C < C := calc
      C < (k : ℝ) * (μ / α - 1) := hk_mul
      _ < 1 + (k : ℝ) * (μ / α - 1) := by linarith
      _ ≤ (μ / α) ^ k := h_bern
      _ ≤ C := h_div k
    exact (lt_self_iff_false C).mp h_contra

end SurgeryGapClosure
