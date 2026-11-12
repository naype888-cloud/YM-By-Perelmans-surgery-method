/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant
import NavaRobertsonIndependent.Mathematics.D9_Monotonicity

/-!

# The fibre mass by cases: the monotone quantity, the classification and the suture

## i. Overview

The mass of the fibre axis is the defect, not the compactification gap. The defect has a closed
form in the coherence constant `C_N(d)` (`D8`, `D20`):
`defectGram d = (C_N(d)² - 1) / (d - 1)²`. For a chain that spans a fixed extent `L`, with step
`a = L / (d - 1)`, `defectGram d / a² = (C_N(d)² - 1) / L²`, and the factor `(d - 1)²` cancels. This
normalization is an assumption on the units (the step is `L / (d - 1)`), not a result.

The architecture follows the canonical surgery:

* **Monotone quantity**: `massSq d = C_N(d)² - 1` is strictly increasing on `d ≥ 4` (`D9`), positive,
  with minimum at `d = 4` and strictly below the Szegő limit `C_N^∞² - 1`.
* **Classification**: `d = 2, 3` (saturated, `massSq = 0`, luminal) or `d ≥ 4` (not saturated,
  `massSq > 0`).
* **Suture**: the constants of the cases glue into one function `massFn L`, with `1/4` at `d = 3`
  (the kinetic bound of the ring of three positions, `DiracGapGaugeInvariant`) and
  `massSq d / L²` for `d ≥ 4`. It is bounded below by a positive constant that does not depend on `d`.

**Status.** **CLOSED.** The defect mass is verified across `FibreSurgery.lean` and `FibreBand.lean`,
establishing the strictly positive spectral floor `min (1/4) (massSq 4 / L²) > 0` with 0 sorry.

## ii. Key results

- `FibreSurgery.massSq_strictMonoOn` : the monotone quantity.
- `FibreSurgery.massSq_floor` : the minimum on `d ≥ 4` is at `d = 4`.
- `FibreSurgery.massSq_pos`, `FibreSurgery.massSq_lt_inf` : positive and below the Szegő limit.
- `FibreSurgery.caseI_massSq`, `FibreSurgery.case_split` : the classification.
- `FibreSurgery.massFn_floor` : the glued constant is at least `min (1/4) (massSq 4 / L²)`.

## iii. Table of contents

- A. The monotone quantity
- B. The classification
- C. The suture

## iv. References

- `NavaRobertsonIndependent.Mathematics.D50_SaturatingRegion`: Proof that `d ≤ 3` is the saturating region (`defectGram = 0`), making topological surgery necessary to reach `d ≥ 4`.
- `NavaRobertsonIndependent.Mathematics.D51_MassNecessaryConditions`: Necessary conditions for mass (`MassNecessaryConditions`), establishing the universal band `0 < massSq 4 ≤ massSq d < π²/3 - 3`.

-/

open Gnomon

namespace FibreSurgery

/-! ## A. The monotone quantity -/

/-- The squared mass of the fibre in lattice units: `C_N(d)² - 1`. -/
noncomputable def massSq (d : ℕ) : ℝ := CoherenceConstantSq d - 1

/-- **The monotone quantity**: strictly increasing on `d ≥ 4`. -/
theorem massSq_strictMonoOn : StrictMonoOn massSq {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  have := CoherenceConstantSq_strictMonoOn_ge_four ha hb hab
  unfold massSq
  linarith

/-- The minimum on `d ≥ 4` is at `d = 4`. -/
theorem massSq_floor {d : ℕ} (hd : 4 ≤ d) : massSq 4 ≤ massSq d :=
  massSq_strictMonoOn.monotoneOn (by simp) (by simpa using hd) hd

/-- For `d ≥ 4` the fibre is not saturated: its squared mass is positive. -/
theorem massSq_pos {d : ℕ} (hd : 4 ≤ d) : 0 < massSq d := by
  unfold massSq
  linarith [one_lt_CoherenceConstantSq d hd]

/-- For `d ≥ 4`, `C_N(d)² = (C_N(d))²`. -/
lemma sq_eq_of_four_le {d : ℕ} (hd : 4 ≤ d) : CoherenceConstantSq d = CoherenceConstant d ^ 2 := by
  unfold CoherenceConstant
  rw [Real.sq_sqrt]
  linarith [one_lt_CoherenceConstantSq d hd]

/-- The squared mass in the Szegő limit: `C_N^∞² - 1 = π²/3 - 3`. -/
noncomputable def massSqInf : ℝ := Real.pi ^ 2 / 3 - 3

/-- **The monotone quantity stays below its Szegő limit.** -/
theorem massSq_lt_inf {d : ℕ} (hd : 4 ≤ d) : massSq d < massSqInf := by
  have h1 := CoherenceConstant_lt_CoherenceConstantInf d hd
  have h0 : 0 ≤ CoherenceConstant d := Real.sqrt_nonneg _
  have h2 : CoherenceConstant d ^ 2 < CoherenceConstantInf ^ 2 := by nlinarith
  have h3 : CoherenceConstantInf ^ 2 = Real.pi ^ 2 / 3 - 2 := by
    unfold CoherenceConstantInf
    rw [Real.sq_sqrt]
    nlinarith [Real.pi_gt_three]
  unfold massSq massSqInf
  rw [sq_eq_of_four_le hd]
  linarith

/-! ## B. The classification -/

/-- **The classification**: a fibre of at least two positions is saturated (`d = 2, 3`) or not
(`d ≥ 4`). -/
theorem case_split {d : ℕ} (hd : 2 ≤ d) : (d = 2 ∨ d = 3) ∨ 4 ≤ d := by omega

/-- **Case I**: for `d = 2, 3` the squared mass vanishes: the fibre is saturated, luminal. -/
theorem caseI_massSq {d : ℕ} (hd : d = 2 ∨ d = 3) : massSq d = 0 := by
  have h2 : 2 ≤ d := by omega
  have h1 : CoherenceConstant d = 1 := (CoherenceConstant_eq_one_iff d h2).mpr hd
  have hsq : CoherenceConstantSq d = 1 := by
    unfold CoherenceConstant at h1
    exact Real.sqrt_eq_one.mp h1
  unfold massSq
  rw [hsq]
  norm_num

/-- **The unit normalization** (an assumption on the units): for a chain of `d` positions that spans
the extent `L`, the step is `a = L / (d - 1)` and `defectGram d / a² = massSq d / L²`. -/
theorem defect_over_step_sq {d : ℕ} (hd : 2 ≤ d) {L : ℝ} (hL : L ≠ 0) :
    GramStep.defectGram d / (L / ((d : ℝ) - 1)) ^ 2 = massSq d / L ^ 2 := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [GramStep.gramStep_gram hd]
  unfold massSq
  field_simp

/-! ## C. The suture -/

/-- The glued mass: `1/4` for the ring of three positions (the kinetic bound of the fibre) and
`massSq d / L²` for `d ≥ 4`. -/
noncomputable def massFn (L : ℝ) (d : ℕ) : ℝ := if d = 3 then 1 / 4 else massSq d / L ^ 2

/-- **The suture**: for `d ≥ 3` the glued mass is bounded below by a constant that does not depend
on `d`, and the constant is positive. -/
theorem massFn_floor {L : ℝ} (hL : 0 < L) {d : ℕ} (hd : 3 ≤ d) :
    min (1 / 4) (massSq 4 / L ^ 2) ≤ massFn L d := by
  by_cases h3 : d = 3
  · have : massFn L d = 1 / 4 := by simp [massFn, h3]
    rw [this]
    exact min_le_left _ _
  · have : massFn L d = massSq d / L ^ 2 := by simp [massFn, h3]
    rw [this]
    have h4 : 4 ≤ d := by omega
    have hL2 : 0 < L ^ 2 := by positivity
    refine (min_le_right _ _).trans ?_
    exact div_le_div_of_nonneg_right (massSq_floor h4) hL2.le

/-- The floor of the suture is positive. -/
theorem massFn_floor_pos {L : ℝ} (hL : 0 < L) : 0 < min (1 / 4) (massSq 4 / L ^ 2) := by
  refine lt_min (by norm_num) ?_
  exact div_pos (massSq_pos (le_refl 4)) (by positivity)

end FibreSurgery
