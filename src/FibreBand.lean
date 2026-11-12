/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import FibreSurgery
import NavaRobertsonIndependent.Mathematics.D23d_BandWidth

/-!

# The defect on the band of high tension: a lower bound for every state

## i. Overview

The surplus of a unit state `ψ` of the chain `H_d`, `surplus d ψ = Var(T) Var(P) - cov² - ⟨K⟩²/4`,
is the amount by which `ψ` fails to saturate Robertson–Schrödinger. `D23d` proves, for every unit
state,
`gapK d · (surplus ψ - defectGram d)² ≤ 2048 (2/(d-1) - ⟨K_d⟩_ψ)`.
The deficit `2/(d-1) - ⟨K_d⟩_ψ` is the distance of the tension to its maximum, the limit `c`. So
near `c` the surplus is near `defectGram d`, for every state. Here the explicit lower bound: with the
deficit at most `η`, `surplus ψ ≥ defectGram d - √(2048 η / gapK d)`, and with the deficit at most a
quarter of the band width, `surplus ψ ≥ defectGram d / 2 = massSq d / (2 (d-1)²)`.

This is a bound on a functional of the state, uniform on the band. It is not an operator inequality:
`surplus` is not the expectation of an operator. To use it as the mass of a fibre one must choose
the operator, for instance `M² = m² Π`, with `Π` the projection onto the band and `m²` this lower
bound; that choice is a model assumption, with a constant that is derived here.

## ii. Key results

- `FibreBand.surplus_ge_of_deficit` : `surplus ψ ≥ defectGram d - √(2048 η / gapK d)`.
- `FibreBand.surplus_ge_half` : on the quarter of the band, `surplus ψ ≥ defectGram d / 2`.
- `FibreBand.surplus_ge_massSq` : and `defectGram d / 2 = massSq d / (2 (d-1)²)`.

## iii. Table of contents

- A. The lower bound on the band

## iv. References

-/

open Gnomon GramStep BandWidth TransportPosition NearMaxTension

namespace FibreBand

/-- **The surplus on the band**: if the tension deficit is at most `η`, then
`surplus ψ ≥ defectGram d - √(2048 η / gapK d)`. -/
theorem surplus_ge_of_deficit {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) {η : ℝ}
    (h : 2 / ((d : ℝ) - 1) - tension d ψ ≤ η) :
    defectGram d - Real.sqrt (2048 * η / gapK d) ≤ surplus d ψ := by
  have hg : 0 < gapK d := gapK_pos hd
  have hb := surplus_band hd ψ hψ
  have h1 : (surplus d ψ - defectGram d) ^ 2 ≤ 2048 * η / gapK d := by
    rw [le_div_iff₀ hg]
    nlinarith [hb, h]
  have h2 := Real.abs_le_sqrt h1
  linarith [(abs_le.mp h2).1]

/-- **A quarter of the band**: if the deficit is at most a quarter of the band width, the surplus is
at least half of `defectGram d`. -/
theorem surplus_ge_half {d : ℕ} (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (h : 2 / ((d : ℝ) - 1) - tension d ψ ≤ bandWidth d / 4) :
    defectGram d / 2 ≤ surplus d ψ := by
  have hd2 : 2 ≤ d := by omega
  have hg : 0 < gapK d := gapK_pos hd2
  have hgd : 0 < defectGram d := gramStep_gram_pos hd
  have h1 := surplus_ge_of_deficit hd2 ψ hψ h
  have h2 : 2048 * (bandWidth d / 4) / gapK d = (defectGram d / 2) ^ 2 := by
    unfold bandWidth
    field_simp
    ring
  rw [h2, Real.sqrt_sq (by positivity)] at h1
  linarith

/-- **The fibre mass on the band**: with the deficit at most a quarter of the band width,
`surplus ψ ≥ massSq d / (2 (d-1)²)`, where `massSq d = C_N(d)² - 1`. -/
theorem surplus_ge_massSq {d : ℕ} (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (h : 2 / ((d : ℝ) - 1) - tension d ψ ≤ bandWidth d / 4) :
    FibreSurgery.massSq d / (2 * ((d : ℝ) - 1) ^ 2) ≤ surplus d ψ := by
  have h1 := surplus_ge_half hd ψ hψ h
  have h2 : defectGram d = FibreSurgery.massSq d / ((d : ℝ) - 1) ^ 2 :=
    gramStep_gram (by omega)
  rw [h2] at h1
  have hd1 : (0 : ℝ) < ((d : ℝ) - 1) := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc FibreSurgery.massSq d / (2 * ((d : ℝ) - 1) ^ 2)
      = FibreSurgery.massSq d / ((d : ℝ) - 1) ^ 2 / 2 := by field_simp
    _ ≤ surplus d ψ := h1

end FibreBand
