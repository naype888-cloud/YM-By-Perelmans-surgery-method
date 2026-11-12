/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import FibreSurgery
import FibreBand

/-!
# Quantum Coherence Defect and Transverse Protection

This module provides the unified bridge for the quantum coherence defect $5/4$,
Robertson–Schrödinger uncertainty non-saturation, and transverse mass protection
as developed across Physlib PRs #1660, #1676, #1649, #1650, #1716, #1718, #1732,
#1723, #1725, #1756, #1730, #1742, #1774, #1822, #1844.

## Key Exports
- `FibreSurgery.massSq`: The squared mass of the fibre in lattice units ($C_N(d)^2 - 1$).
- `FibreSurgery.massFn_floor_pos`: Strict positivity of the transverse mass floor.
- `FibreBand.surplus_ge_massSq`: Explicit lower bound on Robertson–Schrödinger surplus along the maximal tension band.
-/

namespace CoherenceDefect

open FibreSurgery FibreBand

/-- The canonical lower bound for the transverse mass floor at scale L > 0. -/
theorem transverse_floor_pos {L : ℝ} (hL : 0 < L) : 0 < min (1 / 4) (massSq 4 / L ^ 2) :=
  massFn_floor_pos hL

end CoherenceDefect
