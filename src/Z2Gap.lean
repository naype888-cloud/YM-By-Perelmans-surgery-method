/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import Z2Transfer
import TransferBridge

/-!
# Spectral gap of the `Z₂` transfer matrix from the decay of a Wilson loop

`TransferBridge.transfer_spectral_gap_wilson` assumes that the transfer matrix is positive
semidefinite. For Wilson's `Z₂` model that is proved in `Z2Transfer.transfer_posSemidef`; here it is
discharged, connecting the spectral gap theorem directly to the decay bound of `x ⬝ T^k x` (proved in `Z2WilsonGap.hlaw`).

## Main results

- `Z2Gap.z2_spectral_gap` : for `β ≥ 0`, any positive spatial weight `w` and the transfer matrix of
  `Z2Transfer` indexed by `Fin n`, if `x ⬝ T^k x ≤ C ((t/t')^R (1+a)^8)^k μ₀^k ‖x‖²` and `x` has
  overlap with an eigenvector of positive eigenvalue `μ_j`, then
  `R log (t'/t) - 8 log (1+a) ≤ log (μ₀ / μ_j)`.
-/

open Matrix

namespace Z2Gap

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The transfer matrix of `Z2Transfer`, indexed by `Fin n`. -/
noncomputable def transferFin (β : ℝ) (w : (L → ZMod 2) → ℝ) :
    Matrix (Fin (Fintype.card (L → ZMod 2))) (Fin (Fintype.card (L → ZMod 2))) ℝ :=
  (Z2Transfer.transfer β w).submatrix (Fintype.equivFin (L → ZMod 2)).symm
    (Fintype.equivFin (L → ZMod 2)).symm

theorem transferFin_posSemidef {β : ℝ} (hβ : 0 ≤ β) (w : (L → ZMod 2) → ℝ) :
    (transferFin β w).PosSemidef :=
  (Z2Transfer.transfer_posSemidef hβ w).submatrix _

/-- **Spectral gap of the `Z₂` transfer matrix** from the decay of `x ⬝ T^k x`. -/
theorem z2_spectral_gap {β : ℝ} (hβ : 0 ≤ β) (w : (L → ZMod 2) → ℝ)
    {μ0 t t' a C : ℝ} (hμ0 : 0 < μ0) (ht : 0 < t) (htt' : t < t') (ha : 0 ≤ a) (hC : 0 ≤ C)
    (R : ℕ) (x : Fin (Fintype.card (L → ZMod 2)) → ℝ) (j : Fin (Fintype.card (L → ZMod 2)))
    (hj : SpectralGap.coeff (transferFin_posSemidef hβ w).1 j x ≠ 0)
    (hμj_pos : 0 < (transferFin_posSemidef hβ w).1.eigenvalues j)
    (h_decay : ∀ k : ℕ, x ⬝ᵥ ((transferFin β w ^ k) *ᵥ x) ≤
      C * ((t / t') ^ R * (1 + a) ^ 8) ^ k * (μ0 ^ k * (x ⬝ᵥ x))) :
    (R : ℝ) * Real.log (t' / t) - 8 * Real.log (1 + a) ≤
      Real.log (μ0 / (transferFin_posSemidef hβ w).1.eigenvalues j) :=
  TransferBridge.transfer_spectral_gap_wilson (transferFin_posSemidef hβ w).1
    (fun i => (transferFin_posSemidef hβ w).eigenvalues_nonneg i) hμ0 ht htt' ha hC R x j hj
    hμj_pos h_decay

end Z2Gap
