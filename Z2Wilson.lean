/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import AxialSlab
import AxialSeeds
import AxialArea
import SlabInsert
import SlabFin
import SlabLimit
import PerronOverlap
import Z2Gap

/-!
# From the area law of the axial box to the decay of `x ⬝ T^k x`

For the box `A × (2N + k) × C` in axial gauge and the loop of `R` columns at the times `N` and
`N + k`, the Euclidean Wilson loop is a matrix element of the symmetric transfer matrix
`T = D^{1/2} K_β D^{1/2}` (`AxialSlab.numerator_slice`, `SlabInsert.chain_two_insertions`), and the
area law (`Z2Gauge.area_law_uniform`, with the area bound `AreaBound.area_bound_rectAx` and at most
`8R` seeds) bounds it uniformly in `N`.

## Main results

- `Z2Wilson.numerator_matrix` : the numerator is `v ⬝ (T^N F T^k F T^N) v`, `F = diag (rowChar)`.

## Scope

The boundary of `rectAx` is identified with the two-row loop `cLoop` by a hypothesis `hloop`.
-/

open Matrix Finset AreaBound

namespace Z2Wilson

variable (A C : ℕ)

lemma uW_pos (β : ℝ) (s : LS A C → ZMod 2) : 0 < uW A C β s := by
  unfold uW
  exact Finset.prod_pos fun _ _ => Real.exp_pos _

/-- The symmetric transfer matrix of the axial `Z₂` box. -/
noncomputable def Tm (β : ℝ) : Matrix (LS A C → ZMod 2) (LS A C → ZMod 2) ℝ :=
  SlabChain.transferSym (Z2Transfer.K β) (uW A C β)

/-- The boundary vector `√u`. -/
noncomputable def vec (β : ℝ) : (LS A C → ZMod 2) → ℝ := fun i => Real.sqrt (uW A C β i)

/-- **The numerator of the Wilson loop is a matrix element.** -/
theorem numerator_matrix (β : ℝ) (N k R : ℕ) (k₀ : Fin (C + 1)) :
    ∑ σ : ALink A (2 * N + k) C → ZMod 2, Z2Gauge.weight (ainc A (2 * N + k) C) β σ *
        Z2Gauge.spin (∑ l, cLoop A (2 * N + k) C R k₀ ⟨N, by omega⟩ ⟨N + k, by omega⟩ l * σ l) =
      vec A C β ⬝ᵥ (((Tm A C β ^ N * diagonal (rowChar A C R k₀) * Tm A C β ^ k *
        diagonal (rowChar A C R k₀) * Tm A C β ^ N)) *ᵥ vec A C β) := by
  rw [numerator_slice A (2 * N + k) C β R k₀ ⟨N, by omega⟩ ⟨N + k, by omega⟩]
  exact SlabInsert.chain_two_insertions (M := Z2Transfer.K β) (u := uW A C β)
    (fun i => (uW_pos A C β i).le) (rowChar A C R k₀) (rowChar A C R k₀) N k N (2 * N + k)
    (by omega)

lemma partition_pos (B : ℕ) (β : ℝ) : 0 < Z2Gauge.partition (ainc A B C) β := by
  unfold Z2Gauge.partition
  refine Finset.sum_pos (fun σ _ => ?_) Finset.univ_nonempty
  unfold Z2Gauge.weight
  exact Finset.prod_pos fun _ _ => Real.exp_pos _

open Classical in
/-- **The area law bounds the numerator, uniformly in `N`.** -/
theorem numerator_le (β : ℝ) (hβ : 0 ≤ β) {Δ : ℕ}
    (hdeg : ∀ (B : ℕ) (p : CPlaq A B C), (Finset.univ.filter (Z2Gauge.Adj (cinc A B C) p)).card ≤ Δ)
    {t' a : ℝ} (htt' : Real.tanh β ≤ t') (ht' : 0 < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ Δ ≤ a) (R k : ℕ) (hR : R ≤ A) (k₀ : Fin (C + 1))
    (hloop : ∀ N : ℕ, Z2Gauge.boundary (ainc A (2 * N + k) C) (rectAx A (2 * N + k) C R k N k₀) =
      cLoop A (2 * N + k) C R k₀ ⟨N, by omega⟩ ⟨N + k, by omega⟩) (N : ℕ) :
    ∑ σ : ALink A (2 * N + k) C → ZMod 2, Z2Gauge.weight (ainc A (2 * N + k) C) β σ *
        Z2Gauge.spin (∑ l, cLoop A (2 * N + k) C R k₀ ⟨N, by omega⟩ ⟨N + k, by omega⟩ l * σ l) ≤
      ((Real.tanh β / t') ^ (R * k) * (1 + a) ^ (8 * R)) *
        Z2Gauge.partition (ainc A (2 * N + k) C) β := by
  set B := 2 * N + k with hB
  have hdeg' : ∀ p : CPlaq A B C,
      (Finset.univ.filter (Z2Gauge.Adj (ainc A B C) p)).card ≤ Δ := fun p =>
    le_trans (Finset.card_le_card fun q hq =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, adj_ainc A B C (Finset.mem_filter.mp hq).2⟩)
      (hdeg B p)
  have hmin : ∀ γ : Finset (CPlaq A B C),
      Z2Gauge.boundary (ainc A B C) γ = Z2Gauge.boundary (ainc A B C) (rectAx A B C R k N k₀) →
        R * k ≤ γ.card := fun γ h =>
    area_bound_rectAx A B C R k N hR (by omega) k₀ h
  have hal := Z2Gauge.area_law_uniform hdeg' hβ htt' ht' ha hta (rectAx A B C R k N k₀) hmin
  have hseed := seeds_rectAx_card_le A B C R k N (by omega) k₀
  have h1a : (1 : ℝ) ≤ 1 + a := by linarith
  have hpow : (1 + a) ^ (Finset.univ.filter (Z2Gauge.IsSeed (ainc A B C)
      (Z2Gauge.boundary (ainc A B C) (rectAx A B C R k N k₀)))).card ≤ (1 + a) ^ (8 * R) :=
    pow_le_pow_right₀ h1a hseed
  have hD : 0 ≤ (Real.tanh β / t') ^ (R * k) := by
    have : 0 ≤ Real.tanh β := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos β).le
    exact pow_nonneg (div_nonneg this ht'.le) _
  have hW : Z2Gauge.wilsonExpect (ainc A B C) β (rectAx A B C R k N k₀) ≤
      (Real.tanh β / t') ^ (R * k) * (1 + a) ^ (8 * R) :=
    hal.trans (mul_le_mul_of_nonneg_left hpow hD)
  unfold Z2Gauge.wilsonExpect at hW
  rw [hloop N] at hW
  have hpos := partition_pos A C B β
  exact (div_le_iff₀ hpos).mp hW

end Z2Wilson
