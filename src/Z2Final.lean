/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import Z2WilsonGap
import Z2Spectral
import AxialLoop
import TransferBridge
import AdjDegree

/-!
# A spectral gap of the `Z₂` transfer matrix from the area law

Wilson's `Z₂` model in the axial box. `T` is the transfer matrix of one time slice
(`Z2Wilson.Tm`, positive semidefinite, with positive entries), `μ₀` its largest eigenvalue, and
`x = F w` the loop row character `F` applied to the projection `w` of the boundary vector on the
top eigenspace. If `x` has a component on an eigenvector of positive eigenvalue `μ_j`, then

`R · log (t' / tanh β) ≤ log (μ₀ / μ_j)`.

The area law (`Z2Gauge.area_law_uniform`) is used uniformly in the time extent of the box, and the
transfer matrix is that of the box in axial gauge.

## Main results

- `Z2Final.z2_gap` : the inequality above.
-/

open Matrix Finset AreaBound SpectralGap

namespace Z2Final

variable (A C : ℕ)

/-- `rowChar` is `±1`: its square is `1`. -/
lemma rowChar_mul_self (R : ℕ) (k₀ : Fin (C + 1)) (s : LS A C → ZMod 2) :
    rowChar A C R k₀ s * rowChar A C R k₀ s = 1 := by
  unfold rowChar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  unfold Z2Transfer.sgn
  split_ifs <;> norm_num

lemma diag_dot {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (w z : ι → ℝ) :
    w ⬝ᵥ (diagonal d *ᵥ z) = (diagonal d *ᵥ w) ⬝ᵥ z := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring


lemma reindex_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n) (d : ι → ℝ) :
    SlabFin.reindexFin e (diagonal d) = diagonal (d ∘ e.symm) := by
  unfold SlabFin.reindexFin
  exact Matrix.submatrix_diagonal_equiv d e.symm

/-- The transfer matrix of one slice is positive semidefinite (on `Fin n`). -/
noncomputable def hPSDf (β : ℝ) (hβ : 0 ≤ β) : (Z2WilsonGap.Tfin A C β).PosSemidef :=
  SlabFin.reindex_posSemidef (Z2WilsonGap.eqv A C) (Z2Wilson.Tm_posSemidef A C hβ)

instance instNonemptyFin : Nonempty (Fin (Fintype.card (Z2WilsonGap.Idx A C))) :=
  ⟨Z2WilsonGap.eqv A C (fun _ => 0)⟩

/-- The largest eigenvalue of the transfer matrix. -/
noncomputable def lam0 (β : ℝ) (hβ : 0 ≤ β) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (hPSDf A C β hβ).1.eigenvalues

open Classical in
/-- The eigenvectors of the largest eigenvalue. -/
noncomputable def topSet (β : ℝ) (hβ : 0 ≤ β) : Finset (Fin (Fintype.card (Z2WilsonGap.Idx A C))) :=
  Finset.univ.filter fun j => (hPSDf A C β hβ).1.eigenvalues j = lam0 A C β hβ

/-- The loop row character applied to the projection of the boundary vector on the top
eigenspace. -/
noncomputable def xvec (β : ℝ) (hβ : 0 ≤ β) (R : ℕ) (k₀ : Fin (C + 1)) :
    Fin (Fintype.card (Z2WilsonGap.Idx A C)) → ℝ :=
  diagonal (rowChar A C R k₀ ∘ (Z2WilsonGap.eqv A C).symm) *ᵥ
    Z2Spectral.proj (hPSDf A C β hβ).1 (Z2WilsonGap.vfin A C β) (topSet A C β hβ)


open Classical in
/-- **The decay of `x ⬝ T^k x`** for `x = F w`, from the area law, for every `k`. -/
theorem decay (β : ℝ) (hβ : 0 < β) {Δ : ℕ}
    (hdeg : ∀ (B : ℕ) (p : CPlaq A B C), (Finset.univ.filter (Z2Gauge.Adj (cinc A B C) p)).card ≤ Δ)
    {t' a : ℝ} (htt' : Real.tanh β ≤ t') (ht' : 0 < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ Δ ≤ a) (R : ℕ) (hR : R ≤ A) (k₀ : Fin (C + 1))
    (hμ0 : 0 < lam0 A C β hβ.le) (k : ℕ) :
    xvec A C β hβ.le R k₀ ⬝ᵥ ((Z2WilsonGap.Tfin A C β ^ k) *ᵥ xvec A C β hβ.le R k₀) ≤
      (1 + a) ^ (8 * R) * ((Real.tanh β / t') ^ R) ^ k *
        (lam0 A C β hβ.le ^ k * (xvec A C β hβ.le R k₀ ⬝ᵥ xvec A C β hβ.le R k₀)) := by
  have hβ' : 0 ≤ β := hβ.le
  set hPSD := hPSDf A C β hβ' with hPSDdef
  set hT := hPSD.1 with hTdef
  set lam := lam0 A C β hβ' with hlam
  set e := Z2WilsonGap.eqv A C with he
  set Tf := Z2WilsonGap.Tfin A C β with hTf
  set S := topSet A C β hβ' with hS
  set w := Z2Spectral.proj hT (Z2WilsonGap.vfin A C β) S with hw
  set F' : Matrix _ _ ℝ := SlabFin.reindexFin e (diagonal (rowChar A C R k₀)) with hF'
  have hmax : ∀ j, hT.eigenvalues j ≤ lam := fun j =>
    Finset.le_sup' (f := hT.eigenvalues) (Finset.mem_univ j)
  have hlaw' := fun N : ℕ => Z2WilsonGap.hlaw A C β hβ' hdeg htt' ht' ha hta R k hR k₀
    (fun N => boundary_rectAx_eq_cLoop A (2 * N + k) C R k N (by omega) k₀) N
  have hl := SlabLimit.top_limit hT hPSD.eigenvalues_nonneg hμ0 hmax (F' * Tf ^ k * F')
    (Z2WilsonGap.vfin A C β) ((Real.tanh β / t') ^ (R * k) * (1 + a) ^ (8 * R)) k hlaw'
  have hSeq : (Finset.univ.filter fun j => hT.eigenvalues j = lam) = S := rfl
  rw [hSeq, ← Z2Spectral.top_quad hT _ (Z2WilsonGap.vfin A C β) S,
    ← Z2Spectral.top_sq hT (Z2WilsonGap.vfin A C β) S] at hl
  have hd : F' = diagonal (rowChar A C R k₀ ∘ e.symm) := reindex_diag e _
  have hxdef : xvec A C β hβ' R k₀ = F' *ᵥ w := by
    rw [hd]; rfl
  have e1 : w ⬝ᵥ ((F' * Tf ^ k * F') *ᵥ w) =
      (F' *ᵥ w) ⬝ᵥ ((Tf ^ k) *ᵥ (F' *ᵥ w)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hd, diag_dot]
  have e2 : (F' *ᵥ w) ⬝ᵥ (F' *ᵥ w) = w ⬝ᵥ w := by
    rw [hd, ← diag_dot, Matrix.mulVec_mulVec, diagonal_mul_diagonal]
    have : (fun i => (rowChar A C R k₀ ∘ e.symm) i * (rowChar A C R k₀ ∘ e.symm) i) = fun _ => 1 :=
      funext fun i => rowChar_mul_self A C R k₀ _
    rw [this]
    simp
  rw [hxdef, e2]
  rw [e1] at hl
  calc _ ≤ ((Real.tanh β / t') ^ (R * k) * (1 + a) ^ (8 * R)) * lam ^ k * (w ⬝ᵥ w) := hl
    _ = _ := by rw [pow_mul]; ring


/-- The largest eigenvalue of the transfer matrix is positive. -/
theorem lam0_pos (β : ℝ) (hβ : 0 ≤ β) : 0 < lam0 A C β hβ := by
  set hPSD := hPSDf A C β hβ with hPSDdef
  set hT := hPSD.1 with hTdef
  set lam := lam0 A C β hβ with hlam
  have hmax : ∀ j, hT.eigenvalues j ≤ lam := fun j =>
    Finset.le_sup' (f := hT.eigenvalues) (Finset.mem_univ j)
  have hvpos : ∀ i, 0 < Z2WilsonGap.vfin A C β i := fun i =>
    Real.sqrt_pos.mpr (Z2Wilson.uW_pos A C β _)
  have hTpos : ∀ i j, 0 < Z2WilsonGap.Tfin A C β i j := fun i j => by
    simp only [Z2WilsonGap.Tfin, SlabFin.reindexFin, Matrix.submatrix_apply]
    exact Z2Wilson.Tm_pos A C β _ _
  have hq : 0 < Z2WilsonGap.vfin A C β ⬝ᵥ (Z2WilsonGap.Tfin A C β *ᵥ Z2WilsonGap.vfin A C β) := by
    simp only [dotProduct, mulVec]
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    refine mul_pos (hvpos i) (Finset.sum_pos (fun j _ => ?_) Finset.univ_nonempty)
    exact mul_pos (hTpos i j) (hvpos j)
  have hxx : 0 < Z2WilsonGap.vfin A C β ⬝ᵥ Z2WilsonGap.vfin A C β := by
    simp only [dotProduct]
    exact Finset.sum_pos (fun i _ => mul_pos (hvpos i) (hvpos i)) Finset.univ_nonempty
  have hr := PerronOverlap.rayleigh_le hT hmax (Z2WilsonGap.vfin A C β)
  by_contra h
  push Not at h
  nlinarith


open Classical in
/-- **A spectral gap of the `Z₂` transfer matrix from the area law.** If `x = F w` has a component
on an eigenvector of positive eigenvalue `μ_j`, then `R · log (t' / tanh β) ≤ log (μ₀ / μ_j)`. -/
theorem z2_gap (β : ℝ) (hβ : 0 < β) {Δ : ℕ}
    (hdeg : ∀ (B : ℕ) (p : CPlaq A B C), (Finset.univ.filter (Z2Gauge.Adj (cinc A B C) p)).card ≤ Δ)
    {t' a : ℝ} (htt' : Real.tanh β < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ Δ ≤ a) (R : ℕ) (hR : R ≤ A) (k₀ : Fin (C + 1))
    (j : Fin (Fintype.card (Z2WilsonGap.Idx A C)))
    (hj : coeff (hPSDf A C β hβ.le).1 j (xvec A C β hβ.le R k₀) ≠ 0)
    (hμj : 0 < (hPSDf A C β hβ.le).1.eigenvalues j) :
    (R : ℝ) * Real.log (t' / Real.tanh β) ≤
      Real.log (lam0 A C β hβ.le / (hPSDf A C β hβ.le).1.eigenvalues j) := by
  have ht : 0 < Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβ) (Real.cosh_pos β)
  have ht' : 0 < t' := ht.trans htt'
  have hμ0 := lam0_pos A C β hβ.le
  have hdec := fun k => decay A C β hβ hdeg htt'.le ht' ha hta R hR k₀ hμ0 k
  have hC : 0 ≤ (1 + a) ^ (8 * R) := by positivity
  have h := TransferBridge.transfer_spectral_gap_wilson (hPSDf A C β hβ.le).1
    (hPSDf A C β hβ.le).eigenvalues_nonneg (a := 0) hμ0 ht htt' le_rfl hC R
    (xvec A C β hβ.le R k₀) j hj hμj (by
      intro k
      have := hdec k
      simpa using this)
  simpa using h


/-- **Theorem: `z2_gap_twelve`**: with the plaquette adjacency degree bounded by `12`
as a theorem (`AreaBound.adj_degree_le_twelve`), the degree condition is discharged. -/
theorem z2_gap_twelve (β : ℝ) (hβ : 0 < β)
    {t' a : ℝ} (htt' : Real.tanh β < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ 12 ≤ a) (R : ℕ) (hR : R ≤ A) (k₀ : Fin (C + 1))
    (j : Fin (Fintype.card (Z2WilsonGap.Idx A C)))
    (hj : coeff (hPSDf A C β hβ.le).1 j (xvec A C β hβ.le R k₀) ≠ 0)
    (hμj : 0 < (hPSDf A C β hβ.le).1.eigenvalues j) :
    (R : ℝ) * Real.log (t' / Real.tanh β) ≤
      Real.log (lam0 A C β hβ.le / (hPSDf A C β hβ.le).1.eigenvalues j) :=
  z2_gap A C β hβ (fun B p => AreaBound.adj_degree_le_twelve A B C p) htt' ha hta R hR k₀ j hj hμj

end Z2Final

