/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import Z2Wilson

/-!
# The `Fin n` side: transfer matrix decay theorem from the area law

The transfer matrix of `Z2Wilson` lives on configurations of one time slice. Here it is reindexed
by `Fin n` (`SlabFin`), where `SpectralGap`, `SlabLimit` and `PerronOverlap` work, and the bound
of `Z2Wilson.numerator_le` establishes the theorem
`(T^N v) ⬝ (F T^k F) (T^N v) ≤ D_k · v ⬝ T^{2N+k} v` for `SlabLimit.top_limit`.

## Main results

- `Z2WilsonGap.hlaw` : Theorem establishing the transfer matrix decay bound for `Tfin` and `vfin`
  from the axial box area law.
-/

open Matrix Finset AreaBound

namespace Z2WilsonGap

variable (A C : ℕ)

/-- The index type of the configurations of one time slice. -/
abbrev Idx := LS A C → ZMod 2

/-- The enumeration of the configurations of one slice. -/
noncomputable def eqv : Idx A C ≃ Fin (Fintype.card (Idx A C)) := Fintype.equivFin _

/-- The transfer matrix, indexed by `Fin n`. -/
noncomputable def Tfin (β : ℝ) : Matrix (Fin (Fintype.card (Idx A C))) (Fin (Fintype.card (Idx A C))) ℝ :=
  SlabFin.reindexFin (eqv A C) (Z2Wilson.Tm A C β)

/-- The boundary vector, indexed by `Fin n`. -/
noncomputable def vfin (β : ℝ) : Fin (Fintype.card (Idx A C)) → ℝ :=
  Z2Wilson.vec A C β ∘ (eqv A C).symm

lemma reindex_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    (X Y : Matrix ι ι ℝ) :
    SlabFin.reindexFin e (X * Y) = SlabFin.reindexFin e X * SlabFin.reindexFin e Y := by
  unfold SlabFin.reindexFin
  rw [Matrix.submatrix_mul_equiv]

lemma mulVec_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    (Y : Matrix ι ι ℝ) (w : ι → ℝ) :
    SlabFin.reindexFin e Y *ᵥ (w ∘ e.symm) = (Y *ᵥ w) ∘ e.symm := by
  funext a
  simp only [SlabFin.reindexFin, mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun b => rfl)

lemma Tm_isSymm {β : ℝ} (hβ : 0 ≤ β) : (Z2Wilson.Tm A C β)ᵀ = Z2Wilson.Tm A C β := by
  have h := (Z2Wilson.Tm_posSemidef A C hβ).1
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h.eq


lemma symm_dot {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) (z y : Idx A C → ℝ) :
    ((Z2Wilson.Tm A C β ^ m) *ᵥ z) ⬝ᵥ y = z ⬝ᵥ ((Z2Wilson.Tm A C β ^ m) *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec]
  have hs : (Z2Wilson.Tm A C β ^ m)ᵀ = Z2Wilson.Tm A C β ^ m := by
    rw [Matrix.transpose_pow, Tm_isSymm A C hβ]
  rw [← Matrix.vecMul_transpose, hs]

open Classical in
/-- **Theorem: Transfer matrix decay bound**, proved from the area law of the axial box. -/
theorem hlaw (β : ℝ) (hβ : 0 ≤ β) {Δ : ℕ}
    (hdeg : ∀ (B : ℕ) (p : CPlaq A B C), (Finset.univ.filter (Z2Gauge.Adj (cinc A B C) p)).card ≤ Δ)
    {t' a : ℝ} (htt' : Real.tanh β ≤ t') (ht' : 0 < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ Δ ≤ a) (R k : ℕ) (hR : R ≤ A) (k₀ : Fin (C + 1))
    (hloop : ∀ N : ℕ, Z2Gauge.boundary (ainc A (2 * N + k) C) (rectAx A (2 * N + k) C R k N k₀) =
      cLoop A (2 * N + k) C R k₀ ⟨N, by omega⟩ ⟨N + k, by omega⟩) (N : ℕ) :
    ((Tfin A C β ^ N) *ᵥ vfin A C β) ⬝ᵥ
        (((SlabFin.reindexFin (eqv A C) (diagonal (rowChar A C R k₀))) * Tfin A C β ^ k *
          (SlabFin.reindexFin (eqv A C) (diagonal (rowChar A C R k₀)))) *ᵥ
          ((Tfin A C β ^ N) *ᵥ vfin A C β)) ≤
      ((Real.tanh β / t') ^ (R * k) * (1 + a) ^ (8 * R)) *
        (vfin A C β ⬝ᵥ ((Tfin A C β ^ (2 * N + k)) *ᵥ vfin A C β)) := by
  set e := eqv A C with he
  set T := Z2Wilson.Tm A C β with hT
  set v := Z2Wilson.vec A C β with hv
  set F : Matrix (Idx A C) (Idx A C) ℝ := diagonal (rowChar A C R k₀) with hF
  have hpow : ∀ m : ℕ, Tfin A C β ^ m = SlabFin.reindexFin e (T ^ m) := fun m =>
    SlabFin.reindex_pow e T m
  have hY : SlabFin.reindexFin e F * Tfin A C β ^ k * SlabFin.reindexFin e F =
      SlabFin.reindexFin e (F * T ^ k * F) := by
    rw [hpow k, reindex_mul, reindex_mul]
  have hL : ((Tfin A C β ^ N) *ᵥ vfin A C β) ⬝ᵥ
      (((SlabFin.reindexFin e F) * Tfin A C β ^ k * (SlabFin.reindexFin e F)) *ᵥ
        ((Tfin A C β ^ N) *ᵥ vfin A C β)) =
      v ⬝ᵥ ((T ^ N * F * T ^ k * F * T ^ N) *ᵥ v) := by
    rw [hY, hpow N]
    unfold vfin
    rw [mulVec_reindex, SlabFin.dotProduct_reindex, symm_dot A C hβ N,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rfl
  have hR' : vfin A C β ⬝ᵥ ((Tfin A C β ^ (2 * N + k)) *ᵥ vfin A C β) =
      v ⬝ᵥ ((T ^ (2 * N + k)) *ᵥ v) := by
    rw [hpow]
    unfold vfin
    exact SlabFin.dotProduct_reindex e _ v v
  rw [hL, hR', ← Z2Wilson.numerator_matrix A C β N k R k₀]
  have hpart : Z2Gauge.partition (ainc A (2 * N + k) C) β = v ⬝ᵥ ((T ^ (2 * N + k)) *ᵥ v) := by
    rw [partition_slice]
    exact SlabChain.chainSum_eq_transfer (Z2Transfer.K β) (fun i => (Z2Wilson.uW_pos A C β i).le) _
  rw [← hpart]
  exact Z2Wilson.numerator_le A C β hβ hdeg htt' ht' ha hta R k hR k₀ hloop N

end Z2WilsonGap
