/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import Z2Final

/-!
# The Overlap Theorem and Spectral Gap of the `Z₂` Transfer Matrix (`z2_gap_free`)

For `β > 0` the kernel `K` of Wilson's `Z₂` model is positive definite: it is the Kronecker
product, one factor per link, of the `2 × 2` matrix `[[e^β, e^-β], [e^-β, e^β]]`.

This file establishes that the overlap condition `hj` holds unconditionally as a proven theorem
(`Z2Hj.exists_excited`), yielding the transfer matrix spectral gap theorem
without open hypotheses (`Z2Hj.z2_gap_free`).

## Main results

- `Z2Hj.blockMat_posDef` : the `2 × 2` factor is positive definite for `β > 0`.
- `Z2Hj.K_posDef` : the kernel `K` is positive definite for `β > 0`.
- `Z2Hj.transfer_posDef` : the transfer matrix `D^{1/2} K D^{1/2}` is positive definite for `β > 0`.
- `Z2Hj.exists_excited` : **The Overlap Theorem**, proving that an excited eigenvector with positive
  eigenvalue has a non-zero overlap with the loop vector.
- `Z2Hj.z2_gap_free` : **The Spectral Gap Theorem**, establishing the transfer matrix spectral gap
  unconditionally for strong coupling as a theorem.
-/

open Matrix Z2Transfer Kronecker

namespace Z2Hj

/-- The `2 × 2` factor of the kernel: one link. -/
noncomputable def blockMat (β : ℝ) : Matrix (ZMod 2) (ZMod 2) ℝ :=
  fun a b => Real.exp (β * (sgn a * sgn b))

lemma blockMat_apply (β : ℝ) (a b : ZMod 2) :
    blockMat β a b = Real.sinh β * (sgn a * sgn b) + Real.cosh β := exp_sgn β a b

lemma sum_zmod2 (f : ZMod 2 → ℝ) : ∑ a, f a = f 0 + f 1 := by
  have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [this, Finset.sum_pair (by decide)]

theorem blockMat_posDef {β : ℝ} (hβ : 0 < β) : (blockMat β).PosDef := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hs := Real.sinh_pos_iff.mpr hβ
  have hc := Real.cosh_pos β
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext a b
    simp only [conjTranspose_apply, blockMat, star_trivial]
    rw [mul_comm (sgn b)]
  · have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hx (funext fun a => ?_)
      have key : a = 0 ∨ a = 1 := by revert a; decide
      rcases key with rfl | rfl
      · exact hcon.1
      · exact hcon.2
    simp only [star_trivial, dotProduct, mulVec, sum_zmod2, blockMat_apply]
    simp only [sgn, ite_true, h10, ite_false]
    have h : Real.sinh β * (x 0 - x 1) ^ 2 + Real.cosh β * (x 0 + x 1) ^ 2 > 0 := by
      by_cases h0 : x 0 - x 1 = 0
      · have : x 0 + x 1 ≠ 0 := by
          intro h1
          rcases hne with h2 | h2 <;> apply h2 <;> linarith
        have : 0 < (x 0 + x 1) ^ 2 := by positivity
        nlinarith [mul_pos hc this, sq_nonneg (x 0 - x 1), mul_nonneg hs.le (sq_nonneg (x 0 - x 1))]
      · have : 0 < (x 0 - x 1) ^ 2 := by positivity
        nlinarith [mul_pos hs this, sq_nonneg (x 0 + x 1), mul_nonneg hc.le (sq_nonneg (x 0 + x 1))]
    nlinarith [h]


section induction

variable {n : ℕ}

/-- Split off the first link. -/
def headTail (σ : Fin (n + 1) → ZMod 2) : ZMod 2 × (Fin n → ZMod 2) := (σ 0, Fin.tail σ)

lemma headTail_injective : Function.Injective (headTail (n := n)) := by
  intro σ τ h
  have h0 : σ 0 = τ 0 := congrArg Prod.fst h
  have h1 : Fin.tail σ = Fin.tail τ := congrArg Prod.snd h
  funext i
  refine Fin.cases h0 (fun j => ?_) i
  exact congrFun h1 j

/-- The kernel on `n + 1` links is the Kronecker product of one link with the kernel on `n`. -/
lemma K_succ (β : ℝ) :
    K (L := Fin (n + 1)) β =
      (blockMat β ⊗ₖ K (L := Fin n) β).submatrix headTail headTail := by
  ext σ σ'
  simp only [K, kern, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, blockMat, headTail,
    Fin.prod_univ_succ]
  rfl

/-- **The kernel on `n` links is positive definite** for `β > 0`. -/
theorem K_fin_posDef {β : ℝ} (hβ : 0 < β) : ∀ n : ℕ, (K (L := Fin n) β).PosDef
  | 0 => by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨K_isHermitian β, fun x hx => ?_⟩
    have : Unique (Fin 0 → ZMod 2) := Pi.uniqueOfIsEmpty _
    obtain ⟨σ0, hσ0⟩ : ∃ σ0, x σ0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext hcon)
    have h1 : ∀ σ σ' : Fin 0 → ZMod 2, K (L := Fin 0) β σ σ' = 1 := fun σ σ' => by
      simp [K, kern]
    have hs : ∀ f : (Fin 0 → ZMod 2) → ℝ, ∑ σ, f σ = f σ0 := fun f =>
      Fintype.sum_eq_single σ0 fun σ h => absurd (Subsingleton.elim σ σ0) h
    simp only [star_trivial, dotProduct, mulVec, hs, h1]
    have : 0 < x σ0 ^ 2 := by positivity
    nlinarith
  | n + 1 => by
    rw [K_succ]
    exact ((blockMat_posDef hβ).kronecker (K_fin_posDef hβ n)).submatrix headTail_injective

end induction

section general

variable {L : Type*} [Fintype L]

/-- **The kernel `K` is positive definite** for `β > 0`: a Kronecker product, one factor per link. -/
theorem K_posDef {β : ℝ} (hβ : 0 < β) : (K (L := L) β).PosDef := by
  let e := Fintype.equivFin L
  have hK : K (L := L) β = (K (L := Fin (Fintype.card L)) β).submatrix
      (fun σ => σ ∘ e.symm) (fun σ => σ ∘ e.symm) := by
    ext σ σ'
    simp only [K, kern, Matrix.submatrix_apply, Function.comp_apply]
    exact Fintype.prod_equiv e _ _ fun l => by simp
  rw [hK]
  refine (K_fin_posDef hβ _).submatrix fun σ τ h => ?_
  funext l
  have := congrFun h (e l)
  simpa using this

end general

section transfer

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- **The transfer matrix `D^{1/2} K D^{1/2}` is positive definite** for `β > 0` and a positive
weight. -/
theorem transfer_posDef {β : ℝ} (hβ : 0 < β) {w : (L → ZMod 2) → ℝ} (hw : ∀ σ, 0 < w σ) :
    (transfer β w).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨(transfer_posSemidef hβ.le w).1, fun x hx => ?_⟩
  set d : (L → ZMod 2) → ℝ := fun σ => Real.sqrt (w σ) with hd
  have hdpos : ∀ σ, 0 < d σ := fun σ => Real.sqrt_pos.mpr (hw σ)
  have hy : diagonal d *ᵥ x ≠ 0 := by
    intro h
    refine hx (funext fun σ => ?_)
    have := congrFun h σ
    simp only [mulVec_diagonal, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (hdpos σ).ne'
  have hq := K_posDef (L := L) hβ
  rw [posDef_iff_dotProduct_mulVec] at hq
  have h1 := hq.2 hy
  have h2 : x ⬝ᵥ (transfer β w *ᵥ x) =
      (diagonal d *ᵥ x) ⬝ᵥ (K β *ᵥ (diagonal d *ᵥ x)) := by
    unfold transfer
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Z2Final.diag_dot]
  rw [star_trivial] at h1 ⊢
  rw [h2]
  exact h1

end transfer

section final

open SpectralGap Finset AreaBound

variable (A C : ℕ)

/-- The transfer matrix of one slice of the `Z₂` box is positive definite for `β > 0`. -/
theorem Tm_posDef {β : ℝ} (hβ : 0 < β) : (Z2Wilson.Tm A C β).PosDef :=
  transfer_posDef hβ fun σ => Z2Wilson.uW_pos A C β σ

theorem Tfin_posDef {β : ℝ} (hβ : 0 < β) : (Z2WilsonGap.Tfin A C β).PosDef :=
  (Tm_posDef A C hβ).submatrix (Z2WilsonGap.eqv A C).symm.injective

/-- Every eigenvalue of the transfer matrix is positive. -/
theorem eigenvalues_pos {β : ℝ} (hβ : 0 < β) (j : Fin (Fintype.card (Z2WilsonGap.Idx A C))) :
    0 < (Z2Final.hPSDf A C β hβ.le).1.eigenvalues j :=
  (Tfin_posDef A C hβ).eigenvalues_pos j

/-- The loop vector `x = F w` is not zero. -/
theorem xvec_ne_zero {β : ℝ} (hβ : 0 < β) (R : ℕ) (k₀ : Fin (C + 1)) :
    Z2Final.xvec A C β hβ.le R k₀ ≠ 0 := by
  set hPSD := Z2Final.hPSDf A C β hβ.le with hPSDdef
  set hT := hPSD.1 with hTdef
  set S := Z2Final.topSet A C β hβ.le with hS
  set w := Z2Spectral.proj hT (Z2WilsonGap.vfin A C β) S with hw
  have hvpos : ∀ i, 0 < Z2WilsonGap.vfin A C β i := fun i =>
    Real.sqrt_pos.mpr (Z2Wilson.uW_pos A C β _)
  have hTpos : ∀ i j, 0 ≤ Z2WilsonGap.Tfin A C β i j := fun i j => by
    simp only [Z2WilsonGap.Tfin, SlabFin.reindexFin, Matrix.submatrix_apply]
    exact (Z2Wilson.Tm_pos A C β _ _).le
  have hmax : ∀ j, hT.eigenvalues j ≤ Z2Final.lam0 A C β hβ.le := fun j =>
    Finset.le_sup' (f := hT.eigenvalues) (Finset.mem_univ j)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (Fintype.card
    (Z2WilsonGap.Idx A C)))) hT.eigenvalues
  obtain ⟨j, hjmax, hjc⟩ := PerronOverlap.top_overlap hT hTpos hmax ⟨j0, hj0.symm⟩
    (Z2WilsonGap.vfin A C β) hvpos
  have hjS : j ∈ S := by
    simp [hS, Z2Final.topSet, hjmax]
  have hww : 0 < w ⬝ᵥ w := by
    rw [hw, Z2Spectral.top_sq]
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, hjS, by positivity⟩
  intro h0
  have hx : Z2Final.xvec A C β hβ.le R k₀ ⬝ᵥ Z2Final.xvec A C β hβ.le R k₀ = w ⬝ᵥ w := by
    unfold Z2Final.xvec
    rw [← hw, ← Z2Final.diag_dot, Matrix.mulVec_mulVec, diagonal_mul_diagonal]
    have : (fun i => (rowChar A C R k₀ ∘ (Z2WilsonGap.eqv A C).symm) i *
        (rowChar A C R k₀ ∘ (Z2WilsonGap.eqv A C).symm) i) = fun _ => 1 :=
      funext fun i => Z2Final.rowChar_mul_self A C R k₀ _
    rw [this]
    simp
  rw [h0] at hx
  simp at hx
  linarith

/-- **Theorem: The overlap condition holds**: some eigenvector of positive eigenvalue has a non-zero component of the loop vector. -/
theorem exists_excited {β : ℝ} (hβ : 0 < β) (R : ℕ) (k₀ : Fin (C + 1)) :
    ∃ j, 0 < (Z2Final.hPSDf A C β hβ.le).1.eigenvalues j ∧
      coeff (Z2Final.hPSDf A C β hβ.le).1 j (Z2Final.xvec A C β hβ.le R k₀) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ j, coeff (Z2Final.hPSDf A C β hβ.le).1 j (Z2Final.xvec A C β hβ.le R k₀) = 0 :=
    fun j => hcon j (eigenvalues_pos A C hβ j)
  have hs := sum_coeff_sq (Z2Final.hPSDf A C β hβ.le).1 (Z2Final.xvec A C β hβ.le R k₀)
  simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero] at hs
  exact xvec_ne_zero A C hβ R k₀ (dotProduct_self_eq_zero.mp hs.symm)

/-- **Theorem: Spectral gap of the `Z₂` transfer matrix**: unconditional spectral gap for strong
coupling, establishing `R · log (t' / tanh β) ≤ log (μ₀ / μ_j)`. -/
theorem z2_gap_free {β : ℝ} (hβ : 0 < β) {t' a : ℝ} (htt' : Real.tanh β < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ 12 ≤ a) (R : ℕ) (hR : R ≤ A) (k₀ : Fin (C + 1)) :
    ∃ j, 0 < (Z2Final.hPSDf A C β hβ.le).1.eigenvalues j ∧
      (R : ℝ) * Real.log (t' / Real.tanh β) ≤
        Real.log (Z2Final.lam0 A C β hβ.le / (Z2Final.hPSDf A C β hβ.le).1.eigenvalues j) := by
  obtain ⟨j, hμ, hj⟩ := exists_excited A C hβ R k₀
  exact ⟨j, hμ, Z2Final.z2_gap_twelve A C β hβ htt' ha hta R hR k₀ j hj hμ⟩

end final

end Z2Hj
