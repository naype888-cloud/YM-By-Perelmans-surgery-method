/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Current.Eigenstates
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
/-!

# The energies of the open tight binding cube are its whole spectrum

## i. Overview

The open chain of `N` sites has the standing waves `∑ n, sin ((n + 1) k π / (N + 1)) |n⟩` with
`k = 1, …, N`, of energy `E₀ - 2 t cos (k π / (N + 1))`. The Hamiltonian of the open cube is the
sum of the three chain Hamiltonians, each acting on its own axis. The products of three standing
waves are eigenstates of it with the sum of the three energies. They are nonzero and pairwise
orthogonal, there are `Nx Ny Nz` of them, which is the dimension of the Hilbert space of the
cube, so they are a basis. An eigenvector has a nonzero overlap with one of them, and since the
Hamiltonian is hermitian its eigenvalue is the energy of that product: there are no other
eigenvalues.

## ii. Key results

- `standingWave`, `openEnergy` : the standing waves of the open chain and their energies.
- `openHamiltonian_standingWave` : `H ψ_k = E_k ψ_k`.
- `hasEigenvalue_openHamiltonian_iff` : the eigenvalues of the open chain are exactly `E_k`.
- `cubeHamiltonian` : the Hamiltonian of the open cube.
- `cubeHamiltonian_cubeWave` : the product of three standing waves has the sum of the energies.
- `hasEigenvalue_cubeHamiltonian_iff` : the eigenvalues of the cube are exactly the sums
  `E_x + E_y + E_z`.

## iii. Table of contents

- A. The standing waves of the open chain
- B. The standing waves are a basis
- C. The spectrum of the open chain
- D. The Hamiltonian of the open cube
- E. The spectrum of the open cube

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter

/-!

## A. An orthogonal family of eigenvectors that fills the space gives the whole spectrum

-/

section Eigenbasis

open InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} [Fintype ι]

/-- **The eigenvalues of a hermitian operator with an orthogonal eigenbasis are exactly the
eigenvalues of the basis.** The vectors `e i` are nonzero, pairwise orthogonal and as many as the
dimension, so they span; an eigenvector has a nonzero overlap with one of them. -/
lemma hasEigenvalue_iff_of_orthogonal_eigenvectors {H : V →ₗ[ℂ] V} (hH : H.IsSymmetric)
    {e : ι → V} {lam : ι → ℝ} (he0 : ∀ i, e i ≠ 0)
    (horth : Pairwise fun i j => ⟪e i, e j⟫_ℂ = 0)
    (hcard : Fintype.card ι = Module.finrank ℂ V) (hHe : ∀ i, H (e i) = (lam i : ℂ) • e i)
    (μ : ℂ) : Module.End.HasEigenvalue H μ ↔ ∃ i, (lam i : ℂ) = μ := by
  have hli : LinearIndependent ℂ e := linearIndependent_of_ne_zero_of_inner_eq_zero he0
    fun _ _ h => horth h
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range e) :=
    le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hne : ∃ i, ⟪e i, v⟫_ℂ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hker : Submodule.span ℂ (Set.range e) ≤ LinearMap.ker (innerSL ℂ v).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          innerSL_apply_apply]
        rw [← inner_conj_symm, hcon i, map_zero]
      have := hker (hspan (Submodule.mem_top (x := v)))
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
        inner_self_eq_zero] at this
      exact hv.2 this
    obtain ⟨i, hi⟩ := hne
    refine ⟨i, ?_⟩
    have h1 : ⟪e i, H v⟫_ℂ = μ * ⟪e i, v⟫_ℂ := by
      rw [Module.End.mem_eigenspace_iff.mp hv.1, inner_smul_right]
    have h2 : ⟪e i, H v⟫_ℂ = lam i * ⟪e i, v⟫_ℂ := by
      rw [← hH, hHe i, inner_smul_left, Complex.conj_ofReal]
    exact (mul_right_cancel₀ hi (h2.symm.trans h1))
  · rintro ⟨i, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (hHe i), he0 i⟩

end Eigenbasis

namespace TightBindingChain
open InnerProductSpace
variable (T : TightBindingChain)

/-!

## B. The standing waves of the open chain

-/

/-- The angle `(k + 1) π / (N + 1)` of the `k`-th standing wave. -/
noncomputable def openAngle (k : Fin T.N) : ℝ := ((k : ℕ) + 1) * Real.pi / (T.N + 1)

/-- The standing wave `∑ n, sin ((n + 1) θ_k) |n⟩` of the open chain. -/
noncomputable def standingWave (k : Fin T.N) : T.HilbertSpace :=
  ∑ n : Fin T.N, ((Real.sin (((n : ℕ) + 1) * T.openAngle k) : ℝ) : ℂ) • |n⟩

/-- The energy `E₀ - 2 t cos θ_k` of the `k`-th standing wave. -/
noncomputable def openEnergy (k : Fin T.N) : ℝ := T.E0 - 2 * T.t * Real.cos (T.openAngle k)

/-- The amplitude of the standing wave on the site `m`. -/
lemma inner_standingWave (k m : Fin T.N) :
    ⟪|m⟩, T.standingWave k⟫_ℂ = ((Real.sin (((m : ℕ) + 1) * T.openAngle k) : ℝ) : ℂ) := by
  rw [standingWave, T.localizedState_orthonormal.inner_right_fintype]

/-- The standing wave vanishes just outside the chain: `sin ((N + 1) θ_k) = 0`. -/
lemma sin_openAngle_end (k : Fin T.N) :
    Real.sin (((T.N : ℝ) + 1) * T.openAngle k) = 0 := by
  unfold openAngle
  rw [mul_div_cancel₀ _ (by positivity)]
  exact_mod_cast Real.sin_nat_mul_pi ((k : ℕ) + 1)

/-- The sum over the sites of the amplitudes `sin ((n + 1) θ)` at `n = m + 1`: the amplitude at the
site `m + 1`, which vanishes just outside the chain. -/
private lemma sum_next (θ : ℝ) (hN : Real.sin (((T.N : ℝ) + 1) * θ) = 0) (m : Fin T.N) :
    ∑ n : Fin T.N, (if (m : ℕ) + 1 = n then ((Real.sin (((n : ℕ) + 1) * θ) : ℝ) : ℂ) else 0) =
      ((Real.sin (((m : ℕ) + 2) * θ) : ℝ) : ℂ) := by
  by_cases h : (m : ℕ) + 1 < T.N
  · rw [Finset.sum_eq_single ⟨(m : ℕ) + 1, h⟩]
    · simp only [↓reduceIte]
      push_cast
      ring_nf
    · intro b _ hb
      exact ite_eq_right_iff.mpr fun hb' => absurd (Fin.ext hb'.symm) hb
    · simp
  · rw [Finset.sum_eq_zero]
    · have h1 : ((m : ℕ) : ℝ) + 1 = (T.N : ℝ) := by exact_mod_cast (by omega : (m : ℕ) + 1 = T.N)
      have h2 : (((m : ℕ) : ℝ) + 2) = (T.N : ℝ) + 1 := by linarith
      rw [h2, hN]
      simp
    · intro b _
      exact ite_eq_right_iff.mpr fun hb' => absurd (hb' ▸ b.isLt) h

/-- The sum over the sites of the amplitudes at `n + 1 = m`: the amplitude at `m - 1`, which
vanishes just outside the chain. -/
private lemma sum_prev (θ : ℝ) (m : Fin T.N) :
    ∑ n : Fin T.N, (if (n : ℕ) + 1 = m then ((Real.sin (((n : ℕ) + 1) * θ) : ℝ) : ℂ) else 0) =
      ((Real.sin ((m : ℕ) * θ) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos (m : ℕ) with h | h
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro b _
      exact ite_eq_right_iff.mpr fun hb' => absurd hb' (by omega)
  · rw [Finset.sum_eq_single ⟨(m : ℕ) - 1, by omega⟩]
    · have hc : (m : ℕ) - 1 + 1 = m := by omega
      simp only [hc, ↓reduceIte]
      congr 3
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    · intro b _ hb
      exact ite_eq_right_iff.mpr fun hb' =>
        absurd (Fin.ext (by simp only []; omega)) hb
    · simp

/-- **The standing waves are eigenstates of the open chain**: `H ψ_k = E_k ψ_k`. -/
lemma openHamiltonian_standingWave (k : Fin T.N) :
    T.openHamiltonian (T.standingWave k) = (T.openEnergy k : ℂ) • T.standingWave k := by
  have hN := T.sin_openAngle_end k
  apply localizedState.repr.injective
  ext m
  simp only [OrthonormalBasis.repr_apply_apply]
  rw [inner_smul_right, inner_standingWave]
  simp only [standingWave, map_sum, map_smul, inner_sum, inner_smul_right,
    inner_openHamiltonian]
  have key (n : Fin T.N) : ((Real.sin (((n : ℕ) + 1) * T.openAngle k) : ℝ) : ℂ) *
      (if m = n then (T.E0 : ℂ)
        else if (m : ℕ) + 1 = n ∨ (n : ℕ) + 1 = m then -(T.t : ℂ) else 0) =
      (if m = n then (T.E0 : ℂ) * ((Real.sin (((n : ℕ) + 1) * T.openAngle k) : ℝ) : ℂ) else 0) +
      (-(T.t : ℂ)) * ((if (m : ℕ) + 1 = n then
        ((Real.sin (((n : ℕ) + 1) * T.openAngle k) : ℝ) : ℂ) else 0) +
      (if (n : ℕ) + 1 = m then
        ((Real.sin (((n : ℕ) + 1) * T.openAngle k) : ℝ) : ℂ) else 0)) := by
    by_cases h1 : m = n
    · subst h1
      have e1 : ¬ ((m : ℕ) + 1 = m) := by omega
      simp only [↓reduceIte, e1, add_zero]
      ring
    · by_cases h2 : (m : ℕ) + 1 = n
      · have e1 : ¬ ((n : ℕ) + 1 = m) := by omega
        simp only [h1, h2, e1, ↓reduceIte, true_or, zero_add]
        ring
      · by_cases h3 : (n : ℕ) + 1 = m
        · simp only [h1, h2, h3, ↓reduceIte, or_true, zero_add]
          ring
        · simp only [h1, h2, h3, or_self, ↓reduceIte, add_zero]
          ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, sum_next T _ hN,
    sum_prev, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  unfold openEnergy openAngle
  have hsum : Real.sin (((m : ℕ) + 2) * (((k : ℕ) + 1) * Real.pi / (T.N + 1))) +
      Real.sin ((m : ℕ) * (((k : ℕ) + 1) * Real.pi / (T.N + 1))) =
      2 * Real.cos (((k : ℕ) + 1) * Real.pi / (T.N + 1)) *
        Real.sin (((m : ℕ) + 1) * (((k : ℕ) + 1) * Real.pi / (T.N + 1))) := by
    generalize ((k : ℕ) + 1) * Real.pi / (T.N + 1) = θ
    have e1 : ((m : ℝ) + 2) * θ = ((m : ℝ) + 1) * θ + θ := by ring
    have e2 : (m : ℝ) * θ = ((m : ℝ) + 1) * θ - θ := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring
  have hsumC := congrArg (fun r : ℝ => (r : ℂ)) hsum
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] at hsumC
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (-(T.t : ℂ)) * hsumC

/-!

## C. The standing waves are a basis, and the spectrum of the open chain

-/

/-- The angles `θ_k` lie strictly between `0` and `π`. -/
lemma openAngle_mem (k : Fin T.N) : 0 < T.openAngle k ∧ T.openAngle k < Real.pi := by
  have hk : ((k : ℕ) : ℝ) + 1 < (T.N : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ k.isLt
  unfold openAngle
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- A standing wave is not zero: its amplitude on the first site is `sin θ_k > 0`. -/
lemma standingWave_ne_zero (k : Fin T.N) : T.standingWave k ≠ 0 := fun h => by
  have h0 := T.inner_standingWave k 0
  rw [h, inner_zero_right] at h0
  have hs : 0 < Real.sin ((((0 : Fin T.N) : ℕ) + 1) * T.openAngle k) := by
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul]
    exact Real.sin_pos_of_pos_of_lt_pi (T.openAngle_mem k).1 (T.openAngle_mem k).2
  exact hs.ne' (by exact_mod_cast h0.symm)

/-- Distinct standing waves have distinct energies, if the hopping does not vanish. -/
lemma openEnergy_injective (ht : T.t ≠ 0) : Function.Injective T.openEnergy := by
  intro j k h
  have hc : Real.cos (T.openAngle j) = Real.cos (T.openAngle k) := by
    unfold openEnergy at h
    have h2 : 2 * T.t * Real.cos (T.openAngle j) = 2 * T.t * Real.cos (T.openAngle k) := by
      linarith
    exact mul_left_cancel₀ (mul_ne_zero two_ne_zero ht) h2
  have hθ := Real.injOn_cos ⟨(T.openAngle_mem j).1.le, (T.openAngle_mem j).2.le⟩
    ⟨(T.openAngle_mem k).1.le, (T.openAngle_mem k).2.le⟩ hc
  unfold openAngle at hθ
  have hN : (0 : ℝ) < (T.N : ℝ) + 1 := by positivity
  have h3 : ((j : ℕ) : ℝ) + 1 = ((k : ℕ) : ℝ) + 1 := by
    have := Real.pi_pos
    field_simp at hθ
    nlinarith
  exact Fin.ext (by exact_mod_cast add_right_cancel h3)

/-- The standing waves of different energy are orthogonal: the Hamiltonian is hermitian. -/
lemma standingWave_orthogonal (ht : T.t ≠ 0) :
    Pairwise fun j k => ⟪T.standingWave j, T.standingWave k⟫_ℂ = 0 := by
  intro j k hjk
  have h := T.openHamiltonian_hermitian (T.standingWave j) (T.standingWave k)
  rw [openHamiltonian_standingWave, openHamiltonian_standingWave, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal] at h
  have hne : (T.openEnergy j : ℂ) ≠ T.openEnergy k := by
    exact_mod_cast fun h' => hjk (T.openEnergy_injective ht h')
  by_contra hc
  exact hne (mul_right_cancel₀ hc h)

/-- **The energies of the open chain are its whole spectrum**: `μ` is an eigenvalue of the
Hamiltonian of the open chain iff it is one of the energies `E₀ - 2 t cos (k π / (N + 1))`,
`k = 1, …, N`. -/
theorem hasEigenvalue_openHamiltonian_iff (ht : T.t ≠ 0) (μ : ℂ) :
    Module.End.HasEigenvalue T.openHamiltonian μ ↔ ∃ k : Fin T.N, (T.openEnergy k : ℂ) = μ :=
  hasEigenvalue_iff_of_orthogonal_eigenvectors (fun ψ φ => T.openHamiltonian_hermitian ψ φ)
    T.standingWave_ne_zero (T.standingWave_orthogonal ht)
    (by rw [Fintype.card_fin, T.finrank_hilbertSpace]) T.openHamiltonian_standingWave μ

/-!

## D. The Hamiltonian of the open cube

-/

open QuantumMechanics FiniteHilbertSpace

variable (Tx Ty Tz : TightBindingChain)

/-- The Hamiltonian of the open cube: the sum of the Hamiltonians of the three open chains, each
acting on its own axis. -/
noncomputable def cubeHamiltonian : Tx.CubeHilbertSpace Ty Tz →ₗ[ℂ] Tx.CubeHilbertSpace Ty Tz :=
  onFst (β := Fin Ty.N × Fin Tz.N) Tx.openHamiltonian +
    onSnd (α := Fin Tx.N) (onFst (β := Fin Tz.N) Ty.openHamiltonian) +
    onSnd (α := Fin Tx.N) (onSnd (α := Fin Ty.N) Tz.openHamiltonian)

/-- The Hamiltonian of the open cube is hermitian. -/
lemma cubeHamiltonian_isSymmetric : (cubeHamiltonian Tx Ty Tz).IsSymmetric :=
  ((onFst_isSymmetric (fun ψ φ => Tx.openHamiltonian_hermitian ψ φ)).add
    (onSnd_isSymmetric (onFst_isSymmetric (fun ψ φ => Ty.openHamiltonian_hermitian ψ φ)))).add
    (onSnd_isSymmetric (onSnd_isSymmetric (fun ψ φ => Tz.openHamiltonian_hermitian ψ φ)))

/-- The product of a standing wave on each axis. -/
noncomputable def cubeWave (k : Fin Tx.N × Fin Ty.N × Fin Tz.N) : Tx.CubeHilbertSpace Ty Tz :=
  prodVec (Tx.standingWave k.1) (prodVec (Ty.standingWave k.2.1) (Tz.standingWave k.2.2))

/-- The energy `E_x + E_y + E_z` of a product of standing waves. -/
noncomputable def cubeEnergy (k : Fin Tx.N × Fin Ty.N × Fin Tz.N) : ℝ :=
  Tx.openEnergy k.1 + Ty.openEnergy k.2.1 + Tz.openEnergy k.2.2

/-- **A product of three standing waves is an eigenstate of the cube** with the sum of the three
energies. -/
lemma cubeHamiltonian_cubeWave (k : Fin Tx.N × Fin Ty.N × Fin Tz.N) :
    cubeHamiltonian Tx Ty Tz (cubeWave Tx Ty Tz k) =
      (cubeEnergy Tx Ty Tz k : ℂ) • cubeWave Tx Ty Tz k := by
  simp only [cubeHamiltonian, cubeWave, cubeEnergy, LinearMap.add_apply, onFst_prodVec,
    onSnd_prodVec, openHamiltonian_standingWave, Complex.coe_smul, prodVec_smul_left,
    prodVec_smul_right, add_smul]

/-!

## E. The spectrum of the open cube

-/

/-- A product of standing waves is not zero. -/
lemma cubeWave_ne_zero (k : Fin Tx.N × Fin Ty.N × Fin Tz.N) : cubeWave Tx Ty Tz k ≠ 0 := by
  intro h
  have h1 : ⟪cubeWave Tx Ty Tz k, cubeWave Tx Ty Tz k⟫_ℂ = 0 := by rw [h, inner_zero_left]
  simp only [cubeWave, inner_prodVec] at h1
  have hx := (inner_self_ne_zero (𝕜 := ℂ)).2 (Tx.standingWave_ne_zero k.1)
  have hy := (inner_self_ne_zero (𝕜 := ℂ)).2 (Ty.standingWave_ne_zero k.2.1)
  have hz := (inner_self_ne_zero (𝕜 := ℂ)).2 (Tz.standingWave_ne_zero k.2.2)
  exact mul_ne_zero hx (mul_ne_zero hy hz) h1

/-- Different products of standing waves are orthogonal, if the three hoppings do not vanish. -/
lemma cubeWave_orthogonal (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0) :
    Pairwise fun j k => ⟪cubeWave Tx Ty Tz j, cubeWave Tx Ty Tz k⟫_ℂ = 0 := by
  intro j k hjk
  simp only [cubeWave, inner_prodVec]
  by_cases h1 : j.1 = k.1
  · by_cases h2 : j.2.1 = k.2.1
    · have h3 : j.2.2 ≠ k.2.2 := fun h3 => hjk (Prod.ext h1 (Prod.ext h2 h3))
      rw [Tz.standingWave_orthogonal hz h3]
      simp
    · rw [Ty.standingWave_orthogonal hy h2]
      simp
  · rw [Tx.standingWave_orthogonal hx h1]
    simp

/-- The dimension of the Hilbert space of the cube is `Nx Ny Nz`. -/
lemma finrank_cubeHilbertSpace :
    Module.finrank ℂ (Tx.CubeHilbertSpace Ty Tz) = Tx.N * Ty.N * Tz.N := by
  have := Module.finrank_eq_card_basis
    (QuantumMechanics.FiniteHilbertSpace.basisFun (Fin Tx.N × Fin Ty.N × Fin Tz.N)).toBasis
  simpa [mul_assoc] using this

/-- **The energies of the open cube are its whole spectrum**: `μ` is an eigenvalue of the
Hamiltonian of the open cube iff it is a sum `E_x + E_y + E_z` of one energy of each axis. -/
theorem hasEigenvalue_cubeHamiltonian_iff (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (μ : ℂ) :
    Module.End.HasEigenvalue (cubeHamiltonian Tx Ty Tz) μ ↔
      ∃ k : Fin Tx.N × Fin Ty.N × Fin Tz.N, (cubeEnergy Tx Ty Tz k : ℂ) = μ :=
  hasEigenvalue_iff_of_orthogonal_eigenvectors (cubeHamiltonian_isSymmetric Tx Ty Tz)
    (cubeWave_ne_zero Tx Ty Tz) (cubeWave_orthogonal Tx Ty Tz hx hy hz)
    (by rw [finrank_cubeHilbertSpace]; simp [mul_assoc]) (cubeHamiltonian_cubeWave Tx Ty Tz) μ

/-- **The cube of side `d`**: three copies of the same open chain of `d` sites. The eigenvalues
of the Hamiltonian on the `d³`-dimensional Hilbert space are exactly
`3 E₀ - 2 t (cos θ_a + cos θ_b + cos θ_c)` with `θ = k π / (d + 1)`, `k = 1, …, d`. -/
theorem hasEigenvalue_cubeHamiltonian_iff_same (T : TightBindingChain) (ht : T.t ≠ 0) (μ : ℂ) :
    Module.End.HasEigenvalue (cubeHamiltonian T T T) μ ↔
      ∃ a b c : Fin T.N, ((3 * T.E0 - 2 * T.t * (Real.cos (T.openAngle a) +
        Real.cos (T.openAngle b) + Real.cos (T.openAngle c)) : ℝ) : ℂ) = μ := by
  rw [hasEigenvalue_cubeHamiltonian_iff T T T ht ht ht]
  constructor
  · rintro ⟨⟨a, b, c⟩, h⟩
    refine ⟨a, b, c, ?_⟩
    rw [← h]
    simp only [cubeEnergy, openEnergy]
    congr 1
    ring
  · rintro ⟨a, b, c, h⟩
    refine ⟨⟨a, b, c⟩, ?_⟩
    rw [← h]
    simp only [cubeEnergy, openEnergy]
    congr 1
    ring

end TightBindingChain


#print axioms CondensedMatter.TightBindingChain.hasEigenvalue_cubeHamiltonian_iff
#print axioms CondensedMatter.TightBindingChain.hasEigenvalue_cubeHamiltonian_iff_same
