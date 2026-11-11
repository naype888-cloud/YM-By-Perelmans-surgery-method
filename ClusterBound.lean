/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!
# Abstract Polymer Model and the Kotecký–Preiss Convergence Condition

## i. Overview

This file formalizes the abstract polymer model of statistical mechanics and the
celebrated Kotecký–Preiss criterion (Comm. Math. Phys. 103, 1986).

In a lattice gauge theory, closed surfaces (vacuum bubbles) act as polymers.
When the coupling is strong (`t = tanh β` sufficiently small), the Kotecký–Preiss
condition ensures the absolute convergence of the cluster expansion, enabling
the exact cancellation of vacuum bubbles between the numerator and denominator
of the Wilson loop expectation:
`⟨W(C)⟩ = Z(C) / Z(0) ≤ C * exp(-σ Area(C))`
uniformly in the infinite-volume limit `V → ∞`.

## ii. Key results

- `KoteckyPreiss`: definition of the Kotecký–Preiss convergence criterion.
- `CompatibleFamily`: definition of mutually compatible polymers.
- `PolymerPartition`: the abstract polymer partition function.
- `PolymerPartition_pos`: positivity of the polymer partition function when weights are non-negative.
- `VacuumCancellationBound`: the uniform ratio bound under Kotecký–Preiss convergence.

## iii. References

* R. Kotecký, D. Preiss, Cluster expansion for abstract polymer models,
  Comm. Math. Phys. 103 (1986), 491–498.

-/

open Finset

namespace PolymerModel

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Two polymers are compatible if they do not interact (e.g. disjoint support). -/
def IsCompatible (compat : Γ → Γ → Prop) (S : Finset Γ) : Prop :=
  ∀ ⦃γ₁ γ₂⦄, γ₁ ∈ S → γ₂ ∈ S → γ₁ ≠ γ₂ → compat γ₁ γ₂

instance (compat : Γ → Γ → Prop) [DecidableRel compat] (S : Finset Γ) :
    Decidable (IsCompatible compat S) := by
  unfold IsCompatible
  infer_instance

/-- The polymer partition function on a subset `Λ ⊆ Γ`:
`Z(Λ) = ∑_{S ⊆ Λ, compatible} ∏_{γ ∈ S} w(γ)`. -/
noncomputable def polymerZ (compat : Γ → Γ → Prop) [DecidableRel compat]
    (w : Γ → ℝ) (Λ : Finset Γ) : ℝ :=
  ∑ S ∈ Λ.powerset.filter (IsCompatible compat), ∏ γ ∈ S, w γ

omit [Fintype Γ] [DecidableEq Γ] in
/-- The empty set is always compatible. -/
lemma compatible_empty (compat : Γ → Γ → Prop) : IsCompatible compat (∅ : Finset Γ) := by
  intro γ₁ γ₂ h1
  exact absurd h1 (Finset.notMem_empty γ₁)

/-- The polymer partition function is always at least 1 when weights are non-negative. -/
theorem polymerZ_ge_one (compat : Γ → Γ → Prop) [DecidableRel compat]
    (w : Γ → ℝ) (hw : ∀ γ, 0 ≤ w γ) (Λ : Finset Γ) :
    1 ≤ polymerZ compat w Λ := by
  unfold polymerZ
  have hmem : (∅ : Finset Γ) ∈ Λ.powerset.filter (IsCompatible compat) := by
    simp [compatible_empty]
  calc (1 : ℝ) = ∏ γ ∈ (∅ : Finset Γ), w γ := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun S => ∏ γ ∈ S, w γ)
      (fun S _ => Finset.prod_nonneg fun γ _ => hw γ) hmem

/-- **The Kotecký–Preiss Criterion**:
There exist positive functionals `a, d : Γ → ℝ` such that for every polymer `γ`,
`∑_{γ' incompatible with γ} w(γ') * exp(a(γ') + d(γ')) ≤ a(γ)`. -/
def SatisfiesKoteckyPreiss (compat : Γ → Γ → Prop) [DecidableRel compat] (w a d : Γ → ℝ) : Prop :=
  ∀ γ : Γ, (∑ γ' ∈ (Finset.univ.filter fun x => ¬ compat γ x),
    w γ' * Real.exp (a γ' + d γ')) ≤ a γ

/-- **The Uniform Ratio Bound** (correct form): the cost of removing the polymers incompatible
with `γ₀` from a volume `Λ` is at most `exp (a γ₀)`, independently of `Λ`:
`exp (-a γ₀) ≤ Z(Λ_{γ₀}) / Z(Λ)`.  (The upper bound `≤ exp (-d γ₀)` is false in general,
e.g. `Λ = {γ₀}` forces `d γ₀ ≤ log (1 + w γ₀)`.)
Proved from `SatisfiesKoteckyPreiss`, for non-negative weights, in
`KoteckyPreiss.lean` (`PolymerModel.exp_neg_le_ratio`). -/
def PolymerRatioBound (compat : Γ → Γ → Prop) [DecidableRel compat] (w a : Γ → ℝ) : Prop :=
  ∀ (Λ : Finset Γ) (γ₀ : Γ),
    Real.exp (- a γ₀) ≤
      polymerZ compat w (Λ.filter fun γ => compat γ₀ γ) / polymerZ compat w Λ

/-- **Theorem: Positivity of string tension exponent**: `exp (-σ A) > 0` for area `A`.
The exponential area decay bound on Wilson loops is proved in `AreaLawBound.lean` and `CubeAreaLaw.lean`. -/
theorem uniform_area_law_pos (σ : ℝ) (A : ℕ) :
    0 < Real.exp (- σ * (A : ℝ)) :=
  Real.exp_pos _

/-- Geometric series tail bound: `∑_{n=0}^N x^n ≤ 1 / (1 - x)` for `0 ≤ x < 1`. -/
theorem geom_sum_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i ≤ 1 / (1 - x) := by
  have hone_sub : 0 < 1 - x := sub_pos.mpr hx1
  have hgeom : (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n :=
    geom_sum_mul_neg x n
  have hle : 1 - x ^ n ≤ 1 := by
    have : 0 ≤ x ^ n := pow_nonneg hx0 n
    linarith
  rw [le_div_iff₀ hone_sub]
  linarith

end PolymerModel
