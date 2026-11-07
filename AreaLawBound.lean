/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import TreeBound

/-!

# The area law of a Z₂ gauge theory at strong coupling, uniform in the volume

## i. Overview

Combining `PolymerBound.lean` (`⟨W(C)⟩` is at most the weighted number of surfaces attached to the
loop) and `TreeBound.lean` (that weighted number is at most `(1 + a)^{#seeds}`), with the lower bound
`|γ| ≥ m` on the area of every surface bounded by the loop, one gets for `t ≤ t'`
`⟨W(C)⟩ ≤ (t / t')^m · (1 + a)^{#seeds}`
whenever every plaquette is adjacent to at most `Δ` others and `t' (1 + a)^Δ ≤ a`. For a loop of
perimeter `P` and area `m`, the number of seeds is at most a constant times `P`: the bound is an
area law, with string tension at least `log (t' / t)` up to a perimeter term, and it does not
depend on the volume.

The hypotheses are all local (the degree `Δ` of the adjacency, the minimal area `m`). The group is
`ℤ/2`, abelian: this is not the Yang–Mills mass gap.

## ii. Key results

- `Z2Gauge.ratio_le_attached` : `N(C) / Z ≤ ∑_{γ attached} t^|γ|` for `t ≥ 0`.
- `Z2Gauge.attached_sum_le` : `∑_{γ attached} t^|γ| ≤ (t / t')^m (1 + a)^{#seeds}`.
- `Z2Gauge.area_law_uniform` : `⟨W(∂S₀)⟩ ≤ (tanh β / t')^m (1 + a)^{#seeds}`.

## iii. Table of contents

- A. The bound by the attached surfaces
- B. The decay in the area

## iv. References

* K. Osterwalder, E. Seiler, Gauge field theories on a lattice, Ann. Phys. 110 (1978).

-/

open Finset

namespace Z2Gauge

set_option linter.unusedSectionVars false

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
variable {inc : P → L → ZMod 2}

/-! ## A. The bound by the attached surfaces -/

/-- For `t ≥ 0`, `N(C) / Z ≤ ∑_{γ attached to C} t^|γ|`. -/
theorem ratio_le_attached {t : ℝ} (ht : 0 ≤ t) (C : L → ZMod 2) :
    highTempSum inc t C / highTempSum inc t 0 ≤ ∑ γ ∈ attachedSets inc C, t ^ γ.card := by
  have hZ : 0 < highTempSum inc t 0 := lt_of_lt_of_le one_pos (one_le_highTempSum_zero inc ht)
  rw [div_le_iff₀ hZ]
  exact numerator_le ht C

/-! ## B. The decay in the area -/

open Classical in
/-- **The attached surfaces weigh at most `(t / t')^m (1 + a)^{#seeds}`**: with every plaquette
adjacent to at most `Δ` others, `t ≤ t'`, `t' (1 + a)^Δ ≤ a` and every attached surface of at least
`m` plaquettes. -/
theorem attached_sum_le {Δ : ℕ} (hdeg : ∀ p : P, (univ.filter (Adj inc p)).card ≤ Δ) {t t' a : ℝ}
    (ht : 0 ≤ t) (htt' : t ≤ t') (ht' : 0 < t') (ha : 0 ≤ a) (hta : t' * (1 + a) ^ Δ ≤ a)
    (C : L → ZMod 2) {m : ℕ} (hmin : ∀ γ ∈ attachedSets inc C, m ≤ γ.card) :
    ∑ γ ∈ attachedSets inc C, t ^ γ.card ≤
      (t / t') ^ m * (1 + a) ^ (univ.filter (IsSeed inc C)).card := by
  have hq0 : 0 ≤ t / t' := div_nonneg ht ht'.le
  have hq1 : t / t' ≤ 1 := (div_le_one ht').mpr htt'
  have hstep : ∀ γ ∈ attachedSets inc C, t ^ γ.card ≤ (t / t') ^ m * t' ^ γ.card := by
    intro γ hγ
    have h1 : t ^ γ.card = (t / t') ^ γ.card * t' ^ γ.card := by
      rw [← mul_pow, div_mul_cancel₀ _ ht'.ne']
    rw [h1]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 (hmin γ hγ))
      (pow_nonneg ht'.le _)
  have hsub : attachedSets inc C ⊆
      (Finset.univ : Finset P).powerset.filter (Rooted inc (univ.filter (IsSeed inc C))) := by
    intro γ hγ
    simp only [attachedSets, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, Rooted, Finset.mem_univ] at hγ ⊢
    intro p hp
    obtain ⟨q, hq, hseed, hr⟩ := hγ.2 p hp
    exact ⟨q, hq, hseed, hr⟩
  calc ∑ γ ∈ attachedSets inc C, t ^ γ.card
      ≤ ∑ γ ∈ attachedSets inc C, (t / t') ^ m * t' ^ γ.card := sum_le_sum hstep
    _ = (t / t') ^ m * ∑ γ ∈ attachedSets inc C, t' ^ γ.card := by rw [Finset.mul_sum]
    _ ≤ (t / t') ^ m * rootedSum inc t' Finset.univ (univ.filter (IsSeed inc C)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 _)
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg ht'.le _
    _ ≤ (t / t') ^ m * (1 + a) ^ (univ.filter (IsSeed inc C)).card :=
        mul_le_mul_of_nonneg_left
          (rootedSum_le hdeg ht'.le ha hta _ Finset.univ _ rfl (Finset.subset_univ _))
          (pow_nonneg hq0 _)

open Classical in
/-- **The area law of the Z₂ gauge theory at strong coupling, uniform in the volume.** With `C = ∂S₀`
and every surface bounded by `C` having at least `m` plaquettes:
`⟨W(C)⟩ ≤ (tanh β / t')^m (1 + a)^{#seeds}`. -/
theorem area_law_uniform {Δ : ℕ} (hdeg : ∀ p : P, (univ.filter (Adj inc p)).card ≤ Δ) {β t' a : ℝ}
    (hβ : 0 ≤ β) (htt' : Real.tanh β ≤ t') (ht' : 0 < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ Δ ≤ a) (S₀ : Finset P) {m : ℕ}
    (hmin : ∀ γ : Finset P, boundary inc γ = boundary inc S₀ → m ≤ γ.card) :
    wilsonExpect inc β S₀ ≤
      (Real.tanh β / t') ^ m * (1 + a) ^ (univ.filter (IsSeed inc (boundary inc S₀))).card := by
  have ht : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos β).le
  rw [wilsonExpect_highTemp]
  refine (ratio_le_attached ht _).trans ?_
  refine attached_sum_le hdeg ht htt' ht' ha hta _ (fun γ hγ => hmin γ ?_)
  simp only [attachedSets, Finset.mem_filter] at hγ
  exact hγ.2.1

end Z2Gauge
