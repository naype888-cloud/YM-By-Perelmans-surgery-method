/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import ClusterBound

/-!
# Kotecký–Preiss for non-negative weights: proved, not assumed

`ClusterBound.lean` only *defines* the Kotecký–Preiss condition.  This file proves its
consequences for `PolymerModel.polymerZ` when the weights are non-negative (the
strong-coupling Wilson case).

## Main results

* `polymerZ_insert`: `Z(Λ ∪ {γ}) = Z(Λ) + w(γ) · Z(Λ_γ)` for a symmetric compatibility.
* `polymerZ_union_le`: `Z(Λ ∪ B) ≤ Z(Λ) · exp (∑_{b ∈ B} w b)`.
* `ratio_le_exp_of_kp`: under `SatisfiesKoteckyPreiss`, `Z(Λ) ≤ Z(Λ_γ₀) · exp (a γ₀)`,
  uniformly in the volume `Λ`.
* `exp_neg_le_ratio`: `exp (-a γ₀) ≤ Z(Λ_γ₀) / Z(Λ) ≤ 1`.
* `log_polymerZ_le`: `0 ≤ log Z(Λ) ≤ ∑_{γ ∈ Λ} w γ`.
-/

open Finset

namespace PolymerModel

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {compat : Γ → Γ → Prop} [DecidableRel compat]

/-- `Z(∅) = 1`. -/
theorem polymerZ_empty (w : Γ → ℝ) : polymerZ compat w (∅ : Finset Γ) = 1 := by
  simp [polymerZ, Finset.filter_singleton, compatible_empty]

private theorem polymerZ_eq_sum (w : Γ → ℝ) (Λ : Finset Γ) :
    polymerZ compat w Λ =
      ∑ t ∈ Λ.powerset, if IsCompatible compat t then ∏ γ ∈ t, w γ else 0 := by
  unfold polymerZ
  rw [Finset.sum_filter]

/-- Insertion formula: `Z(Λ ∪ {γ}) = Z(Λ) + w(γ) · Z(Λ_γ)`. -/
theorem polymerZ_insert (hs : ∀ ⦃x y⦄, compat x y → compat y x) (w : Γ → ℝ) {a : Γ} {Λ : Finset Γ}
    (ha : a ∉ Λ) :
    polymerZ compat w (insert a Λ) =
      polymerZ compat w Λ + w a * polymerZ compat w (Λ.filter (compat a)) := by
  set F := Λ.filter (compat a) with hF
  have key : ∀ t ∈ Λ.powerset,
      (if IsCompatible compat (insert a t) then ∏ γ ∈ insert a t, w γ else 0) =
        if t ⊆ F then w a * (if IsCompatible compat t then ∏ γ ∈ t, w γ else 0) else 0 := by
    intro t ht
    have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
    rw [Finset.prod_insert hat]
    have hiff : IsCompatible compat (insert a t) ↔ (t ⊆ F ∧ IsCompatible compat t) := by
      constructor
      · intro h
        refine ⟨fun x hx => ?_, fun x y hx hy hxy =>
          h (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp ht hx,
          h (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hx) ?_⟩
        rintro rfl; exact hat hx
      · rintro ⟨hsub, hc⟩ x y hx hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact absurd rfl hxy
          · exact (Finset.mem_filter.mp (hsub hy')).2
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact hs (Finset.mem_filter.mp (hsub hx')).2
          · exact hc hx' hy' hxy
    by_cases h1 : t ⊆ F <;> by_cases h2 : IsCompatible compat t <;> simp [hiff, h1, h2]
  have hpow : Λ.powerset.filter (· ⊆ F) = F.powerset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans (Finset.filter_subset _ _), h⟩⟩
  have h2 : ∀ g : Finset Γ → ℝ,
      (∑ x ∈ Λ.powerset, if x ⊆ F then g x else 0) = ∑ x ∈ F.powerset, g x := by
    intro g
    rw [← Finset.sum_filter, hpow]
  simp only [polymerZ_eq_sum]
  rw [Finset.sum_powerset_insert ha, Finset.sum_congr rfl key,
    h2 (fun x => w a * if IsCompatible compat x then ∏ γ ∈ x, w γ else 0), ← Finset.mul_sum]

variable (w : Γ → ℝ) (hw : ∀ γ, 0 ≤ w γ)
include hw

/-- Monotonicity in the volume. -/
theorem polymerZ_mono {Λ Λ' : Finset Γ} (h : Λ ⊆ Λ') :
    polymerZ compat w Λ ≤ polymerZ compat w Λ' := by
  unfold polymerZ
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun S _ _ =>
    Finset.prod_nonneg fun γ _ => hw γ
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  exact ⟨hS.1.trans h, hS.2⟩

variable (hs : ∀ ⦃x y⦄, compat x y → compat y x)
include hs

/-- Adding one polymer multiplies `Z` by at most `1 + w`. -/
theorem polymerZ_insert_le {a : Γ} {Λ : Finset Γ} (ha : a ∉ Λ) :
    polymerZ compat w (insert a Λ) ≤ (1 + w a) * polymerZ compat w Λ := by
  rw [polymerZ_insert hs w ha]
  have h1 := polymerZ_mono w hw (compat := compat) (Finset.filter_subset (compat a) Λ)
  have := hw a
  nlinarith

/-- `Z(Λ ∪ B) ≤ Z(Λ) · exp (∑_{b ∈ B} w b)`. -/
theorem polymerZ_union_le (Λ B : Finset Γ) :
    polymerZ compat w (Λ ∪ B) ≤ polymerZ compat w Λ * Real.exp (∑ b ∈ B, w b) := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [Finset.sum_insert hb, Real.exp_add]
    have hZ : 0 ≤ polymerZ compat w Λ := by
      have := polymerZ_ge_one compat w hw ∅
      have h0 := polymerZ_mono w hw (compat := compat) (Finset.empty_subset Λ)
      rw [polymerZ_empty] at h0; linarith
    have hsum : 0 ≤ ∑ b ∈ B, w b := Finset.sum_nonneg fun i _ => hw i
    by_cases hbΛ : b ∈ Λ ∪ B
    · have : Λ ∪ insert b B = Λ ∪ B := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert] at hbΛ ⊢
        constructor
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact hbΛ
          · exact Or.inr h
        · rintro (h | h) <;> tauto
      rw [this]
      have h1 : 1 ≤ Real.exp (w b) := Real.one_le_exp (hw b)
      calc _ ≤ _ := ih
        _ ≤ _ := by
          have : 0 ≤ polymerZ compat w Λ * Real.exp (∑ b ∈ B, w b) :=
            mul_nonneg hZ (Real.exp_pos _).le
          nlinarith
    · have hins : Λ ∪ insert b B = insert b (Λ ∪ B) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [hins]
      calc _ ≤ (1 + w b) * polymerZ compat w (Λ ∪ B) := polymerZ_insert_le w hw hs hbΛ
        _ ≤ Real.exp (w b) * (polymerZ compat w Λ * Real.exp (∑ b ∈ B, w b)) := by
          apply mul_le_mul _ ih (by
            have := polymerZ_ge_one compat w hw (Λ ∪ B); linarith) (Real.exp_pos _).le
          linarith [Real.add_one_le_exp (w b)]
        _ = _ := by ring

omit [Fintype Γ] hs hw in
/-- A volume splits into the polymers compatible with `γ₀` and those that are not. -/
theorem split_volume (γ₀ : Γ) (Λ : Finset Γ) :
    Λ = Λ.filter (compat γ₀) ∪ Λ.filter (fun γ => ¬ compat γ₀ γ) := by
  rw [Finset.filter_union_filter_not_eq]

/-- **Kotecký–Preiss ratio bound (non-negative weights), uniform in the volume**:
`Z(Λ) ≤ Z(Λ_{γ₀}) · exp (a γ₀)`. -/
theorem ratio_le_exp_of_kp {a d : Γ → ℝ} (ha : ∀ γ, 0 ≤ a γ) (hd : ∀ γ, 0 ≤ d γ)
    (hkp : SatisfiesKoteckyPreiss compat w a d) (γ₀ : Γ) (Λ : Finset Γ) :
    polymerZ compat w Λ ≤
      polymerZ compat w (Λ.filter (compat γ₀)) * Real.exp (a γ₀) := by
  have h1 := polymerZ_union_le w hw hs (Λ.filter (compat γ₀)) (Λ.filter fun γ => ¬ compat γ₀ γ)
  rw [← split_volume γ₀ Λ] at h1
  refine h1.trans ?_
  have hZ : 0 ≤ polymerZ compat w (Λ.filter (compat γ₀)) :=
    (zero_le_one).trans (polymerZ_ge_one compat w hw _)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hZ
  calc ∑ b ∈ Λ.filter (fun γ => ¬ compat γ₀ γ), w b
      ≤ ∑ b ∈ Finset.univ.filter (fun γ => ¬ compat γ₀ γ), w b * Real.exp (a b + d b) := by
        calc _ ≤ ∑ b ∈ Λ.filter (fun γ => ¬ compat γ₀ γ), w b * Real.exp (a b + d b) :=
              Finset.sum_le_sum fun b _ => by
                have : 1 ≤ Real.exp (a b + d b) := Real.one_le_exp (add_nonneg (ha b) (hd b))
                nlinarith [hw b]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset_filter _ (Finset.subset_univ Λ))
                fun b _ _ => mul_nonneg (hw b) (Real.exp_pos _).le
    _ ≤ a γ₀ := hkp γ₀

/-- `exp (-a γ₀) ≤ Z(Λ_{γ₀}) / Z(Λ) ≤ 1`, uniformly in `Λ`. -/
theorem exp_neg_le_ratio {a d : Γ → ℝ} (ha : ∀ γ, 0 ≤ a γ) (hd : ∀ γ, 0 ≤ d γ)
    (hkp : SatisfiesKoteckyPreiss compat w a d) (γ₀ : Γ) (Λ : Finset Γ) :
    Real.exp (- a γ₀) ≤ polymerZ compat w (Λ.filter (compat γ₀)) / polymerZ compat w Λ ∧
      polymerZ compat w (Λ.filter (compat γ₀)) / polymerZ compat w Λ ≤ 1 := by
  have hpos : 0 < polymerZ compat w Λ :=
    lt_of_lt_of_le zero_lt_one (polymerZ_ge_one compat w hw Λ)
  constructor
  · rw [le_div_iff₀ hpos, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    simpa [mul_comm] using ratio_le_exp_of_kp w hw hs ha hd hkp γ₀ Λ
  · rw [div_le_one hpos]
    exact polymerZ_mono w hw (Finset.filter_subset _ _)

/-- `0 ≤ log Z(Λ) ≤ ∑_{γ ∈ Λ} w γ`. -/
theorem log_polymerZ_le (Λ : Finset Γ) :
    0 ≤ Real.log (polymerZ compat w Λ) ∧
      Real.log (polymerZ compat w Λ) ≤ ∑ γ ∈ Λ, w γ := by
  have hge := polymerZ_ge_one compat w hw Λ
  refine ⟨Real.log_nonneg hge, ?_⟩
  have h := polymerZ_union_le w hw hs (∅ : Finset Γ) Λ
  rw [Finset.empty_union, polymerZ_empty, one_mul] at h
  exact (Real.log_le_log (lt_of_lt_of_le zero_lt_one hge) h).trans (Real.log_exp _).le

end PolymerModel
