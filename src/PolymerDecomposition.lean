/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import PolymerBound
import KoteckyPreiss

/-!
# The Z2 partition function is a polymer partition function

For the high temperature expansion of `Z2AreaLaw.lean`, `Z = ∑_{∂S = 0} t^|S|`.  A closed surface
`S` splits uniquely into its connected components (connected through shared links); each
component is closed, and different components share no link.  Hence `Z = polymerZ` for the
polymer model whose polymers are the non-empty, closed, connected sets of plaquettes, compatible
when they share no link, with weight `t^|γ|`.

## Main results

- `Z2Gauge.highTempSum_zero_eq_polymerZ` :
  `highTempSum inc t 0 = polymerZ (Compat inc) (polyWeight inc t) univ`.

This makes `KoteckyPreiss.lean` (`ratio_le_exp_of_kp`, `exp_neg_le_ratio`, `log_polymerZ_le`)
applicable to the Z2 gauge partition function, for `t ≥ 0`.
-/

open Finset PolymerModel

set_option linter.unusedSectionVars false

namespace Z2Gauge

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
variable (inc : P → L → ZMod 2)

/-- A set of plaquettes is connected if any two of its plaquettes are reachable inside it. -/
def Conn (γ : Finset P) : Prop := ∀ p ∈ γ, ∀ q ∈ γ, ReachIn inc γ p q

/-- A polymer: non-empty, closed (`∂γ = 0`) and connected. -/
def ValidPolymer (γ : Finset P) : Prop := γ.Nonempty ∧ boundary inc γ = 0 ∧ Conn inc γ

/-- Two polymers are compatible if their plaquettes are distinct and share no link. -/
def Compat (γ γ' : Finset P) : Prop :=
  ∀ p ∈ γ, ∀ q ∈ γ', p ≠ q ∧ ∀ l, inc p l = 0 ∨ inc q l = 0

open Classical in
/-- The polymer weight `t^|γ|` on valid polymers, `0` otherwise. -/
noncomputable def polyWeight (t : ℝ) (γ : Finset P) : ℝ :=
  if ValidPolymer inc γ then t ^ γ.card else 0

variable {inc}

lemma adj_symm {p q : P} (h : Adj inc p q) : Adj inc q p :=
  ⟨h.1.symm, by obtain ⟨l, h1, h2⟩ := h.2; exact ⟨l, h2, h1⟩⟩

lemma compat_symm {γ γ' : Finset P} (h : Compat inc γ γ') : Compat inc γ' γ :=
  fun q hq p hp => ⟨(h p hp q hq).1.symm, fun l => ((h p hp q hq).2 l).symm⟩

lemma reach_symm {S : Finset P} {p q : P} (h : ReachIn inc S p q) : ReachIn inc S q p :=
  by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    exact (Relation.ReflTransGen.single ⟨hs.2.1, hs.1, adj_symm hs.2.2⟩).trans ih

lemma reach_mem {S : Finset P} {p q : P} (hp : p ∈ S) (h : ReachIn inc S p q) : q ∈ S := by
  induction h with
  | refl => exact hp
  | tail _ hs _ => exact hs.2.1

lemma reach_mono {S S' : Finset P} (hS : S ⊆ S') {p q : P} (h : ReachIn inc S p q) :
    ReachIn inc S' p q :=
  by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ⟨hS hs.1, hS hs.2.1, hs.2.2⟩

/-- Inside a subset closed under adjacency (within `S`), reachability in `S` is reachability in
the subset. -/
lemma reach_restrict {S T : Finset P} (hT : ∀ x ∈ T, ∀ y ∈ S, Adj inc x y → y ∈ T)
    {x y : P} (hx : x ∈ T) (h : ReachIn inc S x y) : ReachIn inc T x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxz hs ih =>
    rename_i z w
    have hzT : z ∈ T := reach_mem hx ih
    exact ih.tail ⟨hzT, hT z hzT w hs.2.1 hs.2.2, hs.2.2⟩

/-! ## A. A compatible family of polymers: its members are the components of its union -/

section Family

variable {F : Finset (Finset P)} (hF : ∀ γ ∈ F, ValidPolymer inc γ)
  (hC : ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → Compat inc γ γ')
include hF hC

lemma family_reach_iff {γ : Finset P} (hγ : γ ∈ F) {p q : P} (hp : p ∈ γ)
    (hq : q ∈ F.biUnion id) : ReachIn inc (F.biUnion id) p q ↔ q ∈ γ := by
  constructor
  · intro h
    revert hq
    induction h with
    | refl => intro _; exact hp
    | tail hxz hs ih =>
      rename_i z w
      intro _
      have ih' := ih hs.1
      obtain ⟨γ', hγ', hwγ'⟩ := Finset.mem_biUnion.mp hs.2.1
      by_cases hg : γ = γ'
      · exact hg ▸ hwγ'
      · obtain ⟨_, hl⟩ := hC γ hγ γ' hγ' hg z ih' w (by simpa using hwγ')
        obtain ⟨l, h1, h2⟩ := hs.2.2.2
        rcases hl l with h | h
        · exact absurd h h1
        · exact absurd h h2
  · intro hqγ
    exact reach_mono (fun x hx => Finset.mem_biUnion.mpr ⟨γ, hγ, hx⟩)
      ((hF γ hγ).2.2 p hp q hqγ)

lemma family_boundary : boundary inc (F.biUnion id) = 0 := by
  funext l
  have hdisj : (F : Set (Finset P)).PairwiseDisjoint id := by
    intro γ hγ γ' hγ' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    exact (hC γ hγ γ' hγ' hne p hp p hp').1 rfl
  unfold boundary
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun γ hγ => ?_
  have := congrFun (hF γ hγ).2.1 l
  simpa [boundary] using this

end Family

/-! ## B. A closed surface: its components -/

open Classical in
/-- The component of `p` in `S`. -/
noncomputable def comp (inc : P → L → ZMod 2) (S : Finset P) (p : P) : Finset P :=
  S.filter (ReachIn inc S p)

lemma mem_comp {S : Finset P} {p q : P} : q ∈ comp inc S p ↔ q ∈ S ∧ ReachIn inc S p q := by
  simp [comp]

lemma comp_closed {S : Finset P} {p : P} :
    ∀ x ∈ comp inc S p, ∀ y ∈ S, Adj inc x y → y ∈ comp inc S p := by
  intro x hx y hy hadj
  obtain ⟨hxS, hr⟩ := mem_comp.mp hx
  exact mem_comp.mpr ⟨hy, hr.tail ⟨hxS, hy, hadj⟩⟩

lemma comp_nolink {S : Finset P} {p x y : P} (hx : x ∈ comp inc S p) (hy : y ∈ S)
    (hn : y ∉ comp inc S p) (l : L) : inc x l = 0 ∨ inc y l = 0 := by
  by_contra h
  push Not at h
  exact hn (comp_closed x hx y hy ⟨fun e => hn (e ▸ hx), l, h.1, h.2⟩)

lemma comp_boundary {S : Finset P} (hS : boundary inc S = 0) (p : P) :
    boundary inc (comp inc S p) = 0 := by
  classical
  funext l
  have hsub : comp inc S p ⊆ S := fun q hq => (mem_comp.mp hq).1
  have hsplit : boundary inc S l =
      boundary inc (comp inc S p) l + ∑ y ∈ S.filter (· ∉ comp inc S p), inc y l := by
    unfold boundary
    rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ comp inc S p)]
    congr 1
    have : S.filter (· ∈ comp inc S p) = comp inc S p := by
      ext q; simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [this]
  by_cases hex : ∃ x ∈ comp inc S p, inc x l ≠ 0
  · obtain ⟨x, hx, hxl⟩ := hex
    have hz : ∑ y ∈ S.filter (· ∉ comp inc S p), inc y l = 0 :=
      Finset.sum_eq_zero fun y hy => by
        obtain ⟨hyS, hyn⟩ := Finset.mem_filter.mp hy
        rcases comp_nolink hx hyS hyn l with h | h
        · exact absurd h hxl
        · exact h
    have := congrFun hS l
    rw [hsplit, hz, add_zero] at this
    simpa using this
  · push Not at hex
    simp only [boundary, Pi.zero_apply]
    exact Finset.sum_eq_zero hex

lemma comp_conn {S : Finset P} (p : P) : Conn inc (comp inc S p) := by
  intro x hx y hy
  obtain ⟨hxS, hrx⟩ := mem_comp.mp hx
  obtain ⟨hyS, hry⟩ := mem_comp.mp hy
  exact reach_restrict comp_closed hx ((reach_symm hrx).trans hry)

lemma comp_valid {S : Finset P} (hS : boundary inc S = 0) {p : P} (hp : p ∈ S) :
    ValidPolymer inc (comp inc S p) :=
  ⟨⟨p, mem_comp.mpr ⟨hp, Relation.ReflTransGen.refl⟩⟩, comp_boundary hS p, comp_conn p⟩

lemma comp_eq_of_mem {S : Finset P} {p q : P} (hq : q ∈ comp inc S p) :
    comp inc S q = comp inc S p := by
  obtain ⟨hqS, hr⟩ := mem_comp.mp hq
  ext x
  simp only [mem_comp]
  constructor
  · rintro ⟨hx, h⟩; exact ⟨hx, hr.trans h⟩
  · rintro ⟨hx, h⟩; exact ⟨hx, (reach_symm hr).trans h⟩

lemma comp_compat {S : Finset P} {p q : P}
    (hne : comp inc S p ≠ comp inc S q) :
    Compat inc (comp inc S p) (comp inc S q) := by
  intro x hx y hy
  have hyS : y ∈ S := (mem_comp.mp hy).1
  have hyn : y ∉ comp inc S p := fun h =>
    hne ((comp_eq_of_mem h).symm.trans (comp_eq_of_mem hy))
  exact ⟨fun e => hyn (e ▸ hx), comp_nolink hx hyS hyn⟩

/-- A member of a compatible family is the component of any of its plaquettes in the union. -/
lemma family_eq_comp {F : Finset (Finset P)} (hF : ∀ γ ∈ F, ValidPolymer inc γ)
    (hC : ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → Compat inc γ γ') {γ : Finset P} (hγ : γ ∈ F) {p : P}
    (hp : p ∈ γ) : γ = comp inc (F.biUnion id) p := by
  ext q
  rw [mem_comp]
  constructor
  · intro hq
    exact ⟨Finset.mem_biUnion.mpr ⟨γ, hγ, hq⟩,
      (family_reach_iff hF hC hγ hp (Finset.mem_biUnion.mpr ⟨γ, hγ, hq⟩)).mpr hq⟩
  · rintro ⟨hq, hr⟩
    exact (family_reach_iff hF hC hγ hp hq).mp hr

/-! ## C. The decomposition -/

open Classical in
/-- **`Z = polymerZ`**: the Z2 high temperature partition function is the polymer partition
function of the closed connected surfaces, compatible when they share no link. -/
theorem highTempSum_zero_eq_polymerZ (t : ℝ) :
    highTempSum inc t 0 =
      polymerZ (Compat inc) (polyWeight inc t) (Finset.univ : Finset (Finset P)) := by
  unfold highTempSum polymerZ
  symm
  refine Finset.sum_bij_ne_zero (fun F _ _ => F.biUnion id) ?_ ?_ ?_ ?_
  · -- the union is a closed surface
    intro F hF hne
    have hvalid : ∀ γ ∈ F, ValidPolymer inc γ := by
      intro γ hγ
      have h1 := (Finset.prod_ne_zero_iff.mp hne) γ hγ
      by_contra hv
      exact h1 (by simp [polyWeight, hv])
    have hcomp : ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → Compat inc γ γ' := fun γ hγ γ' hγ' h =>
      (Finset.mem_filter.mp hF).2 hγ hγ' h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      family_boundary hvalid hcomp⟩
  · -- injectivity
    intro F₁ h₁ n₁ F₂ h₂ n₂ heq
    have valid : ∀ (F : Finset (Finset P)), ∏ γ ∈ F, polyWeight inc t γ ≠ 0 →
        ∀ γ ∈ F, ValidPolymer inc γ := by
      intro F hne γ hγ
      have h1 := (Finset.prod_ne_zero_iff.mp hne) γ hγ
      by_contra hv
      exact h1 (by simp [polyWeight, hv])
    have hv₁ := valid F₁ n₁
    have hv₂ := valid F₂ n₂
    have hc₁ : ∀ γ ∈ F₁, ∀ γ' ∈ F₁, γ ≠ γ' → Compat inc γ γ' := fun γ hγ γ' hγ' h =>
      (Finset.mem_filter.mp h₁).2 hγ hγ' h
    have hc₂ : ∀ γ ∈ F₂, ∀ γ' ∈ F₂, γ ≠ γ' → Compat inc γ γ' := fun γ hγ γ' hγ' h =>
      (Finset.mem_filter.mp h₂).2 hγ hγ' h
    have key : ∀ (A B : Finset (Finset P)), (∀ γ ∈ A, ValidPolymer inc γ) →
        (∀ γ ∈ B, ValidPolymer inc γ) →
        (∀ γ ∈ A, ∀ γ' ∈ A, γ ≠ γ' → Compat inc γ γ') →
        (∀ γ ∈ B, ∀ γ' ∈ B, γ ≠ γ' → Compat inc γ γ') →
        A.biUnion id = B.biUnion id → ∀ γ ∈ A, γ ∈ B := by
      intro A B hA hB hcA hcB hAB γ hγ
      obtain ⟨p, hp⟩ := (hA γ hγ).1
      have hpB : p ∈ B.biUnion id := hAB ▸ Finset.mem_biUnion.mpr ⟨γ, hγ, hp⟩
      obtain ⟨γ', hγ', hpγ'⟩ := Finset.mem_biUnion.mp hpB
      have e1 := family_eq_comp hA hcA hγ hp
      have e2 := family_eq_comp hB hcB hγ' hpγ'
      rw [hAB] at e1
      exact (e1.trans e2.symm) ▸ hγ'
    ext γ
    exact ⟨key F₁ F₂ hv₁ hv₂ hc₁ hc₂ heq γ, key F₂ F₁ hv₂ hv₁ hc₂ hc₁ heq.symm γ⟩
  · -- surjectivity
    intro S hS hne
    have hSc : boundary inc S = 0 := (Finset.mem_filter.mp hS).2
    refine ⟨S.image (comp inc S), ?_, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      intro γ₁ γ₂ h1 h2 hne12
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h2
      exact comp_compat hne12
    · by_cases hS0 : S = ∅
      · subst hS0; simp
      · have ht : t ≠ 0 := by
          rintro rfl
          exact hne (by simp [Finset.nonempty_iff_ne_empty.mpr hS0 |>.card_pos.ne'])
        refine Finset.prod_ne_zero_iff.mpr fun γ hγ => ?_
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hγ
        simp [polyWeight, comp_valid hSc hp, ht]
    · ext x
      simp only [Finset.mem_biUnion, Finset.mem_image, id]
      constructor
      · rintro ⟨γ, ⟨p, hp, rfl⟩, hx⟩; exact (mem_comp.mp hx).1
      · intro hx
        exact ⟨comp inc S x, ⟨x, hx, rfl⟩, mem_comp.mpr ⟨hx, Relation.ReflTransGen.refl⟩⟩
  · -- the weights agree
    intro F hF hne
    have hvalid : ∀ γ ∈ F, ValidPolymer inc γ := by
      intro γ hγ
      have h1 := (Finset.prod_ne_zero_iff.mp hne) γ hγ
      by_contra hv
      exact h1 (by simp [polyWeight, hv])
    have hcomp : ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → Compat inc γ γ' := fun γ hγ γ' hγ' h =>
      (Finset.mem_filter.mp hF).2 hγ hγ' h
    have hdisj : ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → Disjoint (id γ) (id γ') := by
      intro γ hγ γ' hγ' hg
      rw [Finset.disjoint_left]
      intro p hp hp'
      exact (hcomp γ hγ γ' hγ' hg p hp p hp').1 rfl
    have hw : ∏ γ ∈ F, polyWeight inc t γ = ∏ γ ∈ F, t ^ γ.card :=
      Finset.prod_congr rfl fun γ hγ => by simp [polyWeight, hvalid γ hγ]
    rw [hw, Finset.prod_pow_eq_pow_sum, Finset.card_biUnion hdisj]
    try rfl

lemma polyWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (γ : Finset P) : 0 ≤ polyWeight inc t γ := by
  unfold polyWeight
  split_ifs
  · exact pow_nonneg ht _
  · exact le_rfl

open Classical in
/-- **Kotecký–Preiss applies to Z2**: for `t ≥ 0`, `Z(Λ) ≤ Z(Λ_γ₀) · exp (a γ₀)` for every
sub-volume `Λ` of polymers, whenever the weights satisfy the Kotecký–Preiss condition. -/
theorem z2_ratio_le_exp {t : ℝ} (ht : 0 ≤ t) {a d : Finset P → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hd : ∀ γ, 0 ≤ d γ) (hkp : SatisfiesKoteckyPreiss (Compat inc) (polyWeight inc t) a d)
    (γ₀ : Finset P) (Λ : Finset (Finset P)) :
    polymerZ (Compat inc) (polyWeight inc t) Λ ≤
      polymerZ (Compat inc) (polyWeight inc t) (Λ.filter (Compat inc γ₀)) * Real.exp (a γ₀) :=
  ratio_le_exp_of_kp _ (polyWeight_nonneg ht) (fun _ _ h => compat_symm h) ha hd hkp γ₀ Λ

open Classical in
/-- `0 ≤ log Z ≤ ∑ w` for the Z2 partition function, `t ≥ 0`. -/
theorem z2_log_le {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Real.log (highTempSum inc t 0) ∧
      Real.log (highTempSum inc t 0) ≤ ∑ γ : Finset P, polyWeight inc t γ := by
  rw [highTempSum_zero_eq_polymerZ]
  exact log_polymerZ_le _ (polyWeight_nonneg ht) (fun _ _ h => compat_symm h) _

end Z2Gauge
