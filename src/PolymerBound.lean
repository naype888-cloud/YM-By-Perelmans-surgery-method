/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Z2AreaLaw

/-!

# The numerator of a Wilson loop is bounded by the surfaces attached to the loop

## i. Overview

In the high temperature expansion of `Z2AreaLaw.lean`, `⟨W(C)⟩ = N(C) / Z` with
`N(C) = ∑_{∂S = C} t^|S|` and `Z = ∑_{∂S = 0} t^|S|`. For `t ≥ 0` there is no need of a cluster
expansion to bound the quotient from above. Call two plaquettes *adjacent* if they share a link, and
let the *cluster* of `S` be the plaquettes of `S` reachable inside `S` from a plaquette that contains
a link of `C` (a seed). The cluster `γ` and the rest `R = S ∖ γ` share no link, so their boundaries
add without cancellation; since a seed in `R` would be in `γ`, `∂R = 0`, and hence `∂γ = C`.
The map `S ↦ (γ, R)` is injective, so
`N(C) ≤ (∑_γ t^|γ|) · Z`, the sum over the sets `γ` with `∂γ = C` in which every plaquette is
reachable from a seed. Then `⟨W(C)⟩ ≤ ∑_γ t^|γ|`: the closed surfaces far from the loop (the vacuum
bubbles) have cancelled, and the bound does not depend on the volume.

This holds for any incidence. It does not bound the sum over `γ` (that is the counting of connected
surfaces) and says nothing about non-abelian groups.

## ii. Key results

- `Z2Gauge.cluster_boundary` : `∂(cluster) = C` and the rest has `∂ = 0`.
- `Z2Gauge.numerator_le` : `N(C) ≤ (∑_{γ attached} t^|γ|) · Z`.

## iii. Table of contents

- A. Adjacency, seeds and clusters
- B. The boundary of the cluster
- C. The bound

## iv. References

-/

set_option linter.unusedSectionVars false

open Finset

namespace Z2Gauge

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
variable (inc : P → L → ZMod 2)

/-! ## A. Adjacency, seeds and clusters -/

/-- Two distinct plaquettes are adjacent if they share a link. -/
def Adj (p q : P) : Prop := p ≠ q ∧ ∃ l, inc p l ≠ 0 ∧ inc q l ≠ 0

/-- A plaquette is a seed of the loop `C` if it contains a link of `C`. -/
def IsSeed (C : L → ZMod 2) (p : P) : Prop := ∃ l, C l ≠ 0 ∧ inc p l ≠ 0

/-- Reachability inside `S`, through adjacent plaquettes. -/
def ReachIn (S : Finset P) : P → P → Prop :=
  Relation.ReflTransGen fun p q => p ∈ S ∧ q ∈ S ∧ Adj inc p q

/-- A plaquette of `S` is attached to the loop `C` if it is reachable inside `S` from a seed. -/
def Attached (S : Finset P) (C : L → ZMod 2) (p : P) : Prop :=
  p ∈ S ∧ ∃ q ∈ S, IsSeed inc C q ∧ ReachIn inc S q p

open Classical in
/-- The cluster of `S` attached to the loop `C`. -/
noncomputable def cluster (S : Finset P) (C : L → ZMod 2) : Finset P :=
  S.filter (Attached inc S C)

variable {inc}

lemma mem_cluster {S : Finset P} {C : L → ZMod 2} {p : P} :
    p ∈ cluster inc S C ↔ Attached inc S C p := by
  classical
  unfold cluster
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- A seed of `S` is in the cluster. -/
lemma seed_mem_cluster {S : Finset P} {C : L → ZMod 2} {p : P} (hp : p ∈ S)
    (hs : IsSeed inc C p) : p ∈ cluster inc S C :=
  mem_cluster.mpr ⟨hp, p, hp, hs, Relation.ReflTransGen.refl⟩

/-- **The cluster is closed under adjacency inside `S`.** -/
lemma cluster_closed {S : Finset P} {C : L → ZMod 2} {p p' : P} (hp : p ∈ cluster inc S C)
    (hp' : p' ∈ S) (hadj : Adj inc p p') : p' ∈ cluster inc S C := by
  obtain ⟨hpS, q, hqS, hq, hr⟩ := mem_cluster.mp hp
  exact mem_cluster.mpr ⟨hp', q, hqS, hq, hr.tail ⟨hpS, hp', hadj⟩⟩

/-- A plaquette of the cluster and one of `S` outside it share no link. -/
lemma no_shared_link {S : Finset P} {C : L → ZMod 2} {p p' : P} (hp : p ∈ cluster inc S C)
    (hp' : p' ∈ S) (hn : p' ∉ cluster inc S C) (l : L) : inc p l = 0 ∨ inc p' l = 0 := by
  by_contra h
  push Not at h
  have hne : p ≠ p' := fun e => hn (e ▸ hp)
  exact hn (cluster_closed hp hp' ⟨hne, l, h.1, h.2⟩)

/-! ## B. The boundary of the cluster -/

open Classical in
/-- The rest of `S` once the cluster is removed. -/
noncomputable def restOf (inc : P → L → ZMod 2) (S : Finset P) (C : L → ZMod 2) : Finset P :=
  S.filter fun p => ¬ Attached inc S C p

lemma mem_restOf {S : Finset P} {C : L → ZMod 2} {p : P} :
    p ∈ restOf inc S C ↔ p ∈ S ∧ p ∉ cluster inc S C := by
  classical
  unfold restOf
  simp only [Finset.mem_filter, mem_cluster]

/-- The boundary of `S` is the sum of the boundaries of the cluster and of the rest. -/
lemma boundary_split (S : Finset P) (C : L → ZMod 2) :
    boundary inc S = boundary inc (cluster inc S C) + boundary inc (restOf inc S C) := by
  classical
  funext l
  simp only [boundary, Pi.add_apply, cluster, restOf]
  exact (Finset.sum_filter_add_sum_filter_not S (Attached inc S C) fun p => inc p l).symm

/-- **The rest has no boundary**: a seed outside the cluster would be in it. -/
lemma restOf_boundary {S : Finset P} {C : L → ZMod 2} (hS : boundary inc S = C) :
    boundary inc (restOf inc S C) = 0 := by
  classical
  funext l
  show ∑ p ∈ restOf inc S C, inc p l = 0
  by_cases h : ∃ p' ∈ restOf inc S C, inc p' l ≠ 0
  · obtain ⟨p', hp'R, hp'l⟩ := h
    obtain ⟨hp'S, hp'n⟩ := mem_restOf.mp hp'R
    have hC : C l = 0 := by
      by_contra hCl
      exact hp'n (seed_mem_cluster hp'S ⟨l, hCl, hp'l⟩)
    have hG : boundary inc (cluster inc S C) l = 0 :=
      Finset.sum_eq_zero fun p hp => (no_shared_link hp hp'S hp'n l).resolve_right hp'l
    have hsplit := congrFun (boundary_split (inc := inc) S C) l
    rw [hS] at hsplit
    simp only [Pi.add_apply, hC, hG, zero_add] at hsplit
    exact hsplit.symm
  · push Not at h
    exact Finset.sum_eq_zero fun p hp => h p hp

/-- **The cluster has the boundary `C`.** -/
lemma cluster_boundary {S : Finset P} {C : L → ZMod 2} (hS : boundary inc S = C) :
    boundary inc (cluster inc S C) = C := by
  have h := boundary_split (inc := inc) S C
  rw [hS, restOf_boundary hS] at h
  simpa using h.symm

/-- Every plaquette of the cluster is reachable from a seed inside the cluster itself. -/
lemma cluster_attached {S : Finset P} {C : L → ZMod 2} {p : P} (hp : p ∈ cluster inc S C) :
    ∃ q ∈ cluster inc S C, IsSeed inc C q ∧ ReachIn inc (cluster inc S C) q p := by
  obtain ⟨_, q, hqS, hq, hr⟩ := mem_cluster.mp hp
  have key : ∀ b, ReachIn inc S q b →
      b ∈ cluster inc S C ∧ ReachIn inc (cluster inc S C) q b := by
    intro b hb
    induction hb with
    | refl => exact ⟨seed_mem_cluster hqS hq, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      obtain ⟨hbG, hrb⟩ := ih
      have hcG := cluster_closed hbG hbc.2.1 hbc.2.2
      exact ⟨hcG, hrb.tail ⟨hbG, hcG, hbc.2.2⟩⟩
  exact ⟨q, seed_mem_cluster hqS hq, hq, (key p hr).2⟩

/-! ## C. The bound -/

open Classical in
/-- The sets of plaquettes with boundary `C` in which every plaquette is reachable from a seed. -/
noncomputable def attachedSets (inc : P → L → ZMod 2) (C : L → ZMod 2) : Finset (Finset P) :=
  (Finset.univ : Finset P).powerset.filter fun γ =>
    boundary inc γ = C ∧ ∀ p ∈ γ, ∃ q ∈ γ, IsSeed inc C q ∧ ReachIn inc γ q p

/-- **The numerator is bounded by the attached surfaces times the partition function.** For
`t ≥ 0`: `N(C) ≤ (∑_{γ attached} t^|γ|) · Z`. -/
theorem numerator_le {t : ℝ} (ht : 0 ≤ t) (C : L → ZMod 2) :
    highTempSum inc t C ≤ (∑ γ ∈ attachedSets inc C, t ^ γ.card) * highTempSum inc t 0 := by
  classical
  unfold highTempSum
  set A := (Finset.univ : Finset P).powerset.filter fun S => boundary inc S = C with hA
  set Z := (Finset.univ : Finset P).powerset.filter fun S => boundary inc S = (0 : L → ZMod 2)
    with hZ
  let Φ : Finset P → Finset P × Finset P := fun S => (cluster inc S C, restOf inc S C)
  have hAmem : ∀ S, S ∈ A ↔ boundary inc S = C := by
    intro S
    simp [hA]
  have hinj : Set.InjOn Φ A := by
    intro S hS S' hS' h
    have e : ∀ T : Finset P, cluster inc T C ∪ restOf inc T C = T := by
      intro T
      simp only [cluster, restOf]
      exact Finset.filter_union_filter_not_eq _ _
    have h1 : cluster inc S C = cluster inc S' C := congrArg Prod.fst h
    have h2 : restOf inc S C = restOf inc S' C := congrArg Prod.snd h
    rw [← e S, ← e S', h1, h2]
  have himg : ∀ S ∈ A, Φ S ∈ attachedSets inc C ×ˢ Z := by
    intro S hS
    have hS' := (hAmem S).mp hS
    simp only [attachedSets, hZ, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, Φ]
    exact ⟨⟨cluster_boundary hS', fun p hp => cluster_attached hp⟩, restOf_boundary hS'⟩
  have hcard : ∀ S : Finset P, t ^ S.card = t ^ (cluster inc S C).card * t ^ (restOf inc S C).card := by
    intro S
    rw [← pow_add]
    congr 1
    simp only [cluster, restOf]
    exact (Finset.card_filter_add_card_filter_not (s := S) (Attached inc S C)).symm
  calc ∑ S ∈ A, t ^ S.card
      = ∑ S ∈ A, (fun b : Finset P × Finset P => t ^ b.1.card * t ^ b.2.card) (Φ S) :=
        sum_congr rfl fun S _ => hcard S
    _ = ∑ b ∈ A.image Φ, t ^ b.1.card * t ^ b.2.card := (Finset.sum_image (f := fun b : Finset P × Finset P => t ^ b.1.card * t ^ b.2.card) hinj).symm
    _ ≤ ∑ b ∈ attachedSets inc C ×ˢ Z, t ^ b.1.card * t ^ b.2.card :=
        sum_le_sum_of_subset_of_nonneg
          (fun b hb => by
            obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hb
            exact himg S hS)
          fun b _ _ => mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _)
    _ = (∑ γ ∈ attachedSets inc C, t ^ γ.card) * ∑ R ∈ Z, t ^ R.card := by
        rw [Finset.sum_product, Finset.sum_mul_sum]

/-- **The expectation of a Wilson loop is bounded by the attached surfaces, uniformly in the
volume**: for `β ≥ 0`, `⟨W(C)⟩ ≤ ∑_{γ attached to C} tanh(β)^|γ|`. -/
theorem expect_le_attached {β : ℝ} (hβ : 0 ≤ β) (C : L → ZMod 2) :
    highTempSum inc (Real.tanh β) C / highTempSum inc (Real.tanh β) 0 ≤
      ∑ γ ∈ attachedSets inc C, Real.tanh β ^ γ.card := by
  have ht : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos β).le
  have hZ : 0 < highTempSum inc (Real.tanh β) 0 :=
    lt_of_lt_of_le one_pos (one_le_highTempSum_zero inc ht)
  rw [div_le_iff₀ hZ]
  exact numerator_le ht C

end Z2Gauge
