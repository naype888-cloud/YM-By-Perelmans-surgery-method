/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import PolymerBound

/-!

# The weighted number of surfaces attached to a set of seeds is bounded, uniformly in the volume

## i. Overview

Let `Σ` be a set of seeds and call a set `γ` of plaquettes `Σ`-rooted if every plaquette of `γ` is
reachable inside `γ` from a seed of `Σ` that lies in `γ`. Let `F_Q(Σ) = ∑ t^|γ|` over the `Σ`-rooted
`γ ⊆ Q`. If every plaquette is adjacent to at most `Δ` others and `a ≥ 0` satisfies
`t (1 + a)^Δ ≤ a`, then `F_Q(Σ) ≤ (1 + a)^|Σ|` for every `Q` and every `Σ ⊆ Q`.

The proof is an induction on `Q`. Take a seed `r`. The `γ` without `r` are `Σ ∖ r`-rooted in `Q ∖ r`.
The `γ` with `r`, once `r` is removed, are rooted at the seeds of `Σ ∖ r` together with the neighbours
of `r`, at most `Δ` new seeds, and weigh `t` times as much. So
`F_Q(Σ) ≤ (1+a)^{|Σ|-1} (1 + t (1+a)^Δ) ≤ (1+a)^|Σ|`.
No volume appears in the bound: it is a bound by the number of seeds, that is, by the perimeter of
the loop.

## ii. Key results

- `Z2Gauge.reach_erase` : removing a plaquette from a path.
- `Z2Gauge.rootedSum_le` : `F_Q(Σ) ≤ (1 + a)^|Σ|`.

## iii. Table of contents

- A. Removing a plaquette
- B. The induction

## iv. References

-/

open Finset

namespace Z2Gauge

set_option linter.unusedSectionVars false

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
variable {inc : P → L → ZMod 2}

/-! ## A. Removing a plaquette -/

/-- **Removing a plaquette from a path**: if `p ≠ r` is reachable inside `γ` from `q`, then inside
`γ ∖ r` it is reachable from `q` (when `q ≠ r`) or from a neighbour of `r`. -/
lemma reach_erase {γ : Finset P} {r q p : P} (hr : ReachIn inc γ q p) (hp : p ≠ r) :
    (q ≠ r ∧ ReachIn inc (γ.erase r) q p) ∨
      ∃ n ∈ γ.erase r, Adj inc r n ∧ ReachIn inc (γ.erase r) n p := by
  have key : ∀ b, ReachIn inc γ q b → b = r ∨ (q ≠ r ∧ ReachIn inc (γ.erase r) q b) ∨
      ∃ n ∈ γ.erase r, Adj inc r n ∧ ReachIn inc (γ.erase r) n b := by
    intro b hb
    induction hb with
    | refl =>
      by_cases hqr : q = r
      · exact Or.inl hqr
      · exact Or.inr (Or.inl ⟨hqr, Relation.ReflTransGen.refl⟩)
    | @tail b' c _ hbc ih =>
      by_cases hc : c = r
      · exact Or.inl hc
      · have hcγ : c ∈ γ.erase r := Finset.mem_erase.mpr ⟨hc, hbc.2.1⟩
        by_cases hb : b' = r
        · subst hb
          exact Or.inr (Or.inr ⟨c, hcγ, hbc.2.2, Relation.ReflTransGen.refl⟩)
        · have hbγ : b' ∈ γ.erase r := Finset.mem_erase.mpr ⟨hb, hbc.1⟩
          rcases ih with h | ⟨hq, hrq⟩ | ⟨n, hn, hadj, hrn⟩
          · exact absurd h hb
          · exact Or.inr (Or.inl ⟨hq, hrq.tail ⟨hbγ, hcγ, hbc.2.2⟩⟩)
          · exact Or.inr (Or.inr ⟨n, hn, hadj, hrn.tail ⟨hbγ, hcγ, hbc.2.2⟩⟩)
  rcases key p hr with h | h | h
  · exact absurd h hp
  · exact Or.inl h
  · exact Or.inr h

/-! ## B. The induction -/

/-- `γ` is `Σ`-rooted: every plaquette of `γ` is reachable inside `γ` from a seed of `Σ` in `γ`. -/
def Rooted (inc : P → L → ZMod 2) (T γ : Finset P) : Prop :=
  ∀ p ∈ γ, ∃ q ∈ γ, q ∈ T ∧ ReachIn inc γ q p

open Classical in
/-- `∑ t^|γ|` over the `Σ`-rooted subsets `γ` of `Q`. -/
noncomputable def rootedSum (inc : P → L → ZMod 2) (t : ℝ) (Q T : Finset P) : ℝ :=
  ∑ γ ∈ Q.powerset.filter (Rooted inc T), t ^ γ.card

lemma rootedSum_empty (t : ℝ) (Q : Finset P) : rootedSum inc t Q ∅ = 1 := by
  classical
  unfold rootedSum
  have : Q.powerset.filter (Rooted inc ∅) = {∅} := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      by_contra hne
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨q, _, hq, _⟩ := h p hp
      simp at hq
    · rintro rfl
      exact ⟨Finset.empty_subset _, fun p hp => by simp at hp⟩
  rw [this]
  simp

open Classical in
/-- **The weighted number of rooted surfaces is bounded by the number of seeds**: if every plaquette
is adjacent to at most `Δ` others and `t (1 + a)^Δ ≤ a`, then `F_Q(T) ≤ (1 + a)^|T|`. -/
theorem rootedSum_le {Δ : ℕ} (hdeg : ∀ p : P, (univ.filter (Adj inc p)).card ≤ Δ) {t a : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hta : t * (1 + a) ^ Δ ≤ a) :
    ∀ (n : ℕ) (Q T : Finset P), Q.card = n → T ⊆ Q → rootedSum inc t Q T ≤ (1 + a) ^ T.card := by
  classical
  intro n
  induction n with
  | zero =>
    intro Q T hQ hT
    have hQe : Q = ∅ := Finset.card_eq_zero.mp hQ
    have hT0 : T = ∅ := Finset.subset_empty.mp (hQe ▸ hT)
    subst hT0
    rw [rootedSum_empty]
    simp
  | succ n ih =>
    intro Q T hQ hT
    by_cases hTe : T = ∅
    · subst hTe
      rw [rootedSum_empty]
      simp
    obtain ⟨r, hrT⟩ := Finset.nonempty_iff_ne_empty.mpr hTe
    have hrQ : r ∈ Q := hT hrT
    have hQ'c : (Q.erase r).card = n := by
      rw [Finset.card_erase_of_mem hrQ, hQ]
      rfl
    have hT0Q' : T.erase r ⊆ Q.erase r := Finset.erase_subset_erase r hT
    have hT1Q' : T.erase r ∪ (Q.erase r).filter (Adj inc r) ⊆ Q.erase r :=
      Finset.union_subset hT0Q' (Finset.filter_subset _ _)
    have hT0c : (T.erase r).card + 1 = T.card := Finset.card_erase_add_one hrT
    have hNc : ((Q.erase r).filter (Adj inc r)).card ≤ Δ :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hdeg r)
    have hT1c : (T.erase r ∪ (Q.erase r).filter (Adj inc r)).card ≤ (T.erase r).card + Δ :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left hNc _)
    have ih0 := ih (Q.erase r) (T.erase r) hQ'c hT0Q'
    have ih1 := ih (Q.erase r) (T.erase r ∪ (Q.erase r).filter (Adj inc r)) hQ'c hT1Q'
    have h1a : (1 : ℝ) ≤ 1 + a := by linarith
    -- the split according to `r ∈ γ`
    unfold rootedSum at ih0 ih1 ⊢
    rw [← Finset.sum_filter_add_sum_filter_not
      (Q.powerset.filter (Rooted inc T)) (fun γ => r ∈ γ)]
    have hA1 : ∑ γ ∈ (Q.powerset.filter (Rooted inc T)).filter (fun γ => ¬ r ∈ γ), t ^ γ.card ≤
        ∑ γ ∈ (Q.erase r).powerset.filter (Rooted inc (T.erase r)), t ^ γ.card := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => pow_nonneg ht _
      intro γ hγ
      simp only [Finset.mem_filter, Finset.mem_powerset] at hγ ⊢
      obtain ⟨⟨hγQ, hroot⟩, hrγ⟩ := hγ
      refine ⟨fun x hx => Finset.mem_erase.mpr ⟨fun e => hrγ (e ▸ hx), hγQ hx⟩, fun p hp => ?_⟩
      obtain ⟨q, hqγ, hqT, hreach⟩ := hroot p hp
      exact ⟨q, hqγ, Finset.mem_erase.mpr ⟨fun e => hrγ (e ▸ hqγ), hqT⟩, hreach⟩
    have hA2 : ∑ γ ∈ (Q.powerset.filter (Rooted inc T)).filter (fun γ => r ∈ γ), t ^ γ.card ≤
        t * ∑ γ ∈ (Q.erase r).powerset.filter
          (Rooted inc (T.erase r ∪ (Q.erase r).filter (Adj inc r))), t ^ γ.card := by
      have hcard : ∀ γ ∈ (Q.powerset.filter (Rooted inc T)).filter (fun γ => r ∈ γ),
          t ^ γ.card = t * t ^ (γ.erase r).card := by
        intro γ hγ
        have hr : r ∈ γ := (Finset.mem_filter.mp hγ).2
        rw [← Finset.card_erase_add_one hr, pow_succ, mul_comm]
      rw [Finset.sum_congr rfl hcard, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ ht
      have hinj : Set.InjOn (fun γ : Finset P => γ.erase r)
          ((Q.powerset.filter (Rooted inc T)).filter (fun γ => r ∈ γ) : Set (Finset P)) := by
        intro γ hγ γ' hγ' h
        have hr : r ∈ γ := (Finset.mem_filter.mp hγ).2
        have hr' : r ∈ γ' := (Finset.mem_filter.mp hγ').2
        rw [← Finset.insert_erase hr, ← Finset.insert_erase hr']
        exact congrArg _ h
      rw [← Finset.sum_image (f := fun b : Finset P => t ^ b.card) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => pow_nonneg ht _
      intro b hb
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hb
      simp only [Finset.mem_filter, Finset.mem_powerset] at hγ ⊢
      obtain ⟨⟨hγQ, hroot⟩, hrγ⟩ := hγ
      refine ⟨Finset.erase_subset_erase r hγQ, fun p hp => ?_⟩
      have hpr : p ≠ r := (Finset.mem_erase.mp hp).1
      have hpγ : p ∈ γ := (Finset.mem_erase.mp hp).2
      obtain ⟨q, hqγ, hqT, hreach⟩ := hroot p hpγ
      rcases reach_erase hreach hpr with ⟨hq, hrq⟩ | ⟨n', hn', hadj, hrn⟩
      · exact ⟨q, Finset.mem_erase.mpr ⟨hq, hqγ⟩,
          Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hq, hqT⟩), hrq⟩
      · refine ⟨n', hn', Finset.mem_union_right _ ?_, hrn⟩
        exact Finset.mem_filter.mpr ⟨Finset.erase_subset_erase r hγQ hn', hadj⟩
    have hpow0 : (1 + a) ^ (T.erase r).card ≤ (1 + a) ^ (T.card - 1) := by
      rw [← hT0c]; simp
    calc _ ≤ t * ∑ γ ∈ (Q.erase r).powerset.filter
            (Rooted inc (T.erase r ∪ (Q.erase r).filter (Adj inc r))), t ^ γ.card +
          ∑ γ ∈ (Q.erase r).powerset.filter (Rooted inc (T.erase r)), t ^ γ.card :=
          add_le_add hA2 hA1
      _ ≤ t * (1 + a) ^ ((T.erase r).card + Δ) + (1 + a) ^ (T.erase r).card := by
          refine add_le_add (mul_le_mul_of_nonneg_left (ih1.trans ?_) ht) ih0
          exact pow_le_pow_right₀ h1a hT1c
      _ = (1 + a) ^ (T.erase r).card * (1 + t * (1 + a) ^ Δ) := by
          rw [pow_add]; ring
      _ ≤ (1 + a) ^ (T.erase r).card * (1 + a) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) _)
      _ = (1 + a) ^ T.card := by rw [← hT0c, pow_succ]

end Z2Gauge
