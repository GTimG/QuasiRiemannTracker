/- Copyright (c) 2026 Sil. Apache-2.0.
Allocation summation with its literal, nonuniform norm and live-slot
budget. Inactive allocation terms are removed as exact zeros only.
-/
import Candidate.FourthPower.MixedSourceAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedAllocationCost
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentOriginalRadialComparison CenteredMomentEnergyCapacityRemoval
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open MixedSourceAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The energy cost is the sum of the individual bounds, not the
number of terms times a prematurely enlarged common bound. -/
theorem radial_phase_family {ι : Type*} [Fintype ι]
    (phase f : ι→O→ℂ) (E : ι→ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hphase : ∀i z,keep z→‖phase i z‖≤1)
    (hf : ∀i,radialEnergy (f i) keep Φ K≤E i) :
    radialEnergy (fun z=>∑i,phase i z*f i z) keep Φ K≤
      (Fintype.card ι:ℝ)*∑i,E i := by
  let g := fun (i : ι)(z : O)=>if keep z then
    ‖f i z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hg (i : ι) : Summable (g i) := compact_radial_summable (f i) keep Φ K radial hK hs
  have hsum : Summable (fun z=>∑i,g i z) := summable_sum (fun i _=>hg i)
  have he : radialEnergy (fun z=>∑i,phase i z*f i z) keep Φ K≤
      (Fintype.card ι:ℝ)*∑i,radialEnergy (f i) keep Φ K := by
    unfold radialEnergy
    calc
      _ ≤ ∑'z : O,(Fintype.card ι:ℝ)*∑i,g i z := by
        apply (compact_radial_summable _ keep Φ K radial hK hs).tsum_le_tsum _ (hsum.mul_left _)
        intro z
        by_cases hz : keep z
        · simp only [hz,ite_true,g]
          have hh := CubicEisenstein.norm_sum_sq_le_card Finset.univ (fun i=>phase i z*f i z)
          have hp (i : ι) : ‖phase i z*f i z‖^2≤‖f i z‖^2 := by
            apply pow_le_pow_left₀ (norm_nonneg _) _ 2
            rw [norm_mul]
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hphase i z hz) (norm_nonneg _)
          have hb := hh.trans (mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun i _=>hp i)) (Nat.cast_nonneg _))
          simpa only [Finset.card_univ,Finset.sum_mul,mul_assoc] using
            mul_le_mul_of_nonneg_right hb (hΦ z)
        · simp only [hz,ite_false,g,Finset.sum_const_zero,mul_zero,le_refl]
      _ = _ := by
        rw [tsum_mul_left,Summable.tsum_finsetSum (fun i _=>hg i)]
  exact he.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>hf i)) (Nat.cast_nonneg _))

/-- A vanishing allocation phase permits deleting that whole summand;
there is no deletion of coefficients inside a nonzero squared row. -/
theorem radial_active_family {ι : Type*} [Fintype ι]
    (active : ι→Prop) (phase f : ι→O→ℂ) (E : ι→ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hphase : ∀i z,keep z→‖phase i z‖≤1)
    (hz : ∀i,¬active i→∀z,phase i z=0)
    (hf : ∀i,active i → radialEnergy (f i) keep Φ K≤E i) :
    radialEnergy (fun z=>∑i,phase i z*f i z) keep Φ K≤
      (Fintype.card ι:ℝ)*∑i,if active i then E i else 0 := by
  let g := fun (i : ι)(z : O)=>if active i then f i z else 0
  have he := radial_phase_family phase g (fun i=>if active i then E i else 0)
    keep Φ K radial hK hs hΦ hphase (by
      intro i
      by_cases hi : active i
      · simpa only [g,hi,ite_true] using hf i hi
      · simp only [g,hi,ite_false,radialEnergy,norm_zero,zero_pow (by decide : 2≠0),
          zero_mul,ite_self,tsum_zero,le_refl])
  have hrow : (fun z=>∑i,phase i z*g i z)=(fun z=>∑i,phase i z*f i z) := by
    funext z
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : active i
    · simp only [g,ha,ite_true]
    · simp only [g,ha,ite_false,hz i ha z,zero_mul]
  rwa [hrow] at he

variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

def liveWeight (Z κ : ℝ) (w : α→ℝ) (B : Tuple α) : ℝ :=
  Z^(κ*(∑i : liveIndices B,w i.val))/(finiteTupleProduct B).absNorm

def budget (labels : Finset (Tuple α)) (active : labels→Prop)
    (Z κ : ℝ) (w : α→ℝ) : ℝ :=
  (labels.card:ℝ)*∑B : labels,if active B then liveWeight Z κ w B.val else 0

theorem live_weight_nonneg (Z κ : ℝ) (w : α→ℝ) (B : Tuple α) (hZ : 0≤Z) :
    0≤liveWeight Z κ w B := div_nonneg (Real.rpow_nonneg hZ _) (Nat.cast_nonneg _)

theorem budget_nonneg (labels : Finset (Tuple α)) (active : labels→Prop)
    (Z κ : ℝ) (w : α→ℝ) (hZ : 0≤Z) : 0≤budget labels active Z κ w := by
  apply mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg ?_)
  intro B hB
  split_ifs
  · exact live_weight_nonneg Z κ w B.val hZ
  · exact le_rfl

/-- All copies selected in different coordinates remain in the
denominator; this is not merely the norm of the selected radical. -/
theorem selected_weight (D : Id) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (B : Tuple α) (hB : ∀j,B j≠0) (ha : allocationTerm D Finset.univ B a≠0)
    (Z κ : ℝ) (w : α→ℝ) (hZ : 0≤Z) :
    liveWeight Z κ w B≤Z^(κ*(∑i : liveIndices B,w i.val))/
      ((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ) := by
  have hq : 0<((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun j _=>selectedDivisor_ne_zero D Finset.univ a j)))
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ _) hq (selected_product_norm D a B hB ha)

end
end Candidate.FourthPower.MixedAllocationCost
