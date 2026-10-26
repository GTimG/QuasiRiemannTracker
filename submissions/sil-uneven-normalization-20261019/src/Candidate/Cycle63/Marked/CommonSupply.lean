import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRawScale

namespace OAI.SevenEighths.Cycle63CommonSupply
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRawScale CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

/-- Logarithmic widths split exactly between frozen and surviving common slots. -/
theorem common_slot_width_split (B : Tuple ι) (P : ι → ℝ)
    (hP : ∀ i,0<P i) (Z : ℝ) :
    (∑i,Real.logb Z (frozenScale B P i))+
      (∑i : liveIndices B,Real.logb Z (P i)) = ∑i,Real.logb Z (P i) := by
  have he := congrArg (Real.logb Z) (slot_scale_split B P)
  have hF : 0 < ∏i,frozenScale B P i := Finset.prod_pos (fun i _ => frozenScale_pos B P hP i)
  have hL : 0 < ∏i : liveIndices B,P i := Finset.prod_pos (fun i _ => hP i)
  rw [Real.logb_mul hF.ne' hL.ne'] at he
  simp only [Real.logb_prod _ _ (fun i _ => (frozenScale_pos B P hP i).ne'),
    Real.logb_prod _ _ (fun i _ => (hP i).ne')] at he
  rw [Real.logb_prod _ _ (fun (i : liveIndices B) _ => (hP i).ne')] at he
  exact he

theorem plainNorm_ge_one (B : Tuple ι) (hB : ∀ i,B i≠0) : 1 ≤ plainNorm B := by
  have hn (j : Fin 2) : (1:ℝ) ≤ (B (Sum.inr j)).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hB _))
  unfold plainNorm
  nlinarith [hn 0, hn 1, mul_nonneg (sub_nonneg.mpr (hn 0)) (sub_nonneg.mpr (hn 1))]

/-- A nonzero frozen coefficient puts every frozen prime in the fixed annulus.
The total width lost is bounded by the common ideal and fixed support padding. -/
theorem common_frozen_width_le (B : Tuple ι) (hB : ∀ i,B i≠0)
    (C R : Ideal O) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0<P i) (a b : ℝ) (ha : 0<a)
    (hW : ∀ i,Function.support (W i)⊆Set.Icc a b)
    (hne : frozenCoefficient B C R ν W P≠0) (Z : ℝ) (hZ : 1<Z) :
    (∑i,Real.logb Z (frozenScale B P i)) ≤
      Real.logb Z (C.absNorm:ℝ)-(Fintype.card ι:ℝ)*Real.logb Z (min 1 a) := by
  have hm : 0 < min 1 a := lt_min zero_lt_one ha
  have hr := (actual_reduction_norm B hB C R hprod ν W P hP a b ha hW hne).1
  have hh := Real.logb_le_logb_of_le hZ
    (mul_pos (pow_pos hm _) (rawReduction_pos B hB P hP)) hr
  rw [Real.logb_mul (pow_pos hm _).ne' (rawReduction_pos B hB P hP).ne',
    Real.logb_pow] at hh
  have hs := Real.logb_nonneg hZ (plainNorm_ge_one B hB)
  unfold rawReduction at hh
  rw [Real.logb_mul (plainNorm_pos B hB).ne'
    (Finset.prod_pos (fun i _ => frozenScale_pos B P hP i)).ne',
    Real.logb_prod _ _ (fun i _ => (frozenScale_pos B P hP i).ne')] at hh
  linarith

theorem common_live_width_lower (B : Tuple ι) (hB : ∀ i,B i≠0)
    (C R : Ideal O) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0<P i) (a b : ℝ) (ha : 0<a)
    (hW : ∀ i,Function.support (W i)⊆Set.Icc a b)
    (hne : frozenCoefficient B C R ν W P≠0) (Z : ℝ) (hZ : 1<Z) :
    (∑i,Real.logb Z (P i))-Real.logb Z (C.absNorm:ℝ)+
      (Fintype.card ι:ℝ)*Real.logb Z (min 1 a) ≤
        ∑i : liveIndices B,Real.logb Z (P i) := by
  have h1 := common_slot_width_split B P hP Z
  have h2 := common_frozen_width_le B hB C R hprod ν W P hP a b ha hW hne Z hZ
  linarith

end
end OAI.SevenEighths.Cycle63CommonSupply
#print axioms OAI.SevenEighths.Cycle63CommonSupply.common_slot_width_split
#print axioms OAI.SevenEighths.Cycle63CommonSupply.common_frozen_width_le
#print axioms OAI.SevenEighths.Cycle63CommonSupply.common_live_width_lower
