/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussPaymentLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussFrozenFactors_7c048a846e438871_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

lemma arbitrary_live_normalization_ne (r : Source ι a b) (B : Tuple ι) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B=>r.P i.val)≠0 := by
  unfold MixedLiveNormalization.normalization
  apply mul_ne_zero
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂))).ne')
  · exact Finset.prod_ne_zero_iff.mpr (fun i _=>inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le (r.hP i.val))).ne'))

/-- Exact native normalization ratio: each frozen marked coordinate contributes
its own inverse square-root scale and no ordinary-prefix factor. -/
lemma normalization_ratio_eq_frozen_product (r : Source ι a b) (B : Tuple ι) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B=>r.P i.val))⁻¹=
    ∏i : ι with B (Sum.inl i)≠1,(Real.sqrt (r.P i):ℂ)⁻¹ := by
  have hp : (∏i:ι,(Real.sqrt (r.P i):ℂ)⁻¹)=
      (∏i:liveIndices B,(Real.sqrt (r.P i.val):ℂ)⁻¹)*
      (∏i:ι with B (Sum.inl i)≠1,(Real.sqrt (r.P i):ℂ)⁻¹) := by
    rw [Finset.prod_coe_sort (liveIndices B) (fun i:ι=>(Real.sqrt (r.P i):ℂ)⁻¹)]
    unfold liveIndices
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i:ι=>B (Sum.inl i)=1)
      (fun i=>(Real.sqrt (r.P i):ℂ)⁻¹)).symm
  have hn : MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P=
      MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B=>r.P i.val)*
      (∏i:ι with B (Sum.inl i)≠1,(Real.sqrt (r.P i):ℂ)⁻¹) := by
    unfold MixedLiveNormalization.normalization
    rw [hp]
    ring
  rw [hn,mul_right_comm,mul_inv_cancel₀ (arbitrary_live_normalization_ne r B),one_mul]

lemma normalization_ratio_norm_sq (r : Source ι a b) (B : Tuple ι) :
    ‖MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B=>r.P i.val))⁻¹‖^2=
    ∏i : ι with B (Sum.inl i)≠1,(r.P i)⁻¹ := by
  rw [normalization_ratio_eq_frozen_product,norm_prod,←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow,Real.sq_sqrt (zero_le_one.trans (r.hP i))]

lemma frozenCoefficient_profile_nonzero (B : Tuple ι) (C R : Id)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (h : frozenCoefficient B C R ν Wslot P≠0) (i : ι) (hi : B (Sum.inl i)≠1) :
    Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i)≠0 := by
  unfold frozenCoefficient at h
  exact right_ne_zero_of_mul
    (Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul h) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))

/-- Active frozen marked coordinates satisfy the original annulus cap.
This follows from their actual profile value, with no pool-size estimate. -/
lemma frozenCoefficient_mark_cap (B : Tuple ι) (C R : Id)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (bslot : ℝ)
    (hs : ∀i,Function.support (Wslot i)⊆Set.Iic bslot)
    (hP : ∀i,0<P i) (h : frozenCoefficient B C R ν Wslot P≠0)
    (i : ι) (hi : B (Sum.inl i)≠1) :
    (Ideal.absNorm (B (Sum.inl i)):ℝ)≤bslot*P i :=
  (div_le_iff₀ (hP i)).mp (hs i (frozenCoefficient_profile_nonzero B C R ν Wslot P h i hi))

lemma frozenCoefficient_norm_le (B : Tuple ι) (C R : Id)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hM : ∀i,0≤M i) (hν : ∀i,‖ν i (B (Sum.inl i))‖≤1)
    (hW : ∀i x,‖Wslot i x‖≤M i) :
    ‖frozenCoefficient B C R ν Wslot P‖≤∏i : ι with B (Sum.inl i)≠1,M i := by
  unfold frozenCoefficient
  by_cases hc : IsCoprime C R
  · simp only [hc,ite_true,mul_one,norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro i _
    rw [norm_mul]
    exact (mul_le_mul (hν i) (hW i _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simp only [hc,ite_false,mul_zero,norm_zero]
    exact Finset.prod_nonneg (fun i _=>hM i)

#print axioms normalization_ratio_eq_frozen_product
#print axioms normalization_ratio_norm_sq
#print axioms frozenCoefficient_profile_nonzero
#print axioms frozenCoefficient_mark_cap
#print axioms frozenCoefficient_norm_le
end
end QRH.Cycle092.FixedCubeGauss
