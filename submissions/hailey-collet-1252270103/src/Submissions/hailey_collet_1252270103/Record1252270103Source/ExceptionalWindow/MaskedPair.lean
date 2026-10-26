/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Masked exceptional windows pay ordinary radical moments, not common ideal powers. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.MaskedAllocation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Record1252270103Second
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentSecondWindowBudget
local notation "O"=>ActualEisensteinCubic.O
local notation "frozenCost"=>CenteredMomentCommonExceptionalCost.frozenProfile
variable {ι:Type*}[Fintype ι]
local instance maskedPairDecidable : DecidableEq ι:=Classical.decEq _

lemma sqrt_masked_bound (A c r n f E α:ℝ)(hc:0≤c)(hr:0<r)(hn:0<n)(hf:0≤f)(hE:0≤E)
    (hA:A≤c^2*r^(2*α)*(f^2/n^2)*E):
    Real.sqrt A≤c*r^α/n*f*Real.sqrt E:=by
  have he:c^2*r^(2*α)*(f^2/n^2)*E=(c*r^α/n*f*Real.sqrt E)^2:=by
    have hp:r^(2*α)=(r^α)^2:=by rw [mul_comm (2:ℝ) α,Real.rpow_mul hr.le,Real.rpow_two]
    rw [hp,mul_pow,mul_pow,div_pow,mul_pow,Real.sq_sqrt hE]
    ring
  exact (Real.sqrt_le_sqrt (hA.trans_eq he)).trans_eq (Real.sqrt_sq (by positivity))

theorem masked_paired_window (s:Input ι)(C D RC RD:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q seed:Ideal O)(U:Finset (CommonIndex C D))
    (Z ε εL α Lraw Cr Mrow C₀ K₀:ℝ)(J:ℕ)(t:ℝ)
    (hα:0≤α)(hZ:0≤Z)(hCr:0≤Cr)(hK₀:0≤K₀):
    windowBudget J t (allocationBudget s C RC (fun B=>maskedAllocatedBudget s C RC B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀))*
    windowBudget J t (allocationBudget s D RD (fun B=>maskedAllocatedBudget s D RD B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀))≤
    ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
      (((commonRadical C C).absNorm:ℝ)^α*((commonRadical D D).absNorm:ℝ)^α/
        ((C.absNorm:ℝ)*(D.absNorm:ℝ)))*(frozenCost s)^2*
      correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀*
      (heightEnvelope t^J*profileMoment J)^2:=by
  let E:=correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀
  have hE:0≤E:=correctedExceptionalBudget_nonneg s S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hZ hCr hK₀
  have hNC:(0:ℝ)<C.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hND:(0:ℝ)<D.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hRC:(0:ℝ)<(commonRadical C C).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero C C))
  have hRD:(0:ℝ)<(commonRadical D D).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero D D))
  have hf:=CenteredMomentCommonExceptionalCost.frozenProfile_nonneg s
  have hc:=sqrt_masked_bound _ _ _ _ _ E α (Nat.cast_nonneg _) hRC hNC hf hE
    (masked_allocation_budget_radical s C RC hC S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀)
  have hd:=sqrt_masked_bound _ _ _ _ _ E α (Nat.cast_nonneg _) hRD hND hf hE
    (masked_allocation_budget_radical s D RD hD S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀)
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul hc hd (Real.sqrt_nonneg _) (by positivity))
    (sq_nonneg (heightEnvelope t^J*profileMoment J))
  unfold windowBudget
  convert hh using 1
  · ring
  · dsimp only [E] at *
    ring_nf
    rw [Real.sq_sqrt hE]
    ring

lemma common_radical_eq (C D:Ideal O)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D):
    commonRadical C C=(∏P:CommonIndex C D,P.val) ∧
      commonRadical D D=(∏P:CommonIndex C D,P.val):=by
  have he:(∏P:CommonIndex C D,P.val)=commonRadical C D:=by
    change (∏P : ↥(CenteredMomentCompleteCommon.commonSupport C D),P.val)=_
    exact (Finset.prod_coe_sort (CenteredMomentCompleteCommon.commonSupport C D) (fun P:Ideal O=>P))
  change IdealMobiusDivisorSum.primeSupport C=IdealMobiusDivisorSum.primeSupport D at hCD
  rw [he]
  constructor <;> simp only [commonRadical,hCD,Finset.inter_self]

theorem masked_paired_window_common_radical (s:Input ι)(C D RC RD:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q seed:Ideal O)(U:Finset (CommonIndex C D))
    (Z ε εL α Lraw Cr Mrow C₀ K₀:ℝ)(J:ℕ)(t:ℝ)
    (hα:0≤α)(hZ:0≤Z)(hCr:0≤Cr)(hK₀:0≤K₀):
    windowBudget J t (allocationBudget s C RC (fun B=>maskedAllocatedBudget s C RC B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀))*
    windowBudget J t (allocationBudget s D RD (fun B=>maskedAllocatedBudget s D RD B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀))≤
    ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)^(2*α)/
        ((C.absNorm:ℝ)*(D.absNorm:ℝ)))*(frozenCost s)^2*
      correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀*
      (heightEnvelope t^J*profileMoment J)^2:=by
  have hh:=masked_paired_window s C D RC RD hC hD S W₁ W₂ Φ Q seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ J t hα hZ hCr hK₀
  rw [(common_radical_eq C D hCD).1,(common_radical_eq C D hCD).2] at hh
  rw [←Real.rpow_add (by
    rw [←(common_radical_eq C D hCD).1]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero C C))),
    show α+α=2*α by ring] at hh
  exact hh
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.sqrt_masked_bound
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.masked_paired_window
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.masked_paired_window_common_radical
