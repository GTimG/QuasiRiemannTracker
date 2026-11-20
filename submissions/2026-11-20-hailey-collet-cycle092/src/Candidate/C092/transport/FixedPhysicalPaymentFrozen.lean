/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedPhysicalPaymentPrimary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentFrozen_87a772343c137d89_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

open Filter CenteredMomentFiniteProfileExceptional

open CenteredMomentSourceLiveColumn CenteredMomentCommonRawCost

/-- A frozen coordinate pays its actual marked norm already from N≤2P.
This weaker first-power payment is sufficient for the full H14 divisor. -/
theorem frozen_inverse_mark_cost {κ : Type*} [Fintype κ]
    (B:Tuple κ) (C R:Id) (ν:κ→Id→ℂ) (W:κ→ℝ→ℂ) (P M:κ→ℝ)
    (hB:∀j,B j≠0) (hP:∀i,0<P i) (hM:∀i,1≤M i)
    (hν:∀i,‖ν i (B (Sum.inl i))‖≤1) (hW:∀i x,‖W i x‖≤M i)
    (hs:∀i,Function.support (W i)⊆Set.Iic 2) :
    (∏i:κ with B (Sum.inl i)≠1,(P i)⁻¹)*‖frozenCoefficient B C R ν W P‖^2 ≤
      (∏i:κ,2*(M i)^2)*(∏i:κ,(B (Sum.inl i)).absNorm:ℝ)⁻¹ := by
  classical
  let N:κ→ℝ:=fun i=>(B (Sum.inl i)).absNorm
  have hN(i):0<N i:=by
    dsimp only [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB (Sum.inl i)))
  have hrhs : 0≤(∏i:κ,2*(M i)^2)*(∏i:κ,(B (Sum.inl i)).absNorm:ℝ)⁻¹:=by positivity
  by_cases hc:frozenCoefficient B C R ν W P=0
  · simpa only [hc,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero] using hrhs
  have hcap(i:κ)(hi:B (Sum.inl i)≠1):N i≤2*P i:=
    frozenCoefficient_mark_cap B C R ν W P 2 hs hP hc i hi
  have hcoef:=frozenCoefficient_norm_le B C R ν W P M
    (fun i=>zero_le_one.trans (hM i)) hν hW
  have hprodN : (∏i:κ with B (Sum.inl i)≠1,N i)=∏i:κ,N i:=by
    apply Finset.prod_subset (Finset.filter_subset _ _)
      (fun i _ hi=>by
        have hi':B (Sum.inl i)=1:=by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hi
        simp [N,hi'])
  have hMprod:(∏i:κ with B (Sum.inl i)≠1,2*(M i)^2) ≤ ∏i:κ,2*(M i)^2:=by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
      (fun i _=>mul_nonneg (by norm_num) (sq_nonneg _))
    intro i _ _
    have hi:=hM i
    nlinarith [sq_nonneg (M i-1)]
  calc
    _ ≤ (∏i:κ with B (Sum.inl i)≠1,(P i)⁻¹)*(∏i:κ with B (Sum.inl i)≠1,M i)^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcoef 2)
        (Finset.prod_nonneg (fun i _=>inv_nonneg.mpr (hP i).le))
    _ = ∏i:κ with B (Sum.inl i)≠1,(M i)^2/P i:=by
      rw [←Finset.prod_pow,←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl;intro i _;ring
    _ ≤ ∏i:κ with B (Sum.inl i)≠1,2*(M i)^2*(N i)⁻¹:=by
      apply Finset.prod_le_prod₀ (fun i _=>div_nonneg (sq_nonneg _) (hP i).le)
      intro i hi
      apply (div_le_iff₀ (hP i)).mpr
      have hcap':=hcap i (Finset.mem_filter.mp hi).2
      have hh:=mul_le_mul_of_nonneg_right hcap' (sq_nonneg (M i))
      have hhh:=mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (hN i).le)
      convert hhh using 1 <;> field_simp [(hN i).ne'] <;> ring
    _ = (∏i:κ with B (Sum.inl i)≠1,2*(M i)^2)*(∏i:κ,N i)⁻¹:=by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_inv_distrib]
      rw [hprodN]
    _ ≤ _:=mul_le_mul_of_nonneg_right hMprod (inv_nonneg.mpr (Finset.prod_nonneg (fun i _=>(hN i).le)))

#print axioms frozen_inverse_mark_cost
end
end QRH.Cycle092.FixedCubeGauss
