/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColoredRectangle
import Candidate.C092.transport.TwistedRawSourceCanonical

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentSourceRectangle CenteredMomentRectangle
open QRH.SilDensitySplit.CubeFree.FP MixedCommonRestriction MixedCommonCoefficient MixedCommonAllocation MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussColoredFreeze_5bee1f6813017be5_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- Actual final mark assignments are frozen before norms. All original
ordinary prefixes and the signed equal-product rectangle remain visible. -/
theorem coloredCanonicalSource_frozen_marks (ω₁ ω₂ : Character) (χ : Character) (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (R : Id) (pool : ι→Finset Id) (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) :
    TwistedRawSource.canonicalSource (idealCoeff ω₁) (idealCoeff ω₂) χ S H R pool ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ d=
    ∑p : (i:ι)→pool i,canonicalFrozenScalar χ R pool ν Wslot P p*
      ∑I : plainSupportPool b (X₁/(Ideal.absNorm d.1 : ℝ)) (Y₁/(Ideal.absNorm d.1 : ℝ)),
      ∑J : plainSupportPool b (X₂/(Ideal.absNorm d.2 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ)),
        coloredCanonicalPairCoefficient χ ω₁ ω₂ ((punctureProduct S H*(∏i,(p i).val))*R) I J*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*I) (d.2*J) := by
  unfold TwistedRawSource.canonicalSource
  have hpools (A B : Finset Id) : MixedTupleRows.pools pool A B=tuplePools pool A B := by
    funext j
    cases j with
    | inl i=>rfl
    | inr j=>fin_cases j <;> rfl
  rw [hpools]
  have hsplit (A B : Finset Id) (f : Tuple ι→ℂ) :
      (∑v∈Fintype.piFinset (tuplePools pool A B),f v)=
      ∑p : (i:ι)→pool i,∑I : A,∑J : B,f (pack (fun i=>(p i).val) I J) := by
    have h := sum_tuplePool pool A B f
    unfold tuplePool at h
    convert h using 1 <;> congr 2
    exact Subsingleton.elim _ _
  refine (hsplit _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  simp only [TwistedRawSource.ordinaryColor,tupleWeight,tupleRestriction,restriction,slotProduct,profileCoefficient,
    pack_slot,pack_left,pack_right,pack_product,map_mul,one_dvd,ite_true]
  unfold canonicalFrozenScalar coloredCanonicalPairCoefficient canonicalPairCoefficient
  have hc : IsCoprime ((punctureProduct S H*(∏i,(p i).val))*R) ((I:Id)*(J:Id)) ↔
      IsCoprime (punctureProduct S H*(∏i,(p i).val)) ((I:Id)*(J:Id)) ∧
      IsCoprime ((I:Id)*(J:Id)) R := by rw [IsCoprime.mul_left_iff]; exact and_congr Iff.rfl isCoprime_comm
  rw [hc]
  simp only [IsCoprime.mul_left_iff]
  split_ifs <;> simp_all only [and_self,and_true,and_false,true_and,false_and,
    not_true_eq_false,not_false_eq_true,ite_true,ite_false,mul_zero,zero_mul] <;> ring


#print axioms coloredCanonicalSource_frozen_marks
end
end QRH.Cycle092.FixedCubeGauss
