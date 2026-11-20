/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussLocalMask

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
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussFreeze_df02c4dc8afc7eda_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

def canonicalFrozenScalar (χ : Character) (R : Id) (pool : ι→Finset Id)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (p : (i:ι)→pool i) : ℂ :=
  if Function.Injective (fun i=>(p i).val) ∧ IsCoprime (∏i,(p i).val) R then
    (∏i,ν i (p i)*Wslot i ((Ideal.absNorm (p i).val : ℝ)/P i))*idealCoeff χ (∏i,(p i).val)
  else 0

def canonicalPairCoefficient (χ : Character) (K I J : Id) : ℂ :=
  if Candidate.FourthPower.SexticSieve.PowerFree 3 (I*J) ∧ IsCoprime K (I*J) then
    idealCoeff χ I*idealCoeff χ J else 0

/-- Actual final mark assignments are frozen before norms. All original
ordinary prefixes and the signed equal-product rectangle remain visible. -/
theorem canonicalSource_frozen_marks (χ : Character) (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (R : Id) (pool : ι→Finset Id) (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) :
    MixedCanonicalSource.source χ S H R pool ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ d=
    ∑p : (i:ι)→pool i,canonicalFrozenScalar χ R pool ν Wslot P p*
      ∑I : plainSupportPool b (X₁/(Ideal.absNorm d.1 : ℝ)) (Y₁/(Ideal.absNorm d.1 : ℝ)),
      ∑J : plainSupportPool b (X₂/(Ideal.absNorm d.2 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ)),
        canonicalPairCoefficient χ ((punctureProduct S H*(∏i,(p i).val))*R) I J*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*I) (d.2*J) := by
  unfold MixedCanonicalSource.source
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
  simp only [tupleWeight,tupleRestriction,restriction,slotProduct,profileCoefficient,
    pack_slot,pack_left,pack_right,pack_product,map_mul,one_dvd,ite_true]
  unfold canonicalFrozenScalar canonicalPairCoefficient
  have hc : IsCoprime ((punctureProduct S H*(∏i,(p i).val))*R) ((I:Id)*(J:Id)) ↔
      IsCoprime (punctureProduct S H*(∏i,(p i).val)) ((I:Id)*(J:Id)) ∧
      IsCoprime ((I:Id)*(J:Id)) R := by rw [IsCoprime.mul_left_iff]; exact and_congr Iff.rfl isCoprime_comm
  rw [hc]
  simp only [IsCoprime.mul_left_iff]
  split_ifs <;> simp_all only [and_self,and_true,and_false,true_and,false_and,
    not_true_eq_false,not_false_eq_true,ite_true,ite_false,mul_zero,zero_mul] <;> ring

#print axioms canonicalSource_frozen_marks
end
end QRH.Cycle092.FixedCubeGauss
