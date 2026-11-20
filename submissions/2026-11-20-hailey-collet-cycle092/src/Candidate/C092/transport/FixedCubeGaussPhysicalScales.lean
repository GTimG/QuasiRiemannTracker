/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussPaymentLift

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
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussPhysicalScales_721606f155021cd4_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- The literal H8 physical rectangle is shortened only by its two ordinary
prefixes. Marked-coordinate payments remain in the frozen scalar. -/
lemma physical_shortened_products (r : Source ι a b) (d : Id×Id) :
    (r.X₁/(d.1.absNorm:ℝ))*(r.X₂/(d.2.absNorm:ℝ))=r.T/((d.1.absNorm:ℝ)*d.2.absNorm) ∧
    (r.Y₁/(d.1.absNorm:ℝ))*(r.Y₂/(d.2.absNorm:ℝ))=r.T/((d.1.absNorm:ℝ)*d.2.absNorm) := by
  constructor
  · rw [div_mul_div_comm,r.hpX]
  · rw [div_mul_div_comm,r.hpY]

/-- Exact relation between the ordinary shortening and the full allocation
norm used in H14: their quotient is the frozen marked norm product. -/
lemma full_allocation_q_factor (r : Source ι a b) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) :
    ((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*
      (∏j,((B.val j*liftPrimaryTuple B.val E.val j).absNorm:ℝ))=
    ((primaryOrdinaryPrefix r G L B E).1.absNorm:ℝ)*
      (primaryOrdinaryPrefix r G L B E).2.absNorm*
      (∏i:ι,((B.val (Sum.inl i)*liftPrimaryTuple B.val E.val (Sum.inl i)).absNorm:ℝ)) := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_two]
  unfold primaryOrdinaryPrefix commonLiveD
  simp only [Prod.fst,Prod.snd,liftPrimaryTuple_ordinary,map_mul,Nat.cast_mul]
  ring

#print axioms physical_shortened_products
#print axioms full_allocation_q_factor
end
end QRH.Cycle092.FixedCubeGauss
