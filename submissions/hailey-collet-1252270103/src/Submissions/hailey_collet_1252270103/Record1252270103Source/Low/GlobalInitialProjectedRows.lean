/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact marked-squarefree centering on the original pools, with all masks retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialPositive
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledInitialMask
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.Projector
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentHeckeExpansion
open QRH.Record1252270103TwoIdeal CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentSourceRectangle CenteredMomentRectangle CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentCommonRadialData
open QRH.Record1252270103Restoration OAI.SevenEighths.Record1252270103Source
open OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.High.CoupledInitial
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def markedSlotSum (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) : ℂ :=
  ∑v : (∀i,S i),squarefreeIndicator (∏i,(v i:Ideal O))*
    (∏i,β i (v i))*rowWeight η m A z t (∏i,(v i:Ideal O))

def markedPositiveRow (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
    squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂*
      markedSlotSum η m A z t S β

theorem marked_modifier_norm (v : Tuple ι) :
    ‖markedSourceModifier 1 1 1 1 (fun _=>1) v‖≤1 := by
  have h:=sourceModifier_norm_le 1 1 1 (fun _ : Ideal O=>1) v 1 zero_le_one (by simp)
  by_cases hs : Squarefree (markedProduct v)
  · simpa only [markedSourceModifier,one_mul,squarefreeIndicator,hs,ite_true,one_mul] using h
  · simp only [markedSourceModifier,one_mul,squarefreeIndicator,hs,ite_false,zero_mul,norm_zero,zero_le_one]

lemma marked_centered_source_finite_rectangle (s : Input ι) (m A z : O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),
      coefficient s (markedSourceModifier 1 1 1 1 (fun _=>1)) 1 1 I*rowWeight s.η m A z s.t I)=
    (∑I:s.plain₁,∑J:s.plain₂,pairProjector I J*rowWeight s.η m A z s.t (I*J)*
      idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ I J)*
        markedSlotSum s.η m A z s.t s.slots
          (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) := by
  have hp : Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
    ext v
    simp only [tuplePool,Fintype.mem_piFinset,Input.pools,tuplePools]
  unfold coefficient tupleCoefficient
  rw [hp,finite_column_regroup,sum_tuplePool]
  unfold markedSlotSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro v hv
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [markedSourceModifier,markedProduct,pack_slot,one_mul,sourceModifier_pack,
    profileCoefficient,pack_left,pack_right,pack_product,isCoprime_one_right,
    one_dvd,ite_true,mul_one,map_mul]
  ring

/-- The literal marked projector and full fixed coprimality mask survive centering. -/
theorem marked_initial_row_difference (s : Input ι) (R : Ideal O) (A z : O)
    (b : ℝ) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b) :
    markedPositiveRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.X₁ s.X₂-
    markedPositiveRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.Y₁ s.Y₂=
    firstNormalizedRow s (markedSourceModifier 1 1 1 1 (fun _=>1)) R A z := by
  unfold firstNormalizedRow
  simp only [CenteredMomentExceptionalAmplitudePair.volume]
  rw [centered_source_initial_mask,marked_centered_source_finite_rectangle,
    squarefree_plain_difference s _ b hb₁ hb₂]
  unfold markedPositiveRow
  rw [←s.same_product]
  ring

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.marked_modifier_norm
#print axioms QRH.Record1252270103Low.marked_centered_source_finite_rectangle
#print axioms QRH.Record1252270103Low.marked_initial_row_difference
