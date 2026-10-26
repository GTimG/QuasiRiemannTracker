/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact positive-row centering with the literal ordinary squarefree/hole modifier. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledInitialPlain
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledInitial
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentSourceRectangle CenteredMomentRectangle CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentCommonRadialData
open QRH.Record1252270103Restoration OAI.SevenEighths.Record1252270103Source
open CoupledFirst
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledInitialRowsDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma centered_source_finite_rectangle (s:Input ι)(m A z:O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),
      coefficient s (sourceModifier 1 1 1 (fun _=>1)) 1 1 I*rowWeight s.η m A z s.t I)=
    (∑I:s.plain₁,∑J:s.plain₂,pairProjector I J*rowWeight s.η m A z s.t (I*J)*
      idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ I J)*
      ∏i,rowSlot s.η m A z (s.slots i)
        (fun I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.t := by
  have hp:Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
    ext v
    simp only [tuplePool,Fintype.mem_piFinset,Input.pools,tuplePools]
  unfold coefficient tupleCoefficient
  rw [hp]
  rw [finite_column_regroup,sum_tuplePool,live_slot_product,Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro v hv
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceModifier_pack,profileCoefficient,pack_slot,pack_left,pack_right,
    pack_product,isCoprime_one_right,one_dvd,ite_true,one_mul,mul_one,map_mul]
  ring

lemma squarefree_plain_difference (s:Input ι)(ψ:Ideal O→*₀ℂ)(b:ℝ)
    (hb₁:s.b₁≤b)(hb₂:s.b₂≤b) :
    (∑I:s.plain₁,∑J:s.plain₂,pairProjector I J*ψ (I*J)*
      idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ I J)=
      squarefreePlainSum ψ s.W₁ s.W₂ b s.X₁ s.X₂-
        squarefreePlainSum ψ s.W₁ s.W₂ b s.Y₁ s.Y₂ := by
  have hw:=input_plain_zero s
  have hs₁:Function.support s.W₁⊆Set.Iic b:=fun x hx=>(s.support₁ hx).trans hb₁
  have hs₂:Function.support s.W₂⊆Set.Iic b:=fun x hx=>(s.support₂ hx).trans hb₂
  rw [squarefreePlainSum_finite ψ s.W₁ s.W₂ b s.X₁ s.X₂ s.X₁_pos s.X₂_pos
      hw.1 hw.2 hs₁ hs₂ s.plain₁ s.plain₂
      (fun I h=>s.coverage₁ I (Or.inl (by simpa using h)))
      (fun I h=>s.coverage₂ I (Or.inl (by simpa using h))),
    squarefreePlainSum_finite ψ s.W₁ s.W₂ b s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos
      hw.1 hw.2 hs₁ hs₂ s.plain₁ s.plain₂
      (fun I h=>s.coverage₁ I (Or.inr (by simpa using h)))
      (fun I h=>s.coverage₂ I (Or.inr (by simpa using h)))]
  simp only [idealRectangle,mul_sub,Finset.sum_sub_distrib,mul_assoc]

/-- Same positive volume on both sides, for arbitrary positive raw scales. -/
theorem squarefree_row_difference (s:Input ι)(m A z:O)(b:ℝ)(hb₁:s.b₁≤b)(hb₂:s.b₂≤b) :
    squarefreePositiveSlotRow s.η m A z s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.X₁ s.X₂-
    squarefreePositiveSlotRow s.η m A z s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),
        coefficient s (sourceModifier 1 1 1 (fun _=>1)) 1 1 I*rowWeight s.η m A z s.t I := by
  rw [centered_source_finite_rectangle,squarefree_plain_difference s _ b hb₁ hb₂]
  unfold squarefreePositiveSlotRow
  rw [←s.same_product]
  ring

end
end QRH.Record1252270103Source.High.CoupledInitial
#print axioms QRH.Record1252270103Source.High.CoupledInitial.centered_source_finite_rectangle
#print axioms QRH.Record1252270103Source.High.CoupledInitial.squarefree_row_difference
