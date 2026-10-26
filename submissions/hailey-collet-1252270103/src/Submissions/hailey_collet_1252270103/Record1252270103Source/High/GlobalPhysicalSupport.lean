/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified first-column lower support and scalar normalization.
Adapted from pinned OpenAI/Hailey Collet FirstPhysicalSourceSupport. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceLowerSupport CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSupportedZeroEnergy CenteredMomentFirstPhysicalSourceSupport
local notation "O"=>ActualEisensteinCubic.O
local instance modifiedSupportSumDecEq {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem original_column_lower {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed I:Ideal O)
    (a₁ a₂:ℝ)(ha₁:0≤a₁)(ha₂:0≤a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hn:coefficient s modifier R seed I≠0):
    (∏i,s.lo i)*a₁*a₂*volume s.toData≤(I.absNorm:ℝ) := by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (tupleCoefficient s modifier R seed) I hn
  have hh:=profile_product_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos
    (fun i=>(s.lo_pos i).le) ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product (fun i x hx=>(s.support i hx).1)
    hs₁ hs₂ v (tuple_nonzero s modifier R seed v hv0)
  simpa only [he,map_one,Nat.cast_one,mul_one,div_one,volume,mul_assoc] using hh
theorem original_scalar_volume {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ M:ℝ)
    (hK:0<K)(hA:0<A₀)(hB:0<B₀)(hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block s.η m A t S (coefficient s modifier R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ‖scalar C D hC E K A₀ B₀‖*volume s.toData≤
      (Real.exp M/((∏i,s.lo i)*a₁*a₂))*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  let a:ℝ:=(∏i,s.lo i)*a₁*a₂
  have ha:0<a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  have hV:0<volume s.toData:=volume_pos s.toData
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (coefficient s modifier R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ a (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s modifier R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  have hh:=scalar_volume_bound C D hC E K A₀ B₀ a (volume s.toData) M hK hA hB ha.le hV.le hl hr
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*(a*volume s.toData))/a:=by field_simp
    _≤(Real.exp M*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))/a:=div_le_div_of_nonneg_right hh ha.le
    _=_:=by dsimp only [a];ring

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.original_column_lower
#print axioms QRH.Record1252270103Source.High.CoupledFirst.original_scalar_volume
