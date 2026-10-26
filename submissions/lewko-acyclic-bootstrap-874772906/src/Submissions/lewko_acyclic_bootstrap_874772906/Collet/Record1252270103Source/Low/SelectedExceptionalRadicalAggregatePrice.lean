/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full original second blocks inject into the actual radical mass family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalRadicalAggregateMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalCenteredPrice
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalFiniteSum
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSectorWeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open Cycle61InitialMass Record1252270103Second Record1252270103CommonGeometry
open OAI.SevenEighths.Record1252270103Source ExceptionalRadical
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical SecondSectorDatum
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentHeckeColumnWindow CenteredMomentMobiusRegroup CenteredMomentDivisorBoundary
open CenteredMomentSecondWindowBudget CenteredMomentSecondInputCapacitySource
open CenteredMomentFirstAmplificationChoice
open QRH.Record1252270103Low
open Low.SelectedExceptionalNormalized Low.SelectedExceptionalInitialCaps
open Low.SelectedExceptionalNormalizedMasked

lemma radicalPair_nonneg {ι:Type*}[Fintype ι](s:Input ι)(T:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))
    (Q C D L:Ideal O)(U:Finset (CommonIndex C D))
    (Z ε εL power Lraw Cr Mrow C₀ K₀:ℝ)(J:ℕ)(t:ℝ)
    (hZ:0≤Z)(hCr:0≤Cr)(hK₀:0≤K₀):
    0≤radicalPair s T W₁ W₂ Φ Q C D L U Z ε εL power Lraw Cr Mrow C₀ K₀ J t:=by
  have hb:=correctedExceptionalBudget_nonneg s T W₁ W₂ Φ Q C D L U Z ε εL power Lraw Cr Mrow C₀ K₀ hZ hCr hK₀
  unfold radicalPair
  positivity

/-- The full original artificial-divisor pool is paid, and the unclipped
radial cost comes from the nonzero ORIGINAL block. The complementary selected
block is allowed to vanish. -/
theorem eventually_normalized_divisor_price (B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃Hmass:ℝ,0<Hmass ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α:Type*}[Fintype α](d:SecondInputDatum α)(T:Finset (ℕ×ℕ))
      (W₁ W₂:𝓢(ℝ,ℂ))(Q:Ideal O)(ε εL Lraw C₀ K₀:ℝ)(J:ℕ),
    0≤εL→0≤K₀→
    (∀I:sectorPool d.D d.hD.1 (finiteColumns (Fintype.piFinset d.input.pools)),
      ((I:Ideal O).absNorm:ℝ)≤Z^B)→
    ∀(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ)),(∀z∈rows,z≠0)→
    physicalBlock d.input.η d.input.t (finiteColumns (Fintype.piFinset d.input.pools)) β
      d.C d.D d.hC d.hD d.inactive d.radius rows W d.K d.dyad≠0→
    normalizer d.C d.D d.inactive*
      radicalDivisorSum d T W₁ W₂ ballProfile Q Z ε εL (499/1000)
        (Cycle61FinalNatural.retainedScale d.radius d.C d.D d.inactive) 2 Lraw C₀ K₀ J/volume d.input≤
      Hmass*Z^(δ+B*εL)*(CenteredMomentCommonExceptionalCost.frozenProfile d.input)^2*
        centeredProfileFactor d.input T W₁ W₂ ballProfile Q Z ε (499/1000) Lraw 2 C₀ K₀*
        volume d.input*(4*d.radius)^(1/6:ℝ)*
        (heightEnvelope d.input.t^J*profileMoment J)^2*allocationRadical d.input d.C d.D := by
  obtain ⟨Hmass,hHmass,hmass⟩:=actual_full_divisor_budget B δ hB hδ
  refine ⟨Hmass,hHmass,?_⟩
  filter_upwards [hmass] with Z hz
  refine ⟨hz.1,?_⟩
  intro α inst d T W₁ W₂ Q ε εL Lraw C₀ K₀ J hεL hK₀ hcap β rows W hrows hne
  let H:=Cycle61FinalNatural.retainedScale d.radius d.C d.D d.inactive
  let F:=((actualAllocations d.input.pools d.C).card:ℝ)*((actualAllocations d.input.pools d.D).card:ℝ)*
    (CenteredMomentCommonExceptionalCost.frozenProfile d.input)^2*(heightEnvelope d.input.t^J*profileMoment J)^2
  let g:=(Ideal.absNorm (∏P:CommonIndex d.C d.D,P.val):ℝ)^(2*(499/1000:ℝ))/
    ((d.C.absNorm:ℝ)*(d.D.absNorm:ℝ))
  have hF:0≤F:=by dsimp [F];positivity
  have hg:0≤g:=by dsimp [g];positivity
  have hv:=volume_pos d.input
  have hn:0≤normalizer d.C d.D d.inactive:=(normalizer_pos d.C d.D d.hC d.inactive).le
  have hs:=hz.2 d.input T W₁ W₂ ballProfile Q d.C d.D d.inactive ε εL (499/1000)
    Lraw 2 (Real.logb Z H) C₀ K₀ (F*g) hεL (by norm_num) hK₀ (mul_nonneg hF hg)
    Finset.univ (fun I:sectorPool d.D d.hD.1 (finiteColumns (Fintype.piFinset d.input.pools))=>(I:Ideal O))
    (fun I _=>(sectorPool_supported d.D d.hD.1 _ I).1) (fun I _=>hcap I)
  have hs':radicalDivisorSum d T W₁ W₂ ballProfile Q Z ε εL (499/1000) H 2 Lraw C₀ K₀ J≤
      Hmass*Z^(δ+B*εL)*(F*g)*correctedExceptionalBudget d.input T W₁ W₂ ballProfile Q d.C d.D 1 d.inactive
        Z ε εL (499/1000) Lraw 2 (Real.logb Z H) C₀ K₀ := by
    convert hs using 1
    unfold radicalDivisorSum
    apply Finset.sum_congr rfl
    intro L hL
    dsimp only [radicalPair,F,g]
    ring
  have hp:=actual_centered_radical_budget d.input T W₁ W₂ ballProfile Q
    d.input.η d.input.t (finiteColumns (Fintype.piFinset d.input.pools)) β
    d.C d.D d.hC d.hD d.sameSupport d.inactive d.radius rows hrows W d.K d.K_pos d.dyad hne
    Z ε εL (499/1000) Lraw 2 C₀ K₀ hz.1 (by norm_num) hK₀
  calc
    _≤(Hmass*Z^(δ+B*εL)*F)*(normalizer d.C d.D d.inactive*g*
      correctedExceptionalBudget d.input T W₁ W₂ ballProfile Q d.C d.D 1 d.inactive
        Z ε εL (499/1000) Lraw 2 (Real.logb Z H) C₀ K₀/volume d.input):=by
      convert mul_le_mul_of_nonneg_left hs' (div_nonneg hn hv.le) using 1 <;> ring
    _≤(Hmass*Z^(δ+B*εL)*F)*(centeredProfileFactor d.input T W₁ W₂ ballProfile Q
      Z ε (499/1000) Lraw 2 C₀ K₀*volume d.input*(4*d.radius)^(1/6:ℝ)*
      (Ideal.absNorm (∏P:CommonIndex d.C d.D,P.val):ℝ)^(2*(499/1000:ℝ)-2)):=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hHmass.le (Real.rpow_nonneg (zero_lt_one.trans hz.1).le _)) hF)
    _=_:=by dsimp only [F,allocationRadical];ring
end
end QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.radicalPair_nonneg
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.eventually_normalized_divisor_price
