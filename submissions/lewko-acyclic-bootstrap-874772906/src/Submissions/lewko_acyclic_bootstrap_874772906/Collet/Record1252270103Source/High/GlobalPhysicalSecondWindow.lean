/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal second windows for the modified coefficient. Adapted from the
pinned OpenAI/Hailey Collet CommonSectorWindow and Cycle61 SecondWindows. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.JointWindow
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonWindowColumn CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorEnergy CenteredMomentSecondScaled CenteredMomentSecondWindowSource
open CenteredMomentSecondMaskedWindow CenteredMomentChildAssembly CenteredMomentSmooth
open CenteredMomentFirstSectors CenteredMomentCommonSectorWindow
open CenteredMomentPlainWindowEnergy CenteredMomentExceptionalWindowPair
open CenteredMomentExceptionalWholeWindow
open CenteredMomentConjugateWindow Cycle61InitialMass RayFourExpansion
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance secondWindowSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def modifiedWindowCoefficient (s : Input ι) (modifier : Tuple ι→ℂ)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O)
    (I : supportedColumns (columns s C hC)) : ℂ :=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
      CoupledFirst.coefficient s modifier R seed (C*I) else 0)

def modifiedWindowColumn (s : Input ι) (modifier : Tuple ι→ℂ)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O)
    (η : Character) (t θ X : ℝ) (V : ℝ→ℂ) (z : O) : ℂ :=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>modifiedWindowCoefficient s modifier C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((I.val.absNorm:ℝ)/X)) θ) z

def modifiedPlainColumn (s : Input ι) (modifier : Tuple ι→ℂ)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O)
    (η : Character) (t : ℝ) (z : O) : ℂ :=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>modifiedWindowCoefficient s modifier C hC R seed L I*heightCoeff η t I) z

theorem actual_modified_sector_window (s : Input ι) (modifier : Tuple ι→ℂ)
    (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O)
    (t θ X : ℝ) (V : ℝ→ℂ) (z : O)
    (hτ : ∀I : Ideal O,Supported I→IsCoprime C I→∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) :
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=CoupledFirst.coefficient s modifier R seed
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase V (Real.log ((I.val.absNorm:ℝ)/X)) θ) z=
        modifiedWindowColumn s modifier C hC R seed L τ t θ X V z := by
  dsimp only
  simp_rw [masked_divisor_coefficient η τ χ A C hC hτ]
  rw [sector_rowPolynomial _ (fun I=>(if L∣I then CoupledFirst.coefficient s modifier R seed (C*I) else 0)*
    heightCoeff τ t I*columnPhase V (Real.log ((I.absNorm:ℝ)/X)) θ) C hC z]
  unfold modifiedWindowColumn
  rw [←rowPolynomial_factor]
  apply congrArg (fun c=>rowPolynomial Finset.univ (sourceGenerator (columns s C hC)) c z)
  funext I
  dsimp only [modifiedWindowCoefficient]
  split_ifs <;> simp_all <;> ring

theorem modified_window_integral (s : Input ι) (modifier : Tuple ι→ℂ)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O)
    (η : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    modifiedWindowColumn s modifier C hC R seed L η t θ X V z=
      ∫u : ℝ,columnDensity V hc hs u*FourierBridge.logPhase (θ-u) (Real.log X)*
        modifiedPlainColumn s modifier C hC R seed L η (t+2*Real.pi*(u-θ)) z := by
  have hh:=plain_column_integral Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (modifiedWindowCoefficient s modifier C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span,modifiedWindowColumn,modifiedPlainColumn] using hh

theorem modified_window_integrable (s : Input ι) (modifier : Tuple ι→ℂ)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O)
    (η : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun u : ℝ=>columnDensity V hc hs u*FourierBridge.logPhase (θ-u) (Real.log X)*
      modifiedPlainColumn s modifier C hC R seed L η (t+2*Real.pi*(u-θ)) z) := by
  have hh:=plain_column_integrable Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (modifiedWindowCoefficient s modifier C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span,modifiedPlainColumn] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_modified_sector_window
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_window_integral
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_window_integrable
