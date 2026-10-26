/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified common-window Mellin identity, adapted from pinned OpenAI/Hailey Collet source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstAllocation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy


set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace QRH.Record1252270103Source.High.CoupledFirst
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSmooth
open FourierBridge CenteredMomentAddedZeroUniform Record1252270103Source
open CenteredMomentFirstPhysicalSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance coupledFirstWindowDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedPolynomial (D:OriginalData ι)(modifier:Tuple ι→ℂ)(C L:Ideal O)
    (τ:Character)(t T:ℝ)(z:O):ℂ :=
  ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
    gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
      (sourceGenerator_supported (allocatedData D C L B).columns)
      (modifiedRowCoefficient (allocatedData D C L B) (pulledModifier B.val modifier) τ fixedBadMask t T) z

def commonWindow (D:OriginalData ι)(modifier:Tuple ι→ℂ)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then modifiedBeta D modifier (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

theorem common_window_original_integral (D:OriginalData ι)(modifier:Tuple ι→ℂ)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonWindow D modifier C hC τ t θ X V L z=
      ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
          gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported (allocatedData D C L B).columns)
            (modifiedRowCoefficient (allocatedData D C L B) (pulledModifier B.val modifier) τ fixedBadMask
              (t+2*Real.pi*(w-θ)) T) z:=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then modifiedBeta D modifier (C*I) else 0
  have hh:=gauss_column_integral Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    β τ t θ X hX V hVc hVs z
  simp only [generator_span] at hh
  change commonWindow D modifier C hC τ t θ X V L z=
    ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      commonGauss D modifier C hC τ (t+2*Real.pi*(w-θ)) L z at hh
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have he:=normalized_common_gauss_allocation D modifier hS hp C hC hseed τ
    (t+2*Real.pi*(w-θ)) T L z
  rw [←he]
  ring

theorem common_window_original_integrable (D:OriginalData ι)(modifier:Tuple ι→ℂ)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    Integrable (fun w:ℝ=>columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (modifiedRowCoefficient (allocatedData D C L B) (pulledModifier B.val modifier) τ fixedBadMask (t+2*Real.pi*(w-θ)) T) z):=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then modifiedBeta D modifier (C*I) else 0
  have hh:=(CenteredMomentHeckeWindowEnergy.gauss_column_integrable Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) β τ t θ X hX V hVc hVs z).const_mul
      ((Real.sqrt T:ℂ)⁻¹)
  simp only [generator_span] at hh
  convert hh using 1
  funext w
  rw [←normalized_common_gauss_allocation D modifier hS hp C hC hseed τ (t+2*Real.pi*(w-θ)) T L z]
  change _=(Real.sqrt T:ℂ)⁻¹*(columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
    commonGauss D modifier C hC τ (t+2*Real.pi*(w-θ)) L z)
  ring

end QRH.Record1252270103Source.High.CoupledFirst

end

#print axioms QRH.Record1252270103Source.High.CoupledFirst.common_window_original_integral
#print axioms QRH.Record1252270103Source.High.CoupledFirst.common_window_original_integrable
