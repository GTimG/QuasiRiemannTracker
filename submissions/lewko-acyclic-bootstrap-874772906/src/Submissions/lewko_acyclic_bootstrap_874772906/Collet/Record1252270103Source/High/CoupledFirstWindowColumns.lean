/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal modified column/common-window transport, adapted from pinned OpenAI/Hailey Collet source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ConjugateWindow


set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace QRH.Record1252270103Source.High.CoupledFirst
open OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge CenteredMomentAddedZeroUniform Record1252270103Source
open CenteredMomentFirstPhysicalSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance coupledFirstWindowColumnsDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem column_window_common (s:OriginalData ι)(modifier:Tuple ι→ℂ)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then modifiedBeta s modifier (C*I) else 0)*heightCoeff τ t I)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
        commonWindow s modifier C hC τ t θ X V L z:=by
  simp only [ha,element_norm]
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then modifiedBeta s modifier (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) z]
  unfold commonWindow
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem column_window_original_integral (s:OriginalData ι)(modifier:Tuple ι→ℂ)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then modifiedBeta s modifier (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
      ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        allocatedPolynomial s modifier C L τ (t+2*Real.pi*(w-θ)) T z:=by
  rw [column_window_common s modifier Q C hQ hC hQC τ t θ X V L a ha z]
  exact common_window_original_integral s modifier hS hp C hC hseed τ t T θ X hX V hVc hVs L z

theorem column_star_window_original_integral (s:OriginalData ι)(modifier:Tuple ι→ℂ)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then modifiedBeta s modifier (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) (-z)=
      ∫w:ℝ,columnDensity (fun x=>star (V x)) (conjugate_compact V hVc)
        (conjugate_smooth V hVs) w*logPhase (-θ-w) (Real.log X)*
        allocatedPolynomial s modifier C L τ (t+2*Real.pi*(w-(-θ))) T (-z):=by
  simp only [star_columnPhase]
  exact column_window_original_integral s modifier hS hp Q C hQ hC hQC hseed τ t T (-θ) X hX
    (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) L a ha (-z)

end QRH.Record1252270103Source.High.CoupledFirst

end

#print axioms QRH.Record1252270103Source.High.CoupledFirst.column_window_common
#print axioms QRH.Record1252270103Source.High.CoupledFirst.column_window_original_integral
#print axioms QRH.Record1252270103Source.High.CoupledFirst.column_star_window_original_integral
