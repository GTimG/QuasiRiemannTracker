import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ExceptionalReference
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace OAI.SevenEighths.Cycle63FinalRadius
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentFirstMixedRoot CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRetainedWidth CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn

/-- This declared second Fourier radius dominates the genuine first common
child's squared volume divided by its physical radius. -/
theorem actual_second_radius_admissible {ι : Type*} [Fintype ι]
    (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t K : ℝ)
    (hK : 0<K) (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    (volume (child s C R B τ t))^2/K≤(b^N*volume s/(C.absNorm:ℝ))^2/K := by
  have hh := common_volume_le N b hb s hcard hs C R B τ t hne
  apply div_le_div_of_nonneg_right _ hK.le
  exact pow_le_pow_left₀ (volume_pos _).le hh 2

/-- The same completed cutoff supplies an actual ball majorant for every
retained row, with no new arithmetic puncture. -/
theorem actual_retained_majorant (R : ℝ) (G V z : O)
    (h : retainedWeight R (normValue ((G*V)*z))≠0) :
    1≤(ballProfile (normValue z/(max 1 (4*R/(normValue G*normValue V))))).re := by
  obtain ⟨_,_,_,_,hz,hu,_⟩ := retained_geometry R G V z h
  have hH : 0< max 1 (4*R/(normValue G*normValue V)) :=
    zero_lt_one.trans_le (le_max_left _ _)
  rw [ballProfile_one _ (div_nonneg (by linarith) hH.le)
    ((div_le_one hH).mpr (hu.trans (le_max_right _ _)))]
  norm_num

end
end OAI.SevenEighths.Cycle63FinalRadius

end Record1252270103Bootstrap.PR67
