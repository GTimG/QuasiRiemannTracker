import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryWidth
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighSelected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondActualWidth
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open CenteredMomentFirstCanonicalFamily Cycle63Moment
open CenteredMomentFirstPhysicalSource CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondActualWidth CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius

/-- Fixed presentation and profile logarithms are absorbed before any parent,
moving source, allocation, ray, or retained row is chosen. -/
theorem eventual_high_fixed_width_cost (N : ℕ) (b ε : ℝ)
    (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
        Real.logb Z (4*(fixedFactor:ℝ))≤ε := by
  let c:=Real.log fixedPresentationCost+2*(N:ℝ)*Real.log b+Real.log (4*(fixedFactor:ℝ))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (c/ε)),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  have he : Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
      Real.logb Z (4*(fixedFactor:ℝ))=c/Real.log Z := by
    dsimp only [Real.logb,c]
    ring
  rw [he]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr
    (by nlinarith [(div_le_iff₀ hε).mp hc])

/-- Original sources of width exponent `Mrow` over a parent of conductor
exponent `conductor` have a common retained width of at most
`Mrow+conductor+ε+ξ/2`. The inactive ideal is paid by the common frequency
generator, not by its coarse source-norm cap. The threshold precedes the parent
and all arithmetic labels. -/
theorem eventual_high_width_gate (N : ℕ) (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(Mrow conductor : ℝ)(C D : Ideal O)(_hC : Supported C)(U : Finset (CommonIndex C D))
        (c e a reserve ξ : ℝ),0≤a → 0≤ reserve → 0≤ξ →
      (Mrow+conductor-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏p∈U,p.val).absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ)))≤Mrow+conductor+ε+ξ/2 := by
  filter_upwards [eventual_high_fixed_width_cost N b ε hε] with Z hz
  refine ⟨hz.1,?_⟩
  intro Mrow conductor C D hC U c e a reserve ξ ha hr hξ
  have hcommon:=actual_common_log_ge_unit C D hC U Z hz.1
  have hfreq:=frequencyLoss_nonneg Z 32 ξ hz.1 (by norm_num) hξ
  linarith [hz.2,le_max_right (c-e) 0]

/-- A small coordinate box suffices for the larger high-density ceiling.
The lower-volume correction changes only coordinate zero. -/
theorem high_child_coordinate_ceiling (reflected left second : Bool)
    (l : FirstSourceLabel)(hC : Supported l.1.1)(hD : Supported l.1.2)
    (C D : Ideal O)(hC₂ : Supported C)(hD₂ : Supported D)
    (heq : primeSupport C=primeSupport D)(U : Finset (CommonIndex C D))
    (Z M A a ξ reserve ε εv width : ℝ)(hZ : 1<Z)
    (hfirst : (l.1.1.absNorm:ℝ)≤Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤Z^(4:ℝ))
    (hsecond : (C.absNorm:ℝ)≤Z^(4:ℝ) ∧ (D.absNorm:ℝ)≤Z^(4:ℝ))
    (hM : |M|≤4)(hA : |A|≤4)(ha : |a|≤4)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤4)(hε : |ε|≤4)(hwidth : width≤1) :
    childHighCoordinates (actualHighCoordinates reflected left second l C D U
      Z M A a ξ reserve ε) εv 2+width≤130 := by
  have hh:=(actual_high_coordinate_box reflected left second l hC hD C D hC₂ hD₂
    heq U Z M A a ξ reserve ε 4 hZ (by norm_num) hfirst hsecond hM hA ha hω hε 2).2
  simp only [childHighCoordinates,show (2:Fin 4)≠0 by decide,ite_false,add_zero]
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
