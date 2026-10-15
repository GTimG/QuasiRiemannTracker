/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B080
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonSectorWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalIndexedWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PlainChildEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCorrelatedFamily; sha256 73cefd9d510172cfa74624462364203d4a0c4221cff2341a919524c9239208c9 -/
section
                                                                  

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedWidth
open CenteredMomentSupport CenteredMomentSecondRadicalColumns
open CenteredMomentSecondRadicalBudget CenteredMomentSecondSixthSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

def SecondRowConductorBudget (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter→Character) : Prop :=
  ∀w : O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 → ∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm

/-- Retain the row-level conductor evidence from the existing character
construction, before it is weakened to a nonzero-whole-block premise. -/
theorem exists_row_budgeted_second_family (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D)) :
    ∃τ,Family η C D hC hD U τ ∧ SecondRowConductorBudget η C D hC hD U τ := by
  choose τ he ht hrest using fun χ : RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,⟨he,?_,?_⟩,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne' : physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0 := by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩ := physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩ := hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2
  · intro w hw χ
    exact (hrest χ hD hCD w hw).1

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.exists_row_budgeted_second_family

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCorrelatedFamily -/

/- BEGIN ORIGINAL Cycle61.Moment.ActualJointKernel; sha256 f2b6e293d71c1ff42cce50464784315728bf1ef3bd3a64e2ca277479b2e4095a -/
section
                                 
                                                               
                                                           

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentFixedRay
open CenteredMomentChildAssembly CenteredMomentCauchy CenteredMomentSmooth
open CenteredMomentSecondScaled
open CenteredMomentPlainChildEnergy RayFourExpansion
local notation "O" => HeckeFamily.O

structure CanonicalSectorSource where
  C : Ideal O
  D : Ideal O
  supportedC : Supported C
  supportedD : Supported D
  sameSupport : primeSupport C = primeSupport D
  pool : Finset (Ideal O)
  coefficient : Ideal O → ℂ
  character : Character
  height : ℝ
  frequency : O
  projector : Ideal O
  leftRay : RayCharacter
  rightRay : RayCharacter
  leftScale : ℝ
  rightScale : ℝ

abbrev CanonicalSectorSource.LeftIndex (s : CanonicalSectorSource) :=
  sectorPool s.C s.supportedC.1 s.pool
abbrev CanonicalSectorSource.RightIndex (s : CanonicalSectorSource) :=
  sectorPool s.D s.supportedD.1 s.pool

def CanonicalSectorSource.leftCoefficient (s : CanonicalSectorSource)
    (i : s.LeftIndex) : ℂ :=
  divisorCoefficient s.projector (sectorElement s.C s.supportedC.1 s.pool)
    (movingCoefficient s.frequency (sectorElement s.C s.supportedC.1 s.pool)
      (fun I => s.coefficient (s.C*I)*heightCoeff s.character s.height I)) s.leftRay i

def CanonicalSectorSource.rightCoefficient (s : CanonicalSectorSource)
    (i : s.RightIndex) : ℂ :=
  divisorCoefficient s.projector (sectorElement s.D s.supportedD.1 s.pool)
    (movingCoefficient s.frequency (sectorElement s.D s.supportedD.1 s.pool)
      (fun I => s.coefficient (s.D*I)*heightCoeff s.character s.height I)) s.rightRay⁻¹ i

def CanonicalSectorSource.leftLog (s : CanonicalSectorSource) (i : s.LeftIndex) : ℝ :=
  Real.log ((i.val.absNorm:ℝ)/s.leftScale)
def CanonicalSectorSource.rightLog (s : CanonicalSectorSource) (i : s.RightIndex) : ℝ :=
  Real.log ((i.val.absNorm:ℝ)/s.rightScale)

def CanonicalSectorSource.signedWeight (s : CanonicalSectorSource) (q : ℂ) : ℂ :=
  (UniqueFactorizationMonoid.moebius s.projector:ℂ)*
    pairCoeff (phaseTable (primaryGenerator s.C) (primaryGenerator s.D))
      s.leftRay s.rightRay*q

theorem canonical_sector_signed_weight_norm (s : CanonicalSectorSource)
    (q : ℂ) (hq : ‖q‖ ≤ 1) : ‖s.signedWeight q‖ ≤ 1 := by
  have hμ := CubicEisenstein.norm_ideal_moebius_le_one s.projector
  have hp := pairCoeff_norm_le (phaseTable (primaryGenerator s.C) (primaryGenerator s.D))
    1 (fun _ _ => phaseTable_norm _ _ _ _) s.leftRay s.rightRay
  rw [CanonicalSectorSource.signedWeight, norm_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul hμ hp (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans
      (by simpa only [one_mul, mul_one] using hq)

def actualJointLeft {Label : Type*} (source : Label → CanonicalSectorSource)
    (scalar : Label×O → ℂ) (k : Label×O) (i : (source k.1).LeftIndex) : ℂ :=
  scalar k*(source k.1).leftCoefficient i*idealRowHom k.2 i

def actualJointRight {Label : Type*} (source : Label → CanonicalSectorSource)
    (scalar : Label×O → ℂ) (k : Label×O) (i : (source k.1).RightIndex) : ℂ :=
  scalar k*(source k.1).rightCoefficient i*idealRowHom (-k.2) i

/-- Cauchy is applied to the actual source-coordinate × row space before any
first-label or sector-label supremum. Both scalars and the signed residual
projector remain in the literal second-transform expression. -/
theorem actual_joint_sector_kernel_bound (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {Label : Type*} [Fintype Label] [DecidableEq Label]
        (source : Label → CanonicalSectorSource)
        (rows : Finset (Label×O)) (leftScalar rightScalar q : Label×O → ℂ)
        (ρ x : Label×O → ℝ),
      (∀ k ∈ rows, ‖q k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ,
        Real.sqrt (∑ k ∈ rows,
          ‖leftColumn Finset.univ (actualJointLeft source leftScalar k) (V 2)
            (source k.1).leftLog t‖^2) *
        Real.sqrt (∑ k ∈ rows,
          ‖rightColumn Finset.univ (actualJointRight source rightScalar k) (V 3)
            (source k.1).rightLog t‖^2) ≤ E*(1+‖t‖)^J) →
      (1+R)^A * ‖∑ k ∈ rows, (source k.1).signedWeight (q k)*
        (∑ i : (source k.1).LeftIndex, ∑ j : (source k.1).RightIndex,
          (actualJointLeft source leftScalar k i * star (actualJointRight source rightScalar k j))*
            wholeKernel W V R (ρ k) (x k) ((source k.1).leftLog i)
              ((source k.1).rightLog j))‖ ≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_dependent_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro R hR Label _ _ source rows leftScalar rightScalar q ρ x hq hV₀ hV₁ E hE henergy
  exact hbound R hR (Label := Label) (κ := Label×O)
    (α := fun l => (source l).LeftIndex) (β := fun l => (source l).RightIndex)
    rows Prod.fst (actualJointLeft source leftScalar)
    (actualJointRight source rightScalar) (fun l => (source l).leftLog)
    (fun l => (source l).rightLog) ρ x (fun k => (source k.1).signedWeight (q k))
    (fun k hk => canonical_sector_signed_weight_norm _ _ (hq k hk)) hV₀ hV₁ E hE henergy

#print axioms canonical_sector_signed_weight_norm
#print axioms actual_joint_sector_kernel_bound
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.ActualJointKernel -/

/- BEGIN ORIGINAL Cycle61.Moment.JointWindow; sha256 4c4593bc84cd5e4fee824053538c8bbada6150b3da840d88b2a02ff424f73fa8 -/
section
                                                             
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentPlainWindowEnergy CenteredMomentExceptionalWindowPair
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth FourierBridge
open CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_window_column_integral (s : Input ι) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (η : Character) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    windowColumn s C hC R seed L η t θ X V z =
      ∫ u : ℝ, columnDensity V hc hs u*logPhase (θ-u) (Real.log X)*
        normalizedColumn (withHeight s η (t+2*Real.pi*(u-θ))) C hC R seed L z := by
  have hh := plain_column_integral Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (coefficient s C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span, windowColumn, coefficient_polynomial] using hh

theorem actual_window_column_integrable (s : Input ι) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (η : Character) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun u : ℝ => columnDensity V hc hs u*logPhase (θ-u) (Real.log X)*
      normalizedColumn (withHeight s η (t+2*Real.pi*(u-θ))) C hC R seed L z) := by
  have hh := plain_column_integrable Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (coefficient s C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span, coefficient_polynomial] using hh

/-- The common Mellin densities are integrated after summing the matched actual
source coordinates. Characters, masks, heights and scales may vary by coordinate. -/
theorem actual_joint_window_pair {κ : Type*}
    (rows : Finset κ) (s v : κ → Input ι)
    (C D R seed L : κ → Ideal O) (hC : ∀ k, Supported (C k))
    (hD : ∀ k, Supported (D k)) (η τ : κ → Character)
    (t₁ t₂ θ₁ θ₂ X Y : κ → ℝ) (hX : ∀ k, 0 < X k) (hY : ∀ k, 0 < Y k)
    (row₁ row₂ : κ → O) (scalar₁ scalar₂ : κ → ℂ)
    (V₁ V₂ : ℝ → ℂ) (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : ContDiff ℝ ∞ V₁) (hs₂ : ContDiff ℝ ∞ V₂)
    (J₁ J₂ : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ u w : ℝ,
      (∑ k ∈ rows,
        ‖scalar₁ k*normalizedColumn
          (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
          (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
        ‖scalar₂ k*normalizedColumn
          (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
          (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖) ≤
      E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :
    (∑ k ∈ rows,
      ‖scalar₁ k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k)‖*
      ‖scalar₂ k*windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k)‖) ≤
      E*(∫ u : ℝ, (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫ w : ℝ, (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖) := by
  let f := fun k : κ => fun u : ℝ => scalar₁ k*
    (columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁ k-u) (Real.log (X k))*
      normalizedColumn (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
        (C k) (hC k) (R k) (seed k) (L k) (row₁ k))
  let g := fun k : κ => fun w : ℝ => scalar₂ k*
    (columnDensity V₂ hc₂ hs₂ w*logPhase (θ₂ k-w) (Real.log (Y k))*
      normalizedColumn (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
        (D k) (hD k) (R k) (seed k) (L k) (row₂ k))
  have hf (k : κ) : Integrable (f k) :=
    (actual_window_column_integrable (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)).const_mul _
  have hg (k : κ) : Integrable (g k) :=
    (actual_window_column_integrable (v k) (D k) (hD k) (R k) (seed k) (L k)
      (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)).const_mul _
  have hh := paired_integrals rows f g (fun k _ => hf k) (fun k _ => hg k)
    (fun u => (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun w => (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun _ => by positivity) (fun _ => by positivity) E hE ?_
  · have hfEq (k : κ) : (∫ u : ℝ, f k u) = scalar₁ k*
        windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
          (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k) := by
      dsimp only [f]
      rw [integral_const_mul, ←actual_window_column_integral
        (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)]
    have hgEq (k : κ) : (∫ w : ℝ, g k w) = scalar₂ k*
        windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
          (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k) := by
      dsimp only [g]
      rw [integral_const_mul, ←actual_window_column_integral
        (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)]
    simpa only [hfEq, hgEq] using hh
  · intro u w
    simp only [f, g, norm_mul, logPhase_norm, mul_one]
    calc
      _ = (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          ∑ k ∈ rows,
            ‖scalar₁ k*normalizedColumn
              (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
              (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
            ‖scalar₂ k*normalizedColumn
              (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
              (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [norm_mul, norm_mul]
        ring
      _ ≤ (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          (E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :=
        mul_le_mul_of_nonneg_left (hpair u w) (by positivity)
      _ = _ := by ring

#print axioms actual_window_column_integral
#print axioms actual_window_column_integrable
#print axioms actual_joint_window_pair
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.JointWindow -/

/- BEGIN ORIGINAL Cycle61.Moment.JointWindowFamily; sha256 44f69821eff0c1c565c4183b4717eb30627e61ce08013d5cc28eb6bc6e91f458 -/
section
                                 

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentPlainWindowEnergy CenteredMomentExceptionalWindowPair
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth FourierBridge
open CenteredMomentSourceRow
open CenteredMomentHeckeWindowEnergy
local notation "O" => HeckeFamily.O
local instance heterogeneousWindowDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- A single Hilbert energy across different surviving slot sets, before
Mellin integration. The scalar normalization is retained for every row. -/
theorem actual_heterogeneous_joint_window_energy {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ) (slots : κ→Finset α) (s : (k : κ)→Input (slots k))
    (C R seed L : κ→Ideal O) (hC : ∀k,Supported (C k)) (η : κ→Character)
    (t θ X : κ→ℝ) (hX : ∀k,0< X k) (z : κ→O) (scalar : κ→ℂ)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (henergy : ∀u : ℝ,
      (∑k∈rows,‖scalar k*normalizedColumn
        (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
        (C k) (hC k) (R k) (seed k) (L k) (z k)‖^2)≤ E*(1+‖u‖)^(2*J)) :
    (∑k∈rows,‖scalar k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
        E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  let φ (k : κ) (u : ℝ) := logPhase (θ k-u) (Real.log (X k))*
    (scalar k*normalizedColumn (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
      (C k) (hC k) (R k) (seed k) (L k) (z k))
  have hi (k : κ) : Integrable (fun u=>columnDensity V hc hs u*φ k u) := by
    have hh := (actual_window_column_integrable (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t k) (θ k) (X k) (hX k) V hc hs (z k)).const_mul (scalar k)
    convert hh using 1
    funext u
    dsimp [φ]
    ring
  have hb (u : ℝ) : (∑k : rows,‖φ k.val u‖^2)≤ E*((1+‖u‖)^J)^2 := by
    rw [Finset.sum_coe_sort rows (fun k=>‖φ k u‖^2)]
    simpa only [φ,norm_mul,logPhase_norm,one_mul,←pow_mul,Nat.mul_comm] using henergy u
  have hh := finite_weighted_integral_energy (columnDensity V hc hs)
    (fun k : rows=>φ k.val) (fun u=>(1+‖u‖)^J) (fun _=>by positivity)
    E hE (columnDensity_moments V hc hs J) (fun k=>hi k.val) hb
  have he (k : κ) : (∫u : ℝ,columnDensity V hc hs u*φ k u)=
      scalar k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t k) (θ k) (X k) V (z k) := by
    rw [actual_window_column_integral (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t k) (θ k) (X k) (hX k) V hc hs (z k),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [φ]
    ring
  simp only [he] at hh
  rw [Finset.sum_coe_sort rows (fun k=>‖scalar k*windowColumn (s k) (C k) (hC k)
    (R k) (seed k) (L k) (η k) (t k) (θ k) (X k) V (z k)‖^2)] at hh
  exact hh

/-- The second-stage window pair remains joint when different first
allocations retain different subsets of the original slot dictionary. -/
theorem actual_heterogeneous_joint_window_pair {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ) (slots : κ→Finset α) (s v : (k : κ)→Input (slots k))
    (C D R seed L : κ → Ideal O) (hC : ∀ k, Supported (C k))
    (hD : ∀ k, Supported (D k)) (η τ : κ → Character)
    (t₁ t₂ θ₁ θ₂ X Y : κ → ℝ) (hX : ∀ k, 0 < X k) (hY : ∀ k, 0 < Y k)
    (row₁ row₂ : κ → O) (scalar₁ scalar₂ : κ → ℂ)
    (V₁ V₂ : ℝ → ℂ) (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : ContDiff ℝ ∞ V₁) (hs₂ : ContDiff ℝ ∞ V₂)
    (J₁ J₂ : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ u w : ℝ,
      (∑ k ∈ rows,
        ‖scalar₁ k*normalizedColumn
          (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
          (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
        ‖scalar₂ k*normalizedColumn
          (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
          (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖) ≤
      E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :
    (∑ k ∈ rows,
      ‖scalar₁ k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k)‖*
      ‖scalar₂ k*windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k)‖) ≤
      E*(∫ u : ℝ, (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫ w : ℝ, (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖) := by
  let f := fun k : κ => fun u : ℝ => scalar₁ k*
    (columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁ k-u) (Real.log (X k))*
      normalizedColumn (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
        (C k) (hC k) (R k) (seed k) (L k) (row₁ k))
  let g := fun k : κ => fun w : ℝ => scalar₂ k*
    (columnDensity V₂ hc₂ hs₂ w*logPhase (θ₂ k-w) (Real.log (Y k))*
      normalizedColumn (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
        (D k) (hD k) (R k) (seed k) (L k) (row₂ k))
  have hf (k : κ) : Integrable (f k) :=
    (actual_window_column_integrable (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)).const_mul _
  have hg (k : κ) : Integrable (g k) :=
    (actual_window_column_integrable (v k) (D k) (hD k) (R k) (seed k) (L k)
      (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)).const_mul _
  have hh := paired_integrals rows f g (fun k _ => hf k) (fun k _ => hg k)
    (fun u => (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun w => (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun _ => by positivity) (fun _ => by positivity) E hE ?_
  · have hfEq (k : κ) : (∫ u : ℝ, f k u) = scalar₁ k*
        windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
          (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k) := by
      dsimp only [f]
      rw [integral_const_mul, ←actual_window_column_integral
        (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)]
    have hgEq (k : κ) : (∫ w : ℝ, g k w) = scalar₂ k*
        windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
          (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k) := by
      dsimp only [g]
      rw [integral_const_mul, ←actual_window_column_integral
        (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)]
    simpa only [hfEq, hgEq] using hh
  · intro u w
    simp only [f, g, norm_mul, logPhase_norm, mul_one]
    calc
      _ = (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          ∑ k ∈ rows,
            ‖scalar₁ k*normalizedColumn
              (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
              (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
            ‖scalar₂ k*normalizedColumn
              (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
              (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [norm_mul, norm_mul]
        ring
      _ ≤ (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          (E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :=
        mul_le_mul_of_nonneg_left (hpair u w) (by positivity)
      _ = _ := by ring

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.actual_heterogeneous_joint_window_pair
#print axioms OAI.SevenEighths.Cycle61Moment.actual_heterogeneous_joint_window_energy

end
/- END ORIGINAL Cycle61.Moment.JointWindowFamily -/
