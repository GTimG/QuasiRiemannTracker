/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Geometric data for the actual corrected source; no energy bound occurs here. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedForcedScale
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredPositiveEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open ConcretePrimeRowBridge CompletedGauss CanonicalRowCompletion
open CenteredExceptionalProfile CenteredMomentRestrictedSource
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance correctedGeometryTupleDecidableEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

structure CorrectedSourceGeometry (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b Z BA Bpool : ℝ) (depth : ℕ) (A₁ A₂ Df K R : Ideal O) (P : Finset (Ideal O)) : Prop where
  profile_left : s.W₁=(W₁:ℝ→ℂ)
  profile_right : s.W₂=(W₂:ℝ→ℂ)
  support_left : s.b₁≤b
  support_right : s.b₂≤b
  puncture_ne : R≠0
  frozen_left_ne : A₁≠0
  frozen_right_ne : A₂≠0
  correction_dvd : Df∣R
  frozen_norm : ((A₁*A₂).absNorm:ℝ)≤Z^BA
  pool_nonempty : 0<P.card
  pool_prime : ∀p∈P,Prime p
  pool_norm_lower : ∀p∈P,16≤p.absNorm
  pool_norm_upper : ∀p∈P,(p.absNorm:ℝ)≤Z^Bpool
  pool_avoids : ∀p∈P,∀i I,I∈s.slots i→¬p∣I
  pool_budget : 2*((idealDividingPool P Df).card+depth+1:ℝ)≤P.card
  residual_count : ∀n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂,
    Squarefree ((A₁*n.1)*(A₂*n.2))→
    frozenProfile W₁ W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0→
      (idealDividingPool P (n.1*n.2)).card≤depth

structure CorrectedRowGeometry (Q : Ideal O) (η : Character) (χ : RayFourExpansion.RayCharacter)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : Ideal O)
    (Z Bχ Cr Mrow : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) : Prop where
  row_nonzero : ∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→z≠0
  inducing : ∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→
    FixedInducingRow (childCharacter η χ) Q (fixedBadMask*idealGenerator R)
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z
  conductor : ∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→
    (HeckeRowClosure.rowConductorBound (childCharacter η χ) (fixedBadMask*idealGenerator R) 1
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z):ℝ)≤Z^Bχ
  radius : ∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→
    (Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^Mrow

def exceptionalRowCost (Q C D : Ideal O) (U : Finset (CommonIndex C D)) (Z Cr Mrow : ℝ) : ℝ :=
  768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
    Z^((Mrow-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6)

lemma exceptionalRowCost_nonneg (Q C D : Ideal O) (U : Finset (CommonIndex C D))
    (Z Cr Mrow : ℝ) (hZ : 0≤Z) (hCr : 0≤Cr) :
    0≤exceptionalRowCost Q C D U Z Cr Mrow := by
  unfold exceptionalRowCost
  positivity

/-- Exact family transport at the completed norm, retaining the seed and keep. -/
theorem source_family_energy (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R seed : Ideal O) (hCR : C∣R) (η τ : Character) (χ : RayFourExpansion.RayCharacter) (A : O)
    (hτ : ∀I : Ideal O,Supported I→IsCoprime C I→∀t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*RayFourExpansion.rayCharacter χ (primaryGenerator I))
    (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (QRH.Record1252270103Source.High.CoupledFirst.coefficient s modifier R seed)
      (heightCoeff τ t) Φ H/volume s=
      ∑'z : O,if keep z then
        (‖modifiedSourceRow s modifier R seed (childCharacter η χ) t (A*z)‖^2/volume s)*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0 := by
  rw [source_energy_eq_modified_rows s modifier R seed τ t keep Φ H,←tsum_div_const]
  apply tsum_congr
  intro z
  rw [modified_source_family_row s modifier C R seed hCR η τ χ A hτ]
  split_ifs <;> ring
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.source_family_energy
