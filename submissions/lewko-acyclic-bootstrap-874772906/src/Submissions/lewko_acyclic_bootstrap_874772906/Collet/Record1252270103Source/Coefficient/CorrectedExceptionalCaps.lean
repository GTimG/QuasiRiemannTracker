/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite polynomial caps for the actual complete-divisor children. No energy
estimate is part of this input. Both puncture and correction are updated. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedGeometryCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedRowCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedForcedUniformEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open ConcretePrimeRowBridge CompletedGauss CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentChildRows CenteredMomentSecondRadicalBudget
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance correctedExceptionalCapsDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev correctedForcedLabels (s : Input ι) (A₁ A₂ Df K R seed : Ideal O) (P : Finset (Ideal O)) :=
  forcedLabels seed (forcedSource s (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)) R seed)

structure CorrectedForcedCaps (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b Z BA Bpool Bplain BD BR ell : ℝ) (depth : ℕ)
    (A₁ A₂ Df K R seed : Ideal O) (P : Finset (Ideal O)) : Prop where
  profile_left : s.W₁=(W₁:ℝ→ℂ)
  profile_right : s.W₂=(W₂:ℝ→ℂ)
  support_left : s.b₁≤b
  support_right : s.b₂≤b
  puncture_ne : R≠0
  frozen_left_ne : A₁≠0
  frozen_right_ne : A₂≠0
  correction_dvd : Df∣R
  frozen_norm : ∀Cf : correctedForcedLabels s A₁ A₂ Df K R seed P,
    ∀B : actualAllocations s.pools (Cf:Ideal O),
      (((A₁*B.val (Sum.inr 0))*(A₂*B.val (Sum.inr 1))).absNorm:ℝ)≤Z^BA
  correction_norm : ∀Cf : correctedForcedLabels s A₁ A₂ Df K R seed P,((Df*Cf).absNorm:ℝ)≤Z^BD
  puncture_norm : ∀Cf : correctedForcedLabels s A₁ A₂ Df K R seed P,((R*Cf).absNorm:ℝ)≤Z^BR
  pool_nonempty : 0<P.card
  pool_prime : ∀p∈P,Prime p
  pool_sixteen : ∀p∈P,16≤p.absNorm
  pool_floor : ∀p∈P,Z^ell≤(p.absNorm:ℝ)
  pool_upper : ∀p∈P,(p.absNorm:ℝ)≤Z^Bpool
  pool_avoids : ∀p∈P,∀i I,I∈s.slots i→¬p∣I
  pool_size : 2*(BD/ell+depth+1)≤P.card
  depth_cap : Bplain/ell≤depth
  plain_cap : b^2*(s.X₁*s.X₂)≤Z^Bplain

theorem forced_source_geometries_of_caps (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b Z BA Bpool Bplain BD BR ell : ℝ) (depth : ℕ)
    (A₁ A₂ Df K R seed : Ideal O) (P : Finset (Ideal O))
    (hb : 0≤b) (hZ : 1<Z) (hell : 0<ell)
    (hcap : CorrectedForcedCaps s W₁ W₂ b Z BA Bpool Bplain BD BR ell depth A₁ A₂ Df K R seed P)
    (τ : Character) (t : ℝ)
    (Cf : correctedForcedLabels s A₁ A₂ Df K R seed P)
    (B : actualAllocations s.pools (Cf:Ideal O)) :
    CorrectedSourceGeometry (child s Cf R B τ t) W₁ W₂ b Z BA Bpool depth
      (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (Df*Cf)
      (K*Collision.markedProduct B.val) (R*Cf) P := by
  exact corrected_child_geometry_of_caps s Cf R (forcedLabel_ne_zero seed _ Cf) B τ t
    W₁ W₂ b Z BA Bpool Bplain BD ell depth A₁ A₂ Df K P
    hcap.profile_left hcap.profile_right hcap.support_left hcap.support_right hb hZ hell
    hcap.puncture_ne hcap.frozen_left_ne hcap.frozen_right_ne hcap.correction_dvd
    (hcap.frozen_norm Cf B) (hcap.correction_norm Cf)
    hcap.pool_nonempty hcap.pool_prime hcap.pool_sixteen hcap.pool_floor hcap.pool_upper
    hcap.pool_avoids hcap.pool_size hcap.depth_cap hcap.plain_cap

theorem forced_selector_geometries_of_caps (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b Z BA Bpool Bplain BD BR ell : ℝ) (depth : ℕ)
    (A₁ A₂ Df K R seed : Ideal O) (P : Finset (Ideal O))
    (hcap : CorrectedForcedCaps s W₁ W₂ b Z BA Bpool Bplain BD BR ell depth A₁ A₂ Df K R seed P)
    (Q : Ideal O) (η : Character) (χ : RayFourExpansion.RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (brad H Bη Bfreq BH : ℝ) (hZ : 1<Z) (hb : 0≤brad) (hH : 0<H)
    (Φ : 𝓢(ℝ,ℂ)) (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic brad)
    (hη : (η.modulus.absNorm:ℝ)≤Z^Bη)
    (hA : ((Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}).absNorm:ℝ)≤Z^Bfreq)
    (hscale : H≤Z^BH) (hfixed : (fixedFactor:ℝ)*brad≤Z)
    (Cf : correctedForcedLabels s A₁ A₂ Df K R seed P) :
    CorrectedRowGeometry Q η χ C D U (R*Cf) Z (Bη+BR+Bfreq+BH+1) brad (Real.logb Z H)
      (fun z=>z≠0 ∧ CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) Φ H := by
  exact corrected_selector_row_geometry Q η χ C D hC U (R*Cf)
    (mul_ne_zero hcap.puncture_ne (forcedLabel_ne_zero seed _ Cf)) m hm hmLam hm2
    Z brad H Bη BR Bfreq BH hZ hb hH Φ hs hη (hcap.puncture_norm Cf) hA hscale hfixed
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.forced_source_geometries_of_caps
#print axioms OAI.SevenEighths.Record1252270103Source.forced_selector_geometries_of_caps
