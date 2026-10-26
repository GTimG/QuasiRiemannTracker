/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual first geometric character inherits its fixed-anchor conductor
cap. The anchor is fixed before the common-label and source data move. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularSelectedStateCaps
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentFirstPhysicalSource CenteredMomentOriginalCommonHarmonic
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission.FirstFamily
local notation "O"=>HeckeFamily.O

theorem eventually_actual_first_character_cap (ηanchor:Character)(ηloss:ℝ)(hηloss:0<ηloss) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι]
      (reflected:Bool)(s:Input ι)(modifier:Tuple ι→ℂ),s.η=ηanchor→
      ∀(R seed:Ideal O)(K ξ Bfirst:ℝ)(hK:0<K)(bin:ℤ×(Fin 5→ℤ))
        (j:FirstColumnIndex (geometryFirstSource s modifier R seed K Z ξ hK bin)),
      Squarefree seed→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^Bfirst→
      ((columnCharacter reflected s modifier R seed K Z ξ hK bin j).modulus.absNorm:ℝ)≤
        Z^(2*Bfirst+ηloss) := by
  filter_upwards [(tendsto_rpow_atTop hηloss).eventually
    (eventually_ge_atTop (fixedPresentationCost*(ηanchor.modulus.absNorm:ℝ))),
    eventually_gt_atTop (1:ℝ)] with Z hconstant hZ
  refine ⟨hZ,?_⟩
  intro ι instι instDec reflected s modifier hη R seed K ξ Bfirst hK bin j hs hz₁ hz₂ hsource
  have hZ0:=zero_lt_one.trans hZ
  have hcap:=column_modulus_cap reflected s modifier R seed K Z ξ hK bin j
  dsimp only at hcap
  rw [hη] at hcap
  have hfirst:= (actual_geometry_norm_caps s modifier R seed K Z ξ Bfirst hs hz₁ hz₂ hsource j.1.val 0).2
  have hn:(((geometryFirstSource s modifier R seed K Z ξ hK bin j.1).C.absNorm:ℝ))≤Z^Bfirst:=hfirst
  calc
    _≤fixedPresentationCost*(ηanchor.modulus.absNorm:ℝ)*
        (((geometryFirstSource s modifier R seed K Z ξ hK bin j.1).C.absNorm:ℝ))^2:=hcap
    _≤Z^ηloss*(Z^Bfirst)^2:=mul_le_mul hconstant
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2) (sq_nonneg _) (Real.rpow_nonneg hZ0.le _)
    _=Z^(2*Bfirst+ηloss):=by
      rw [←Real.rpow_mul_natCast hZ0.le,←Real.rpow_add hZ0]
      congr 1
      norm_num
      ring

end
end QRH.Record1252270103Source.RegularSelectedStateCaps
#print axioms QRH.Record1252270103Source.RegularSelectedStateCaps.eventually_actual_first_character_cap
