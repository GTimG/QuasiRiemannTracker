/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Shared actual selected HIGH geometry; no analytic estimate is assumed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularSourceDataState
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularGeometryCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularHighSource
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice
open Cycle61Moment Cycle61InitialMass LocalMoment Record12518109Raw
open SelectedRegularSourceData SelectedSecondKeyCaps
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def eventualPredicate {P:ℝ→Prop} (_h:∀ᶠZ:ℝ in atTop,P Z):ℝ→Prop:=P

theorem key_caps_mono {left:Bool}{u₀:O}{unit:FirstSourceLabel→O}
    (key:NonzeroJointSourceLabel left u₀ unit)(Z A B m:ℝ)(hZ:1<Z)(hAB:A≤B)
    (h:KeyCaps key Z A m):KeyCaps key Z B m := by
  have hz:=Real.rpow_le_rpow_of_exponent_le hZ.le hAB
  exact ⟨⟨h.1.1.trans hz,h.1.2.1.trans hz,h.1.2.2.1.trans hz,h.1.2.2.2.trans hz⟩,
    h.2.1.trans hz,h.2.2.1.trans hz,h.2.2.2.1,h.2.2.2.2⟩

theorem selected_common_caps {α Label Row:Type}[Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor α Z}(F:Family a Label)(rows:Finset Row)(second:Bool)(g:Selected F Row rows second)
    (Af Bfirst Bsecond:ℝ)(hAf:Af≤Bfirst)(hsecond:2≤Bsecond)
    (hs:sourceRadius F.s≤Z^Af)(hc:∀u,sourceRadius (F.input (g.row u).val.1.1)≤Z^(2:ℝ)):
    ∀u,((if F.reflected then (F.first (g.row u).val.1).1.2 else
        (F.first (g.row u).val.1).1.1).absNorm:ℝ)≤Z^Bfirst ∧
      ((if second then (g.datum u).D else (g.datum u).C).absNorm:ℝ)≤Z^Bsecond := by
  intro u
  have hf:=FirstFamily.label_common_bounds F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
    F.seed_sf F.zero₁ F.zero₂ (g.column u)
  have hh:=regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ
    ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m (g.row u).val.1
  constructor
  · have hbound:=hs.trans (Real.rpow_le_rpow_of_exponent_le F.hZ.le hAf)
    split_ifs
    · exact hf.2.2.2.trans hbound
    · exact hf.2.2.1.trans hbound
  · have hbound:=(hc u).trans (Real.rpow_le_rpow_of_exponent_le F.hZ.le hsecond)
    split_ifs
    · exact hh.2.trans hbound
    · exact hh.1.trans hbound
end
end QRH.Record1252270103Source.Admission.SelectedRegularHighSource
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighSource.key_caps_mono
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighSource.selected_common_caps
