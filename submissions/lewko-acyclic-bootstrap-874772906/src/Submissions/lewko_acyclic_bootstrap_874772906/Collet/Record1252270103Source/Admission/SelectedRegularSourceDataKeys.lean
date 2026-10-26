/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The same concrete selected rows receive the actual signed-key and frequency caps. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularSourceData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularSourceData
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open Cycle61Moment Cycle61InitialMass LocalMoment
open SelectedSecondNatural SelectedSecondKeyCaps SelectedHighCofactorFamily SelectedHighCofactorCoordinates HighScalar
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Fixed exponents and a genuine MAIN radius identity give every actual key
cap. No polynomial key/frequency hypothesis is accepted. -/
theorem eventual_selected_keys (b err:ℝ)(N:ℕ)(hb:0<b)(herr:0<err):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α Label Row:Type}[Fintype α][Fintype Label]
      (a:Anchor α Z)(F:Family a Label)(rows:Finset Row)(second:Bool)(G:Selected F Row rows second)
      (errv annular Afirst Asecond Brow:ℝ)(w:α→ℝ)(wmin:ℝ)(T:Finset α),
      F.ξ≤err→sourceRadius F.s≤Z^Afirst→
      (∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^Asecond)→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve b N (F.first (G.row u).val.1))→
      (∀u,G.x err errv annular w wmin T u 2≤Brow)→∀u,
      KeyCaps (G.key u) Z (coarseExponent Afirst Asecond Brow) (G.x err errv annular w wmin T u 1) ∧
      rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(G.x err errv annular w wmin T u 2) := by
  filter_upwards [eventual_regular_key_caps b err N hb herr,
    FirstFamily.eventual_literal_high_frequency b err N hb herr] with Z hk hf
  refine ⟨hk.1,?_⟩
  intro α Label Row _ _ a F rows second G errv annular Afirst Asecond Brow w wmin T hξ hs₀ hs₁ hT hq u
  have hcaps:=hk.2 F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec F.ξ ballProfile
    F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m
    F.s F.modifier F.R F.seed F.D F.hK F.bin F.reflected second F.column F.seed_sf F.zero₁ F.zero₂
    (G.row u) (F.amp (G.row u).val.1.1) F.reserve errv ((G.sel u).forced Z) ((G.sel u).live w wmin)
    (∑i∈Record12518109Natural.MarkedPlain.largeSlots T w wmin,w i) annular Afirst Asecond Brow hξ hs₀ (hs₁ u) (hT u) (hq u)
  have hradius:(F.datum (G.row u).val.1).radius=frequencyRadius
    (firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ (3*F.amp (G.row u).val.1.1)
      F.reserve b N (F.first (G.row u).val.1)) Z F.ξ:=by
    change frequencyRadius (F.Tsec (G.row u).val.1.1) Z F.ξ=_
    rw [hT u]
  have hfreq:=hf.2 F.reflected second F.s F.modifier F.R F.seed F.D F.ξ F.hK F.bin (G.column u)
    F.datum F.first (G.row u) rfl (F.amp (G.row u).val.1.1) F.reserve errv hξ hradius
  refine ⟨hcaps,?_⟩
  simpa [Selected.key,FirstFamily.rawKey,Selected.x,Selection.coordinate,cofactorCoordinates,
    lostWidthCoordinates,Selected.datum,Family.first,Selected.column] using hfreq

end
end QRH.Record1252270103Source.Admission.SelectedRegularSourceData
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.eventual_selected_keys
