/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified complete-family ratio count, using the checked Cycle61
SecondRatioCap envelope without a source-label cardinality factor. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Contraction.SelectedFullNormalizedContraction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondSectorDatumFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondRatioCap
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open Cycle61InitialMass Cycle61Moment Record1252270103Second
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Source.SecondSectorDatum
local notation "O" => HeckeFamily.O

/-- Actual SourceBlocks dyads supply the subpower ratio count on the whole
CompleteFamily, uniformly over both ambient types and either row sector. -/
theorem modified_second_family_ratio_bins_subpower (A D₀ B L Cr ε : ℝ)
    (hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)(hCr : 0<Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,
    ∀{α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
      (slots : Label→Finset α)(s : ∀l,Input (slots l))
      (modifier : ∀l,Tuple (slots l)→ℂ)(R seed : Label→Ideal O)
      (hseed : ∀l,Squarefree (seed l))(hz₁ : ∀l,(s l).W₁ 0=0)(hz₂ : ∀l,(s l).W₂ 0=0)
      (W : 𝓢(ℝ,ℂ))(H Tsec ξ : Label→ℝ)(hH : ∀l,0<H l),
      (∀l,Z^(-D₀)≤H l)→(∀l,H l≤Z^A)→
      (∀l,frequencyRadius (Tsec l) Z (ξ l)≤Cr*Z^L)→
      (∀l,sourceRadius (s l)≤Z^B)→
    ∀keep : ∀l,BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) Z (ξ l)→O→Prop,
      ((secondRatioBins
        (fun q : CompleteFamily slots s modifier R seed W H Tsec (fun _=>Z) ξ=>
          modifiedDatumBlock
            (familyDatum slots s modifier R seed hseed hz₁ hz₂ W H Tsec (fun _=>Z) ξ hH keep q)
            (modifier q.1))).card:ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=actual_second_ratio_bins_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hc
  intro α Label _ _ _ slots s modifier R seed hseed hz₁ hz₂ W H Tsec ξ hH hHlo hHhi hfreq hsource keep
  let datum:=familyDatum slots s modifier R seed hseed hz₁ hz₂ W H Tsec (fun _=>Z) ξ hH keep
  have hn (q : CompleteFamily slots s modifier R seed W H Tsec (fun _=>Z) ξ) :
      ((datum q).C.absNorm:ℝ)≤Z^B ∧ ((datum q).D.absNorm:ℝ)≤Z^B := by
    have hh:=modified_retained_seed_and_caps (slots q.1) (s q.1) (modifier q.1)
      (R q.1) (seed q.1) (hseed q.1) (hz₁ q.1) (hz₂ q.1)
      (H q.1) (Tsec q.1) Z (ξ q.1) (hH q.1) q.2.val
    exact ⟨hh.2.2.1.trans (hsource q.1),hh.2.2.2.trans (hsource q.1)⟩
  exact hc (fun q=>modifiedDatumBlock (datum q) (modifier q.1))
    (fun q=>(datum q).C) (fun q=>(datum q).D)
    (fun q=>(datum q).hC) (fun q=>(datum q).hD) (fun q=>(datum q).sameSupport)
    (fun q=>(datum q).inactive) (fun q=>H q.1)
    (fun q=>frequencyRadius (Tsec q.1) Z (ξ q.1)) (fun q=>sourceRadius (s q.1))
    (fun q=>hH q.1) (fun q=>hHlo q.1) (fun q=>hHhi q.1)
    (fun q=>hfreq q.1) (fun q=>hsource q.1) (fun q=>(hn q).1) (fun q=>(hn q).2)
    (fun q=>q.2.val.2.2) (fun _ _=>rfl)

end
end QRH.Record1252270103Source.Contraction
#print axioms QRH.Record1252270103Source.Contraction.modified_second_family_ratio_bins_subpower
