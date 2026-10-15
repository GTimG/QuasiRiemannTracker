/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainAbsoluteBox
import Candidate.Cycle63.Physical.InitialMass.GeometryMainNormalized
import Candidate.Cycle63.Physical.InitialMass.SecondRatioBox

set_option autoImplicit false
set_option maxHeartbeats 160000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile
open CenteredMomentExceptionalAmplitudePair RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O

/-- The ratio image is paid from the actual common four-dyad box. No source
label cardinality or normalized-energy estimate enters this bound. -/
theorem eventual_actual_geometry_main_ratio_payment {α : Type}[Fintype α][DecidableEq α]
    (B loss b bs ξ ε : ℝ) (hB : 0≤B) (hloss : 0<loss)
    (hb : 1≤b) (hbs : 1≤bs) (hξ : 0≤ξ) (hξloss : ξ≤loss) (hε : 0<ε) :
    ∃Cb : ℝ,0<Cb ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))
      (_hend : Endpoints b bs bs s)(_hseed : Squarefree seed)
      (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |M|≤B → |amp|≤B →
      |frequencyLoss Z 32 ξ+reserve|≤B → 0≤amp → 0≤reserve →
      let selected := geometryMainNonzeroBlocks reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ key hz₁ hz₂
      let datum := fun j : selected => geometryLowSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ key j.val.1 hz₁ hz₂ j.val.2
      (∀j,(datum j).block.dyad∈geometryMainAbsoluteBox Z (Fintype.card α) B loss b) ∧
      ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤Cb*Z^ε ∧
      (∀(E : ℝ),0≤E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤Cb*E*Z^ε) ∧
      ∀(χ : selected→RayCharacter)(Q : selected→Ideal O)(m : selected→O)
        (E : ℝ),0≤E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(ordinarySecondDatum (datum j) (χ j) (Q j) (m j)).block),
          E/(1+dyadicScale r)^A)≤Cb*E*Z^ε := by
  obtain ⟨Cb,hCb,hbox⟩ := eventual_actual_geometry_main_absolute_box
    (Fintype.card α) B loss b bs ξ ε hB hloss hb hbs hξ hξloss hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hbox] with Z hz
  refine ⟨hz.1,?_⟩
  intro reflected s R seed M amp reserve t hZ key hend hseed hz₁ hz₂
    hsource hA hM hamp hω hamp0 hreserve selected datum
  have mem (j : selected) : (datum j).block.dyad∈geometryMainAbsoluteBox Z (Fintype.card α) B loss b := by
    have hf := (Finset.mem_filter.mp j.property).2.1
    have hraw := hz.2.2 reflected s R seed M amp reserve t
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) le_rfl hend hseed hz₁ hz₂
      hsource hA hM hamp hω hamp0 hreserve key j.val.1.1.val j.val.1.1.property j.val.1.2 hf j.val.2
    exact hraw
  have hcard : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤Cb*Z^ε := by
    have hcount : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤
        (geometryMainAbsoluteBox Z (Fintype.card α) B loss b).card := by
      exact_mod_cast second_ratio_bins_card_le_box (fun j=>(datum j).block) _ mem
    exact hcount.trans hz.2.1
  have decay (E : ℝ) (hE : 0≤E) (A : ℕ) :
      (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤Cb*E*Z^ε := by
    have hpaid := second_ratio_decay_le_box (fun j=>(datum j).block) _ mem E hE A
    have hbound := mul_le_mul_of_nonneg_right hz.2.1 hE
    exact hpaid.trans (hbound.trans_eq (by ring))
  refine ⟨mem,hcard,decay,?_⟩
  intro χ Q m E hE A
  simpa only [ordinary_second_ratio_bins] using decay E hE A

end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_main_ratio_payment
