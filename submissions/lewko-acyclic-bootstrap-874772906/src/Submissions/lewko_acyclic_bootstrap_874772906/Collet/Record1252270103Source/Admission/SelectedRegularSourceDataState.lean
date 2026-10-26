/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual kept selected rows, with one fixed anchor and the literal Newton puncture,
supply the natural state, buffered zero bin and original signed-key gates. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularSourceDataKeys
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularSelectedStateCapsPuncture
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularSelectedStateCapsCharacter
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularSelectedStateCapsWidth
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularSourceData
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open ConcretePrimeRowBridge
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource Cycle61Moment.LowBranch
open Cycle61Moment Cycle61InitialMass LocalMoment Record12518109Raw
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open SelectedSecondNatural SelectedSecondKeyCaps SelectedHighCofactorFamily
open RegularSelectedStateCaps
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- The fixed anchor and original puncture precede Z and every moving label,
allocation, Newton assignment and finite row restriction. The remaining inputs
are source/radius/pool caps and explicit scalar budgets, never state/key bounds. -/
theorem eventual_selected_retained_data (R₀:Ideal O)(hR₀:R₀≠0)(ηanchor:Character)
    (b err ηR ηchar ηwidth:ℝ)(N:ℕ)(hb:0<b)(herr:0<err)
    (hηR:0<ηR)(hηchar:0<ηchar)(hηwidth:0<ηwidth):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α Label Row:Type}[Fintype α][Fintype Label]
      (a:Anchor α Z)(F:Family a Label)(rows:Finset Row)(second:Bool)(G:Selected F Row rows second)
      (errv annular Afirst Asecond Brow Bradius Binactive Bmask bΦ Mcap ampN:ℝ)
      (w:α→ℝ)(wmin:ℝ)(Tslots:Finset α)(P S A:Finset (Ideal O))(depth:ℕ),
      F.R=R₀→F.s.η=ηanchor→F.ξ≤err→sourceRadius F.s≤Z^Afirst→
      (∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^Asecond)→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve b N (F.first (G.row u).val.1))→
      (∀u,G.x err errv annular w wmin Tslots u 2≤Brow)→
      (∀u,(G.datum u).radius≤Z^Bradius)→
      (∀u,((∏p∈(G.datum u).inactive,p.val).absNorm:ℝ)≤Z^Binactive)→
      ηR+Afirst+Asecond+8+(depth:ℝ)*ampN≤Bmask→
      Bradius+(2*Afirst+ηchar)+Binactive+ηwidth≤Mcap→
      2≤bΦ→(G.L.absNorm:ℝ)≤Z^(4:ℝ)→S⊆P→A⊆S→S.card≤depth→0≤ampN→
      (∀p∈P,p≠0)→(∀p∈P,(p.absNorm:ℝ)≤Z^ampN)→
      F.m≠0→F.Q≤Ideal.span {(72:O)}→goodLambda∣F.m→(2:O)∣F.m→
      ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
        (η₀:Character)(hQM:F.Q≤M)(hQη:F.Q≤η₀.modulus)(e T q:ℝ),
      0<e→2<T→1/2≤q→51/100≤HeckeZeroSupremum.beta→HeckeZeroSupremum.beta≤7/8→
      ∃st:rows→NaturalState Z Bmask bΦ,
      ∃hfixed:∀u,(st u).fixedModulus=F.Q,
      ∃keep:∀u,(st u).radial.keep (G.z u),
      ∃select:rows→BufferIndex e,∀u,
        G.extra S A u≠0 ∧ (st u).character=G.τ u ∧
        (st u).puncture=High.GlobalPhysical.Selection.puncture (G.sel u)*
          ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2) ∧
        (st u).width≤Mcap ∧
        1≤((st u).radial.profile (‖eisEmbedding (G.z u)‖^2/(st u).radial.scale)).re ∧
        (st u).radial.profile (‖eisEmbedding (G.z u)‖^2/(st u).radial.scale)≠0 ∧
        RetainedZeroBin M H hH (st u) η₀ ((hfixed u).trans_le hQM) ((hfixed u).trans_le hQη)
          (G.z u) (keep u) e T (select u) ∧
        (bufferValue e (select u)<(q+1)/2→
          ActualLow M H hH (st u) η₀ ((hfixed u).trans_le hQM) ((hfixed u).trans_le hQη)
            ((q+1)/2) e (3*((select u).1.val+1:ℕ)*T) (G.z u)) ∧
        ((q+1)/2≤bufferValue e (select u)→
          3/4≤bufferValue e (select u) ∧ bufferValue e (select u)≤7/8 ∧
          q≤2*bufferValue e (select u)-1 ∧ 2*bufferValue e (select u)-1≤3/4 ∧
          2*bufferValue e (select u)-1≤2*HeckeZeroSupremum.beta-1) ∧
        KeyCaps (G.key u) Z (coarseExponent Afirst Asecond Brow) (G.x err errv annular w wmin Tslots u 1) ∧
        rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(G.x err errv annular w wmin Tslots u 2) := by
  filter_upwards [eventual_selected_keys b err N hb herr,
    eventually_selected_retained_puncture R₀ hR₀ ηR hηR,
    eventually_actual_first_character_cap ηanchor ηchar hηchar,
    eventually_actual_enlarged_width ηwidth hηwidth] with Z hk hp hc hw
  refine ⟨hk.1,?_⟩
  intro α Label Row _ _ a F rows second G errv annular Afirst Asecond Brow Bradius Binactive Bmask bΦ Mcap ampN
    w wmin Tslots P S A depth hR hη hξ hs₀ hs₁ hT hqcap hradius hinactive hmaskbudget hwidthbudget hbΦ
    hLcap hS hA hdepth hampN hpool0 hpool hm hQ hml hm2 M _ H hH η₀ hQM hQη e T q he hTlarge hq hβlo hβhi
  have hpuncture (u:rows):G.extra S A u≠0 ∧
      ((enlargedRetainedPuncture (G.datum u) second (G.extra S A u)).absNorm:ℝ)≤Z^Bmask:=by
    have hfirst:=FirstFamily.label_common_bounds F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
      F.seed_sf F.zero₁ F.zero₂ (G.column u)
    have hsecond:=regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ
      ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m (G.row u).val.1
    have hC₁:((F.stage (G.row u).val.1.1).common.absNorm:ℝ)≤Z^Afirst:=by
      change ((if F.reflected then (F.first (G.row u).val.1).1.2 else (F.first (G.row u).val.1).1.1).absNorm:ℝ)≤_
      split_ifs
      · exact hfirst.2.2.2.trans hs₀
      · exact hfirst.2.2.1.trans hs₀
    have hC₂:((if second then (G.datum u).D else (G.datum u).C).absNorm:ℝ)≤Z^Asecond:=by
      split_ifs
      · exact hsecond.2.trans (hs₁ u)
      · exact hsecond.1.trans (hs₁ u)
    have hR':(G.datum u).R=R₀*(F.stage (G.row u).val.1.1).common:=by
      change F.R*(F.stage (G.row u).val.1.1).common=_
      rw [hR]
    have hh:=hp.2 (G.datum u) second (F.stage (G.row u).val.1.1).common (G.sel u).Cf G.L
      Afirst Asecond ampN depth P S A hR'
      (allocation_ne F.s (F.stage (G.row u).val.1.1).common (F.stage (G.row u).val.1.1).B)
      G.L_ne (G.forced_upper u) hC₁ hC₂ hLcap hS hA hdepth hampN hpool0 hpool
    refine ⟨?_,?_⟩
    · simpa only [Selected.extra,mul_assoc] using hh.2.1
    · have hh':((enlargedRetainedPuncture (G.datum u) second (G.extra S A u)).absNorm:ℝ)≤
          Z^(ηR+Afirst+Asecond+8+(depth:ℝ)*ampN):=by
        simpa only [Selected.extra,mul_assoc] using hh.2.2.2
      exact hh'.trans (Real.rpow_le_rpow_of_exponent_le hk.1.le hmaskbudget)
  let hJ:=fun u=>(hpuncture u).1
  let hPN:=fun u=>(hpuncture u).2
  let hR':=fun u=>F.mask_ne (G.row u).val.1.1
  let base:=fun u=>enlargedRetainedState (G.datum u) second Z Bmask F.hZ (G.ψ u) F.Q
    (G.extra S A u) (hR' u) (hJ u) (hPN u)
  let st:=fun u=>widenHighState (base u) bΦ hbΦ
  have hfixed:∀u,(st u).fixedModulus=F.Q:=fun _=>rfl
  obtain ⟨keep,select,hkept⟩:=actual_kept_retained_family F.slots F.input F.childModifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m
    M H hH rows G.row second Bmask bΦ F.hZ hbΦ G.ψ (G.extra S A) hR' hJ hPN hm hQ hml hm2
    η₀ hQM hQη e T q he hTlarge hq hβlo hβhi
  refine ⟨st,hfixed,keep,select,?_⟩
  intro u
  have hchar:((G.datum u).input.η.modulus.absNorm:ℝ)≤Z^(2*Afirst+ηchar):=by
    rw [(G.structural u).1]
    exact hc.2 F.reflected F.s F.modifier hη F.R F.seed (Z^F.D) F.ξ Afirst F.hK F.bin (G.column u)
      F.seed_sf F.zero₁ F.zero₂ hs₀
  have hwidth: (st u).width≤Mcap:=
    (hw.2 F.hZ F.datum (G.row u) second Bmask Bradius (2*Afirst+ηchar) Binactive
      (G.ψ u) F.Q (G.extra S A u) (hR' u) (hJ u) (hPN u) (hradius u) hchar (hinactive u)).trans hwidthbudget
  have hkey:=hk.2 a F rows second G errv annular Afirst Asecond Brow w wmin Tslots hξ hs₀ hs₁ hT hqcap u
  refine ⟨hJ u,rfl,?_,hwidth,(hkept u).1,(hkept u).2.1,(hkept u).2.2.2.1,
    (hkept u).2.2.2.2.1,(hkept u).2.2.2.2.2,hkey.1,hkey.2⟩
  exact G.selected_puncture S A u

end
end QRH.Record1252270103Source.Admission.SelectedRegularSourceData
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.eventual_selected_retained_data
