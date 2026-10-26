/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal outputs of the two source branches share one selected original
family, one buffered partition and one common profile/height budget. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularBudget
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBufferedCofactor
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularLowSourceData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildInput CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFiniteProfileExceptional Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open Admission.SelectedRegularSourceData Admission.SelectedHighCofactorFamily
open Cycle61InitialMass LocalMoment
local notation "O"=>HeckeFamily.O
local instance regularCofactorDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

section Values
variable {α Label Row:Type}[Fintype α][Fintype Label]
  {Z:ℝ}{a:Anchor α Z}{F:Family a Label}{rows:Finset Row}{second:Bool}
  (G:Selected F Row rows second)

def regularSelectedSlots (T:Finset α)(t:ℝ)(r:rows):ℂ:=
  ∏j:T,normalizedSlot (G.τ r) (fixedBadMask*idealGenerator (Selection.puncture (G.sel r)))
    1 (G.z r) (F.s.slots j) (restoredSlotCoeff F.s j) t (F.s.P j)

def regularSelectedCentered (S A:Finset (Ideal O))(T:Finset α)(t:ℝ)(r:rows):ℂ:=
  newtonCofactorPlain (G.sel r).finalInput (Selection.frozenLeft (G.sel r))
    (Selection.frozenRight (G.sel r)) (Selection.puncture (G.sel r)) (9/4:ℝ)
    S A (G.τ r) t (G.z r)*regularSelectedSlots G T t r

def regularSelectedCorner (S A:Finset (Ideal O))(T:Finset α)(t:ℝ)(side:Bool)(r:rows):ℂ:=
  positiveNewtonCofactorPlain side (G.sel r).finalInput (Selection.frozenLeft (G.sel r))
    (Selection.frozenRight (G.sel r)) (Selection.puncture (G.sel r)) (9/4:ℝ)
    S A (G.τ r) t (G.z r)*regularSelectedSlots G T t r

theorem regular_selected_weight_nonneg (omega:rows→ℝ)(homega:∀r,0≤omega r)(r:rows):
    0≤selectedPaidWeight (G.sel r) (omega r):=by
  unfold selectedPaidWeight
  dsimp only
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (div_nonneg (volume_pos _).le (volume_pos _).le)) (forcedProfileCost_nonneg _)) (homega r)

/-- The additional univ subtype is exactly the carrier of the genuine LOW
terminal. Removing it neither duplicates a row nor changes its weight. -/
theorem regular_selected_source_fusion
    (S A:Finset (Ideal O))(T:Finset α)(t e q:ℝ)(select:rows→BufferIndex e)
    (omega:rows→ℝ)(homega:∀r,0≤omega r)
    (hb₁:F.s.b₁≤9/4)(hb₂:F.s.b₂≤9/4)(hd:GoodPair (newtonDivisorPair S A))
    (EL EH:ℝ)
    (hL:∀side:Bool,
      (∑r∈Finset.univ.filter (fun r:(Finset.univ:Finset rows)=>bufferValue e (select r.val)<(q+1)/2),
        ‖regularSelectedCorner G S A T t side r.val‖^2*selectedPaidWeight (G.sel r.val) (omega r.val))≤EL)
    (hH:(∑r∈Finset.univ.filter (fun r:rows=>(q+1)/2≤bufferValue e (select r)),
      ‖regularSelectedCentered G S A T t r‖^2*selectedPaidWeight (G.sel r) (omega r))≤EH):
    (∑r:rows,‖regularSelectedCentered G S A T t r‖^2*selectedPaidWeight (G.sel r) (omega r))≤4*EL+EH:=by
  have hl (side:Bool):
      (∑r∈Finset.univ.filter (fun r:rows=>bufferValue e (select r)<(q+1)/2),
        ‖regularSelectedCorner G S A T t side r‖^2*selectedPaidWeight (G.sel r) (omega r))≤EL:=by
    have he:=Admission.SelectedRegularLowSource.sum_univ_subtype_filter
      (ι:=rows) (fun r=>bufferValue e (select r)<(q+1)/2)
      (fun r=>‖regularSelectedCorner G S A T t side r‖^2*selectedPaidWeight (G.sel r) (omega r))
    exact he ▸ hL side
  have h:=centered_buffered_joint_family (Finset.univ:Finset rows)
    (fun r=>liveIndices (G.sel r).Bf.val) (fun r=>(G.sel r).finalInput)
    (fun r=>Selection.frozenLeft (G.sel r)) (fun r=>Selection.frozenRight (G.sel r))
    (fun r=>Selection.puncture (G.sel r)) (fun _=>9/4) S A G.τ (fun _=>t) G.z
    (regularSelectedSlots G T t) (fun r=>selectedPaidWeight (G.sel r) (omega r))
    (fun r _=>regular_selected_weight_nonneg G omega homega r) (by intros;norm_num)
    (fun r _=>(regular_selected_plain_upper (G.sel r)).1.trans_le hb₁)
    (fun r _=>(regular_selected_plain_upper (G.sel r)).2.trans_le hb₂) hd e q select
    EL EL EH (hl false) (hl true) hH
  convert h using 1 <;> first | rfl | ring

end Values

/-- The constant is chosen before the moving family. The two energy inputs
are exactly the literal conclusions of the genuine source applications. -/
theorem regular_selected_cofactor_budget
    (N I JL JH:ℕ)(δ B τ upper e q saving:ℝ)
    (CL Cpref Cslot CH pcCap box:ℝ)(SL SH:Finset (ℕ×ℕ))
    (hCL:0≤CL)(hCpref:0≤Cpref)(hCslot:0≤Cslot)(hCH:0≤CH)
    (hpcCap:0≤pcCap)(hbox:0≤box)(hu:1≤upper)(hq:1/2≤q)(hτ:0≤τ):
    ∃C:ℝ,0<C ∧ ∀{α Label Row:Type}[Fintype α][Fintype Label]
      {Z:ℝ}{a:Anchor α Z}(F:Family a Label)(rows:Finset Row)(second:Bool)
      (G:Selected F Row rows second)(S A:Finset (Ideal O))(T:Finset α)
      (p:Profiles (1/4:ℝ) (9/4:ℝ))(t height geometry omega err errv fee reserve other pref lowExponent:ℝ)
      (select:rows→BufferIndex e)(weight:rows→ℝ),
      (∀r,0≤weight r)→F.s.b₁≤9/4→F.s.b₂≤9/4→GoodPair (newtonDivisorPair S A)→
      1<Z→1≤height→forcedProfileCost F.s≤pcCap→0≤geometry→0≤omega→0≤err→
      lowExponent≤-saving→
      pref+2*δ+τ*(JH:ℝ)+omega+err+errv+other+saving≤fee+reserve→
      (∀side:Bool,
        (∑r∈Finset.univ.filter (fun r:(Finset.univ:Finset rows)=>bufferValue e (select r.val)<(q+1)/2),
          ‖regularSelectedCorner G S A T t side r.val‖^2*selectedPaidWeight (G.sel r.val) (weight r.val))≤
        regularLowBudget N JL CL Cpref Cslot (forcedProfileCost F.s) geometry ((p.control SL)^2) height Z lowExponent)→
      (∑r∈Finset.univ.filter (fun r:rows=>(q+1)/2≤bufferValue e (select r)),
        ‖regularSelectedCentered G S A T t r‖^2*selectedPaidWeight (G.sel r) (weight r))≤
        (∑k∈BufferedSelectedPaidSome.highBins e q,
          bufferedPaidBudget N I JH δ B τ upper Z e omega err errv fee reserve other pref
            CH (forcedProfileCost F.s) geometry ((p.control SH)^2) box k)→
      (∑r:rows,‖regularSelectedCentered G S A T t r‖^2*selectedPaidWeight (G.sel r) (weight r))≤
        C*geometry*(p.control (regularProfileControl SL SH))^2*height^JL*Z^(-saving):=by
  obtain ⟨C,hC,hpay⟩:=regular_budget_common_control N I JL JH δ B τ upper e q saving
    CL Cpref Cslot CH pcCap box SL SH hCL hCpref hCslot hCH hpcCap hbox hu hq hτ
  refine ⟨C,hC,?_⟩
  intro α Label Row _ _ Z a F rows second G S A T p t height geometry omega err errv fee reserve other pref lowExponent
    select weight hw hb₁ hb₂ hd hZ hheight hpc hgeometry homega herr hlow hhigh hL hH
  exact (regular_selected_source_fusion G S A T t e q select weight hw hb₁ hb₂ hd _ _ hL hH).trans
    (hpay p Z height (forcedProfileCost F.s) geometry omega err errv fee reserve other pref lowExponent
      hZ hheight (forcedProfileCost_nonneg F.s) hpc hgeometry homega herr hlow hhigh)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_selected_weight_nonneg
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_selected_source_fusion
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_selected_cofactor_budget
