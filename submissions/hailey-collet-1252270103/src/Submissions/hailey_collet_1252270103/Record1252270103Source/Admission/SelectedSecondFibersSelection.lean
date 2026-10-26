/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual kept complete second rows inherit the same full-cost fiber payment. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedSecondFibersRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedSecondFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentHeckeColumnWindow
open SecondSectorDatum ModifiedFibers
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Full-cost representatives in particular bound every individual key fiber.
This finite consequence permits exact transport of the checked selection API. -/
theorem fiber_bound_of_full_cost {Original Key : Type*} [Fintype Original]
    (key : Original→Key) (transform : Key→Key) (W : ℝ) (hW : 0≤W)
    (hsel : FullCostSelection key transform W) :
    ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤W := by
  intro k
  let fiber:=Finset.univ.filter (fun r=>key r=k)
  obtain ⟨pick,hpick,hinj,ht,hs⟩:=hsel fiber (fun _=>1) (fun _=>zero_le_one)
  have himage : Finset.univ.image (fun r:fiber=>key r.val)⊆{k} := by
    intro j hj
    obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hj
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp r.property).2
  have hcard : ((Finset.univ.image (fun r:fiber=>key r.val)).card:ℝ)≤1 := by
    exact_mod_cast (Finset.card_le_card himage).trans_eq (Finset.card_singleton k)
  have hh : (fiber.card:ℝ)≤W*((Finset.univ.image (fun r:fiber=>key r.val)).card:ℝ) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one] using hs
  exact hh.trans ((mul_le_mul_of_nonneg_left hcard hW).trans_eq (mul_one W))

/-- Any injective reindex or finite restriction retains the same fiber cost.
The full cost itself is untouched and can contain all remaining sums/weights. -/
theorem full_cost_selection_injective_reindex {Row Original Key : Type*}
    [Fintype Row] [Fintype Original] (embed : Row→Original) (hinj : Function.Injective embed)
    (key : Original→Key) (transform : Key→Key) (ht : Function.Injective transform)
    (W : ℝ) (hW : 0≤W) (hsel : FullCostSelection key transform W) :
    FullCostSelection (fun r=>key (embed r)) transform W := by
  apply full_cost_selection_of_fibers _ _ ht W hW
  exact high_restricted_key_fiber embed hinj key W (fiber_bound_of_full_cost key transform W hW hsel)

/-- Keep and complete-block filters are structural restrictions of the original
modified row carrier. No restricted-block nonzero gate or new multiplicity is paid. -/
theorem selected_second_restricted_full_cost_selection (A D₀ B L Cr B_row ε : ℝ)
    (hA : 0≤A) (hD₀ : 0≤D₀) (hB : 0≤B) (hL : 0≤L) (hCr : 0<Cr) (hBrow : 0≤B_row) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,1≤Z ∧
    ∀{α Label : Type*} [Fintype α] [Fintype Label]
      (slots : Label→Finset α) (s : ∀l,Input (slots l)) (modifier : ∀l,Tuple (slots l)→ℂ)
      (R seed : Label→Ideal O) (K Tsec : Label→ℝ) (ξ : ℝ)
      (hseed : ∀l,Squarefree (seed l)) (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
      (hK : ∀l,0<K l) (first : Label→FirstSourceLabel),
      Function.Injective (fun l=>(first l,seed l))→
      (∀l,Z^(-D₀)≤K l)→(∀l,K l≤Z^A)→
      (∀l,frequencyRadius (Tsec l) Z ξ≤Cr*Z^L)→(∀l,sourceRadius (s l)≤Z^B)→
      ∀(left : Bool) (u₀ : O) (unit : FirstSourceLabel→O),
      let blocks:=jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK
      let label:=fun q : JointIndex slots s modifier R seed K Tsec Z ξ=>first q.1
      ∀(hf : ∀r : secondLiveRows blocks,jointFirstFrequency left u₀ unit (secondEncodedRow blocks label r)≠0),
      (∀r : secondLiveRows blocks,
        ((Ideal.span {jointSourceRow left u₀ unit (secondEncodedRow blocks label r)}).absNorm:ℝ)≤Z^B_row)→
      ∀(W : 𝓢(ℝ,ℂ))
        (keep : ∀l,Record1252270103Second.BlockIndex (s l) (modifier l) (R l) (seed l)
          (K l) (Tsec l) Z ξ→O→Prop) (reflected : Bool),
      let kept:=keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep
      FullCostSelection (fun r : secondLiveRows kept=>secondEncodedNonzeroRow kept
        (fun q=>first q.1) r left u₀ unit
        (hf (originalRow slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep r)))
        (fun j=>if reflected then reflectedNonzeroJointLabel j else j) (C₀*Z^ε) := by
  obtain ⟨C₀,hC₀,hfull⟩:=modified_restricted_full_cost_selection A D₀ B L Cr B_row ε
    hA hD₀ hB hL hCr hBrow hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hfull] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label instα instLabel slots s modifier R seed K Tsec ξ hseed hz₁ hz₂ hK first hfirst
    hKlo hKhi hradius hsource left u₀ unit blocks label hf hnorm W keep reflected kept
  have hs:=hZ.2 slots s modifier R seed K Tsec ξ hseed hz₁ hz₂ hK first hfirst
    hKlo hKhi hradius hsource left u₀ unit hf hnorm reflected
  have hW : 0≤C₀*Z^ε := mul_nonneg hC₀.le (Real.rpow_nonneg (zero_le_one.trans hZ.1) _)
  exact full_cost_selection_injective_reindex
    (originalRow slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)
    (original_row_injective slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)
    (fun r : secondLiveRows blocks=>secondEncodedNonzeroRow blocks label r left u₀ unit (hf r))
    (fun j=>if reflected then reflectedNonzeroJointLabel j else j)
    (reflected_nonzero_key_injective reflected) _ hW hs

end
end QRH.Record1252270103Source.Admission.SelectedSecondFibers
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.fiber_bound_of_full_cost
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.full_cost_selection_injective_reindex
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.selected_second_restricted_full_cost_selection
