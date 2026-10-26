/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One actual modified-row fiber pays only explicit auxiliaries and a subpower. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.ModifiedFibersBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.ModifiedFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open Cycle61Moment Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSectors
open CenteredMomentSectorLocalization CenteredMomentHeckeColumnWindow
open Record1252270103Second
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

lemma active_pair_supported (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (p:CenteredMomentSecondBlockAggregate.ActiveLabel S β) :
    Supported p.val.1 ∧ Supported p.val.2 :=
  CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (activeSource S β) p.val.1 p.val.2 p.property

/-- All four actual modified dyads belong to the common absolute box;
the ideal norm caps come from the modified common-column witnesses. -/
theorem modified_dyad_absolute {ι:Type*} [Fintype ι]
    (Z A D₀ B L Cr:ℝ) (hZ:1≤Z) (hA:0≤A) (hD₀:0≤D₀) (hB:0≤B) (hL:0≤L) (hCr:0<Cr)
    (s:Input ι) (modifier:Tuple ι→ℂ) (R seed:Ideal O) (hseed:Squarefree seed)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (K Tsec ξ:ℝ) (hK:0<K)
    (hKlo:Z^(-D₀)≤K) (hKhi:K≤Z^A)
    (hR:frequencyRadius Tsec Z ξ≤Cr*Z^L) (hsource:sourceRadius s≤Z^B)
    (q:BlockIndex s modifier R seed K Tsec Z ξ) :
    (fun i=>(q.2.2 i:ℤ))∈secondAbsoluteBox Z A D₀ B L Cr := by
  have hg:=High.CoupledFirst.actual_common_gates s modifier R seed hseed hz₁ hz₂ q.1.val.val.1 q.1.val.val.2 q.1.val.property
  have hs:=active_pair_supported _ _ q.1.val
  apply Fintype.mem_piFinset.mpr
  intro i
  exact actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
    _ _ hs.1 hs.2 hg.2.2.1 q.2.1 K (frequencyRadius Tsec Z ξ) (sourceRadius s)
    hK hKlo hKhi hR hsource (hg.2.2.2.2.2.1.trans hsource) (hg.2.2.2.2.2.2.trans hsource) q.2.2 i

/-- The actual heterogeneous modified family has a uniform fiber subpower.
The first-choice auxiliary cardinality remains explicit. The constant and
threshold precede every moving family, type, modifier and first allocation. -/
theorem modified_fiber_subpower (A D₀ B L Cr B_row ε:ℝ)
    (hA:0≤A) (hD₀:0≤D₀) (hB:0≤B) (hL:0≤L) (hCr:0<Cr) (hBrow:0≤B_row) (hε:0<ε) :
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,1≤Z ∧
    ∀{α Label Aux:Type*} [Fintype α] [Fintype Label]
      (slots:Label→Finset α) (s:∀l,Input (slots l)) (modifier:∀l,Tuple (slots l)→ℂ)
      (R seed:Label→Ideal O) (K Tsec:Label→ℝ) (ξ:ℝ)
      (hseed:∀l,Squarefree (seed l)) (hz₁:∀l,(s l).W₁ 0=0) (hz₂:∀l,(s l).W₂ 0=0)
      (hK:∀l,0<K l) (first:Label→FirstSourceLabel) (aux:Label→Aux),
      Function.Injective (fun l=>(first l,aux l,seed l))→
      (∀l,Z^(-D₀)≤K l)→(∀l,K l≤Z^A)→
      (∀l,frequencyRadius (Tsec l) Z ξ≤Cr*Z^L)→(∀l,sourceRadius (s l)≤Z^B)→
      ∀(left:Bool) (u₀:O) (unit:FirstSourceLabel→O) (j:NonzeroJointSourceLabel left u₀ unit)
        (choices:Finset Aux),
      ((Ideal.span {jointSourceRow left u₀ unit j.val}).absNorm:ℝ)≤Z^B_row→
      (∀r:secondLiveRows (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK),
        secondEncodedRow (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK)
          (fun q=>first q.1) r=j.val→aux r.val.1.1∈choices)→
      ((Finset.univ.filter (fun r:secondLiveRows
        (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK)=>
        secondEncodedRow (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK)
          (fun q=>first q.1) r=j.val)).card:ℝ)≤C₀*Z^ε*choices.card := by
  obtain ⟨C₁,hC₁,hprojector⟩:=projector_aux_fiber_bound B_row (ε/2) hBrow (half_pos hε)
  obtain ⟨C₂,hC₂,hdyads⟩:=second_absolute_envelope_subpower A D₀ B L Cr (ε/2)
    hA hD₀ hB hL hCr (half_pos hε)
  let rayCost:ℝ:=max 1 ((Fintype.card RayCharacter:ℝ)^2)
  have hray:0<rayCost := by
    dsimp [rayCost]
    exact zero_lt_one.trans_le (le_max_left (1:ℝ) _)
  refine ⟨C₁*C₂*rayCost,by positivity,?_⟩
  filter_upwards [hdyads,eventually_ge_atTop (1:ℝ)] with Z hdyads hZ
  refine ⟨hZ,?_⟩
  intro α Label Aux instα instLabel slots s modifier R seed K Tsec ξ hseed hz₁ hz₂ hK
    first aux hfirst hKlo hKhi hR hsource left u₀ unit j choices hnorm haux
  let blocks:=jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK
  let box:=secondAbsoluteBox Z A D₀ B L Cr
  have hbox (r:secondLiveRows blocks) (_hr:secondEncodedRow blocks (fun q=>first q.1) r=j.val) :
      (blocks r.val.1).dyad∈box :=
    modified_dyad_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr (s r.val.1.1)
      (modifier r.val.1.1) (R r.val.1.1) (seed r.val.1.1) (hseed r.val.1.1)
      (hz₁ r.val.1.1) (hz₂ r.val.1.1) (K r.val.1.1) (Tsec r.val.1.1) ξ (hK r.val.1.1)
      (hKlo r.val.1.1) (hKhi r.val.1.1) (hR r.val.1.1) (hsource r.val.1.1) r.val.1.2
  have hcount:=hprojector Z hZ blocks (fun q=>first q.1) (fun q=>seed q.1) (fun q=>aux q.1)
    (modified_joint_source_keys_aux slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK first aux hfirst)
    (fun q=>hseed q.1) (joint_seed_divides slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK)
    left u₀ unit j choices box hnorm haux hbox
  have hn:(box.card:ℝ)≤C₂*Z^(ε/2) := by
    rw [show box.card=Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) from
      second_absolute_box_card Z A D₀ B L Cr]
    exact hdyads
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have he:Z^(ε/2)*Z^(ε/2)=Z^ε := by
    rw [←Real.rpow_add hz]
    congr 1
    ring
  apply hcount.trans
  calc
    _≤(C₁*Z^(ε/2))*choices.card*(C₂*Z^(ε/2))*(Fintype.card RayCharacter:ℝ)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) (sq_nonneg _)
    _≤(C₁*Z^(ε/2))*choices.card*(C₂*Z^(ε/2))*rayCost :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    _=(C₁*C₂*rayCost)*(Z^(ε/2)*Z^(ε/2))*choices.card := by ring
    _=_ := by rw [he]

end
end QRH.Record1252270103Source.Admission.ModifiedFibers
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_dyad_absolute
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_fiber_subpower
