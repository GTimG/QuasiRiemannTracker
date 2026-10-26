/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal modified-row full-cost representatives for one injective joint family. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.ModifiedFibersDyads
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryHighWeightedSelection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.ModifiedFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Auxiliary choices may depend on the encoded row. Equality of the original
key still determines the entire selected source row, including its auxiliaries. -/
theorem selected_aux_encoded_injective {Label Aux:Type*} [Fintype Label]
    (s:Label→SecondBlockSource) (first:Label→FirstSourceLabel) (aux:Label→Aux)
    (hlabel:Function.Injective (fun l=>(first l,aux l,secondBlockCode (s l))))
    (chooseAux:JointSourceLabel→Aux×(Fin 4→ℤ)×RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter) :
    Function.Injective (fun r:{r:secondLiveRows s // rowAux s aux r=chooseAux (secondEncodedRow s first r)}=>
      secondEncodedRow s first r.val) := by
  intro r t h
  apply Subtype.ext
  apply actual_second_row_key_injective s first aux hlabel
  exact Prod.ext h (r.property.trans ((congrArg chooseAux h).trans t.property.symm))

/-- The complete cost is retained on an arbitrary finite restriction of the
original row carrier. The optional signed reflection changes only its key. -/
def FullCostSelection {Original Key:Type*} [Fintype Original] [DecidableEq Key]
    (key:Original→Key) (transform:Key→Key) (W:ℝ) : Prop :=
  ∀(rows:Finset Original) (cost:rows→ℝ), (∀r,0≤cost r)→
    ∃ pick : (j : Finset.univ.image (fun r:rows=>key r.val)) → rows,
      (∀j,key (pick j).val=j.val) ∧ Function.Injective (fun j=>key (pick j).val) ∧
      Function.Injective (fun j=>transform (key (pick j).val)) ∧
      (∑r:rows,cost r)≤W*(∑j:Finset.univ.image (fun r:rows=>key r.val),cost (pick j))

lemma full_cost_selection_of_fibers {Original Key:Type*} [Fintype Original] [DecidableEq Key]
    (key:Original→Key) (transform:Key→Key) (ht:Function.Injective transform)
    (W:ℝ) (hW:0≤W)
    (hcount:∀j,((Finset.univ.filter (fun r=>key r=j)).card:ℝ)≤W) :
    FullCostSelection key transform W := by
  intro rows cost hc
  obtain ⟨pick,hpick,hinj,hsum⟩:=high_restricted_full_cost_selection
    (fun r:rows=>r.val) Subtype.val_injective key cost W hW hc hcount
  exact ⟨pick,hpick,hinj,ht.comp hinj,hsum⟩

lemma reflected_nonzero_key_injective {left:Bool} {u₀:O} {unit:FirstSourceLabel→O}
    (reflected:Bool) : Function.Injective
      (fun j:NonzeroJointSourceLabel left u₀ unit=>if reflected then reflectedNonzeroJointLabel j else j) := by
  cases reflected
  · exact Function.injective_id
  · intro j k h
    apply Subtype.ext
    exact reflected_joint_involutive.injective (congrArg Subtype.val h)

lemma nonzero_key_fiber_bound {Label:Type*} [Fintype Label]
    (blocks:Label→SecondBlockSource) (first:Label→FirstSourceLabel)
    (left:Bool) (u₀:O) (unit:FirstSourceLabel→O)
    (hf:∀r:secondLiveRows blocks,jointFirstFrequency left u₀ unit (secondEncodedRow blocks first r)≠0)
    (W:ℝ) (hW:0≤W)
    (hcount:∀j:NonzeroJointSourceLabel left u₀ unit,
      (∃r:secondLiveRows blocks,secondEncodedRow blocks first r=j.val)→
      ((Finset.univ.filter (fun r:secondLiveRows blocks=>secondEncodedRow blocks first r=j.val)).card:ℝ)≤W) :
    ∀j,((Finset.univ.filter (fun r:secondLiveRows blocks=>
      secondEncodedNonzeroRow blocks first r left u₀ unit (hf r)=j)).card:ℝ)≤W := by
  intro j
  have he:(Finset.univ.filter (fun r:secondLiveRows blocks=>
      secondEncodedNonzeroRow blocks first r left u₀ unit (hf r)=j))=
      Finset.univ.filter (fun r:secondLiveRows blocks=>secondEncodedRow blocks first r=j.val) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact Subtype.ext_iff
  rw [he]
  by_cases hex:∃r:secondLiveRows blocks,secondEncodedRow blocks first r=j.val
  · exact hcount j hex
  · have hempty:(Finset.univ.filter (fun r:secondLiveRows blocks=>secondEncodedRow blocks first r=j.val))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hex ⟨r,(Finset.mem_filter.mp hr).2⟩
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    exact hW

/-- Uniform actual modified-row selection, with the complete physical cost,
original zero/keep restrictions and all weights retained. Its fiber bound is
proved from actual modified data. First choices must be fixed or selected so
that the displayed first-label/seed map is injective. -/
theorem modified_restricted_full_cost_selection (A D₀ B L Cr B_row ε:ℝ)
    (hA:0≤A) (hD₀:0≤D₀) (hB:0≤B) (hL:0≤L) (hCr:0<Cr) (hBrow:0≤B_row) (hε:0<ε) :
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,1≤Z ∧
    ∀{α Label:Type*} [Fintype α] [Fintype Label]
      (slots:Label→Finset α) (s:∀l,Input (slots l)) (modifier:∀l,Tuple (slots l)→ℂ)
      (R seed:Label→Ideal O) (K Tsec:Label→ℝ) (ξ:ℝ)
      (hseed:∀l,Squarefree (seed l)) (hz₁:∀l,(s l).W₁ 0=0) (hz₂:∀l,(s l).W₂ 0=0)
      (hK:∀l,0<K l) (first:Label→FirstSourceLabel),
      Function.Injective (fun l=>(first l,seed l))→
      (∀l,Z^(-D₀)≤K l)→(∀l,K l≤Z^A)→
      (∀l,frequencyRadius (Tsec l) Z ξ≤Cr*Z^L)→(∀l,sourceRadius (s l)≤Z^B)→
      ∀(left:Bool) (u₀:O) (unit:FirstSourceLabel→O),
      let blocks:=jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK
      let label:=fun q:JointIndex slots s modifier R seed K Tsec Z ξ=>first q.1
      ∀(hf:∀r:secondLiveRows blocks,jointFirstFrequency left u₀ unit (secondEncodedRow blocks label r)≠0),
      (∀r:secondLiveRows blocks,
        ((Ideal.span {jointSourceRow left u₀ unit (secondEncodedRow blocks label r)}).absNorm:ℝ)≤Z^B_row)→
      ∀reflected:Bool,
      FullCostSelection (fun r:secondLiveRows blocks=>secondEncodedNonzeroRow blocks label r left u₀ unit (hf r))
        (fun j=>if reflected then reflectedNonzeroJointLabel j else j) (C₀*Z^ε) := by
  obtain ⟨C₀,hC₀,hfibers⟩:=modified_fiber_subpower A D₀ B L Cr B_row ε hA hD₀ hB hL hCr hBrow hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hfibers] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label instα instLabel slots s modifier R seed K Tsec ξ hseed hz₁ hz₂ hK first hfirst
    hKlo hKhi hR hsource left u₀ unit blocks label hf hnorm reflected
  have hW:0≤C₀*Z^ε:=mul_nonneg hC₀.le (Real.rpow_nonneg (zero_le_one.trans hZ.1) _)
  apply full_cost_selection_of_fibers _ _ (reflected_nonzero_key_injective reflected) _ hW
  apply nonzero_key_fiber_bound blocks label left u₀ unit hf _ hW
  intro j hj
  obtain ⟨r,hr⟩:=hj
  have hjnorm:((Ideal.span {jointSourceRow left u₀ unit j.val}).absNorm:ℝ)≤Z^B_row := by
    rw [←hr]
    exact hnorm r
  have hfirst':Function.Injective (fun l=>(first l,(():Unit),seed l)) := by
    intro l m h
    have hf':first l=first m:=congrArg Prod.fst h
    have hs':seed l=seed m:=congrArg (fun x=>x.2.2) h
    exact hfirst (Prod.ext hf' hs')
  have h:=hZ.2 slots s modifier R seed K Tsec ξ hseed hz₁ hz₂ hK first (fun _=>(() : Unit))
    hfirst' hKlo hKhi hR hsource left u₀ unit j {()} hjnorm (fun _ _=>Finset.mem_singleton_self _)
  simpa only [Finset.card_singleton,Nat.cast_one,mul_one] using h

end
end QRH.Record1252270103Source.Admission.ModifiedFibers
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.selected_aux_encoded_injective
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_restricted_full_cost_selection
