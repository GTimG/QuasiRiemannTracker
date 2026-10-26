/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected original slots, positive Newton corners, and LOW erasure. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedLowErasureTransport
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowActualCapacityAdmission
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowRadialFloor
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalPositiveCornerSplit
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.CoupledAdmission
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowErasure
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst Cycle61Moment Cycle61InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentEnergyBands
open QRH.Record12518109Source QRH.Record1252270103Low QRH.Record1252270103Restoration
open SelectedHighCofactorFamily SelectedHighSlots High.GlobalPhysical
open ConcretePrimeRowBridge CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentSourceRectangleMask CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion Record1252270103Second Record1252270103Source
open QRH.Record1252270103KernelMass
open CenteredMomentCommonRadialData
local notation "O"=>HeckeFamily.O
local instance selectedLowDecidable {κ : Type*} : DecidableEq κ:=Classical.decEq _
variable {α : Type} [Fintype α] {s : Input α} {reflected second : Bool}
  {l : FirstSourceLabel} {C₂ D₂ R : Ideal O}

def finalPuncture (sel : Selection s reflected second l C₂ D₂ R) : Ideal O :=
  ((R*(if reflected then l.1.2 else l.1.1))*(if second then D₂ else C₂))*sel.Cf

def originalCoefficient (s : Input α) (j : α) (I : Ideal O) : ℂ :=
  s.ν j I*s.W j ((I.absNorm:ℝ)/s.P j)

def positiveCorner (sel : Selection s reflected second l C₂ D₂ R) (T : Finset α)
    (corner : Bool) (A₁ A₂ : Ideal O) (b : ℝ) (S A : Finset (Ideal O))
    (η : Character) (height : ℝ) (z : O) : ℂ :=
  positiveNewtonCofactorPlain corner sel.finalInput A₁ A₂ (finalPuncture sel) b S A η height z*
    ∏j : T,normalizedSlot η (fixedBadMask*idealGenerator (finalPuncture sel)) 1 z
      (s.pools (Sum.inl j)) (originalCoefficient s j) height (s.P j)

lemma positiveCorner_squarefree_nonzero
    (sel : Selection s reflected second l C₂ D₂ R) (T : Finset α)
    (corner : Bool) (A₁ A₂ : Ideal O) (b : ℝ) (S A : Finset (Ideal O))
    (η : Character) (height : ℝ) (z : O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣finalPuncture sel)
    (hd : GoodPair (newtonDivisorPair S A)) (hP : ∀j∈T,0<s.P j)
    (havoid : ∀j∈T,∀I∈s.pools (Sum.inl j),IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))
    (hn : positiveCorner sel T corner A₁ A₂ b S A η height z≠0) :
    squarefreePositiveSlotRow η
      (fixedBadMask*idealGenerator (finalPuncture sel*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)))
      1 z sel.finalInput.W₁ sel.finalInput.W₂ b
      (fun j : T=>s.pools (Sum.inl j)) (fun j : T=>originalCoefficient s j) (fun j : T=>s.P j)
      height ((if corner then sel.finalInput.Y₁ else sel.finalInput.X₁)/(newtonDivisorPair S A).1.absNorm)
      ((if corner then sel.finalInput.Y₂ else sel.finalInput.X₂)/(newtonDivisorPair S A).2.absNorm)≠0 := by
  have h₁ : 0<((newtonDivisorPair S A).1.absNorm:ℝ):=zero_lt_one.trans_le (norm_ge_one _ hd.1)
  have h₂ : 0<((newtonDivisorPair S A).2.absNorm:ℝ):=zero_lt_one.trans_le (norm_ge_one _ hd.2.1)
  have hx₁ : 0<(if corner then sel.finalInput.Y₁ else sel.finalInput.X₁):=by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sel.finalInput.X₁_pos
    · exact sel.finalInput.Y₁_pos
  have hx₂ : 0<(if corner then sel.finalInput.Y₂ else sel.finalInput.X₂):=by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sel.finalInput.X₂_pos
    · exact sel.finalInput.Y₂_pos
  unfold positiveCorner at hn
  rw [positive_newton_corner_normalization] at hn
  have he:=RetainedLow.positiveFrozenRow_normalized_slots η (finalPuncture sel) A₁ A₂
    hA₁ hA₂ hAR (newtonDivisorPair S A) hd sel.finalInput.W₁ sel.finalInput.W₂ b
    (fun j : T=>s.pools (Sum.inl j)) (fun j : T=>originalCoefficient s j) (fun j : T=>s.P j)
    (fun j=>hP j j.property) (fun j I hI=>havoid j j.property I hI)
    height _ _ (div_pos hx₁ h₁) (div_pos hx₂ h₂) z
  rw [he] at hn
  exact (mul_ne_zero_iff.mp hn).2

theorem positiveCorner_radial_floor
    (sel : Selection s reflected second l C₂ D₂ R) (T : Finset α)
    (S A : Finset (Ideal O)) (hdpair : GoodPair (newtonDivisorPair S A))
    (w : α→ℝ) (N : ℕ) (upper Z t b F delta rho B plainUpper plainRound e : ℝ)
    (hupper : 1≤upper) (hZ : 1<Z) (hN : Fintype.card α≤N) (hu : s.upper≤upper)
    (hscale : ∀i,s.P i=Z^w i) (ht : length Z s.X₁+length Z s.X₂≤t)
    (hw : ∀i,0≤w i) (htotal : (∑i,w i)≤b) (hround : 0≤plainRound) (he : 0<e)
    (hB0 : 0≤B) (hB1 : B≤1) (hd : 0≤delta)
    (hdc : delta≤Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (hguard : (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound)+
      B*rho+2*e≤B*F-t-b)
    (corner : Bool) (A₁ A₂ : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (hAR : A₁*A₂∣finalPuncture sel) (havoid : ∀j∈T,∀I∈s.pools (Sum.inl j),
      IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))
    (η : Character) (height : ℝ) (z : O)
    (hn : positiveCorner sel T corner A₁ A₂ plainUpper S A η height z≠0) :
    2*e≤F-delta-rho := by
  have hP (j : α) (_ : j∈T) : 0<s.P j := by
    rw [hscale];exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hd₁ : 1≤((newtonDivisorPair S A).1.absNorm:ℝ):=norm_ge_one _ hdpair.1
  have hd₂ : 1≤((newtonDivisorPair S A).2.absNorm:ℝ):=norm_ge_one _ hdpair.2.1
  have hcorner₁ (corner : Bool) : 0<(if corner then sel.finalInput.Y₁ else sel.finalInput.X₁) := by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sel.finalInput.X₁_pos
    · exact sel.finalInput.Y₁_pos
  have hcorner₂ (corner : Bool) : 0<(if corner then sel.finalInput.Y₂ else sel.finalInput.X₂) := by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sel.finalInput.X₂_pos
    · exact sel.finalInput.Y₂_pos
  have hprod (corner : Bool) :
      (if corner then sel.finalInput.Y₁ else sel.finalInput.X₁)*
        (if corner then sel.finalInput.Y₂ else sel.finalInput.X₂)=sel.finalInput.X₁*sel.finalInput.X₂ := by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    exact sel.finalInput.same_product
  have hsf:=positiveCorner_squarefree_nonzero sel T corner A₁ A₂ plainUpper S A η height z
    hA₁ hA₂ hAR hdpair hP havoid hn
  exact (RegularLowRadialFloor.three_positive_corner_floor_or_zero (ι:=α) (κ:=T)
    s (if reflected then l.1.2 else l.1.1) R sel.B₁ sel.τ₁ sel.t₁
    (if second then D₂ else C₂) sel.B₂ sel.τ₂ sel.t₂ sel.Cf sel.Bf sel.τf sel.tf w N upper Z t b F delta rho B
    plainUpper plainRound e hupper hZ hN hu hscale ht hw htotal hround he hB0 hB1 hd hdc hguard
    sel.hf₁ sel.hf₂ sel.hff _ _ _ _ (hcorner₁ corner) (hcorner₂ corner) hd₁ hd₂ (hprod corner)
    η (fixedBadMask*idealGenerator (finalPuncture sel*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)))
    1 z sel.finalInput.W₁ sel.finalInput.W₂ (fun j : T=>s.pools (Sum.inl j))
    (fun j : T=>originalCoefficient s j) (fun j : T=>s.P j) height).resolve_left hsf

theorem selected_low_corner_erasure
    (sel : Selection s reflected second l C₂ D₂ R) (T : Finset α) (hT : T⊆sel.full)
    (S A : Finset (Ideal O)) (hdpair : GoodPair (newtonDivisorPair S A))
    (w : α→ℝ) (N : ℕ) (upper Z t b F delta rho B lam h plainUpper mesh plainRound e : ℝ)
    (hupper : 1≤upper) (hZ : 1<Z) (hN : Fintype.card α≤N) (hu : s.upper≤upper)
    (hscale : ∀i,s.P i=Z^w i) (ht : length Z s.X₁+length Z s.X₂≤t)
    (hw : ∀i,0≤w i) (htotal : (∑i,w i)≤b) (hmesh : 0≤mesh) (hwm : ∀i∈T,w i≤mesh)
    (hround : 0≤plainRound) (he : 0<e) (hB0 : 0≤B) (hB1 : B≤1) (hlam : 0<lam)
    (hd : 0≤delta) (hdc : delta≤Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (hh : 0≤h)
    (hguard : (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound)+
      B*rho+2*e≤B*F-t-b) :
    let emb:=finalEmbedding sel.B₁.val sel.B₂.val sel.Bf.val
    let pull:=originalPullback emb T
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)+Real.logb Z (sel.Cf.absNorm:ℝ)
    let f:=(∑i,w i)-∑i : liveIndices sel.Bf.val,w i.val.val.val
    let loss:=3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound
    let Pcap:=t-c+f+loss-Real.logb Z ((newtonDivisorPair S A).1.absNorm:ℝ)-
      Real.logb Z ((newtonDivisorPair S A).2.absNorm:ℝ)
    let Q:=F-delta-rho
    ∃E : Finset (liveIndices sel.Bf.val),E⊆pull ∧
      let select:=(pull\E).map emb
      select⊆T ∧ T\select=E.map emb ∧
      (∑j∈T,w j)=(∑i∈pull,w (emb i)) ∧
      (∑j∈select,w j)=(∑i∈pull\E,w (emb i)) ∧
      (∑j∈T\select,w j)=(∑i∈E,w (emb i)) ∧
      (∑j∈T\select,w j)≤max 0 (max (b-f-(B*Q-Pcap)/lam) (b-f-h*Q))+mesh ∧
      ∀(corner : Bool)(A₁ A₂ : Ideal O),A₁≠0 → A₂≠0 → A₁*A₂∣finalPuncture sel →
      (∀j∈T,∀I∈s.pools (Sum.inl j),IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)) →
      ∀(η : Character)(height : ℝ)(z : O),
      positiveCorner sel T corner A₁ A₂ plainUpper S A η height z=0 ∨
        (2*e≤Q ∧ RoundedPairAdmission (globalFace B lam h) Z
          ((if corner then sel.finalInput.Y₁ else sel.finalInput.X₁)/(newtonDivisorPair S A).1.absNorm)
          ((if corner then sel.finalInput.Y₂ else sel.finalInput.X₂)/(newtonDivisorPair S A).2.absNorm)
          plainRound (∑j∈select,w j) Q) := by
  rcases sel with ⟨B₁,τ₁,t₁,hf₁,B₂,τ₂,t₂,hf₂,Cf,Bf,τf,tf,hff⟩
  let sel : Selection s reflected second l C₂ D₂ R:=⟨B₁,τ₁,t₁,hf₁,B₂,τ₂,t₂,hf₂,Cf,Bf,τf,tf,hff⟩
  intro emb pull c f loss Pcap Q
  have hmap : T⊆Finset.univ.map emb := by
    simpa only [Selection.full,finalImage_eq_map] using hT
  have hmapPull : pull.map emb=T:=originalPullback_map emb T hmap
  have hP (j : α) (_ : j∈T) : 0<s.P j := by
    rw [hscale];exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hd₁ : 1≤((newtonDivisorPair S A).1.absNorm:ℝ):=norm_ge_one _ hdpair.1
  have hd₂ : 1≤((newtonDivisorPair S A).2.absNorm:ℝ):=norm_ge_one _ hdpair.2.1
  have hcorner₁ (corner : Bool) : 0<(if corner then sel.finalInput.Y₁ else sel.finalInput.X₁) := by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sel.finalInput.X₁_pos
    · exact sel.finalInput.Y₁_pos
  have hcorner₂ (corner : Bool) : 0<(if corner then sel.finalInput.Y₂ else sel.finalInput.X₂) := by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sel.finalInput.X₂_pos
    · exact sel.finalInput.Y₂_pos
  have hprod (corner : Bool) :
      (if corner then sel.finalInput.Y₁ else sel.finalInput.X₁)*
        (if corner then sel.finalInput.Y₂ else sel.finalInput.X₂)=sel.finalInput.X₁*sel.finalInput.X₂ := by
    cases corner <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    exact sel.finalInput.same_product
  have hfloor (corner : Bool) (A₁ A₂ : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
      (hAR : A₁*A₂∣finalPuncture sel) (havoid : ∀j∈T,∀I∈s.pools (Sum.inl j),
        IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))
      (η : Character) (height : ℝ) (z : O)
      (hn : positiveCorner sel T corner A₁ A₂ plainUpper S A η height z≠0) : 2*e≤Q := by
    exact positiveCorner_radial_floor sel T S A hdpair w N upper Z t b F delta rho B
      plainUpper plainRound e hupper hZ hN hu hscale ht hw htotal hround he hB0 hB1 hd hdc hguard
      corner A₁ A₂ hA₁ hA₂ hAR havoid η height z hn
  have htransport:=original_erasure_transport emb pull T hmapPull
  by_cases hQ : 0≤Q
  · have hbase:=RegularLowActualCapacity.three_live_rounded_admission (ι:=α) (κ:=T)
      s (if reflected then l.1.2 else l.1.1) R sel.B₁ sel.τ₁ sel.t₁
      (if second then D₂ else C₂) sel.B₂ sel.τ₂ sel.t₂ sel.Cf sel.Bf sel.τf sel.tf
    have hgeo:=hbase w pull N upper Z t b F delta rho B lam h plainUpper mesh plainRound
      ((newtonDivisorPair S A).1.absNorm:ℝ) ((newtonDivisorPair S A).2.absNorm:ℝ)
    have hchoice:=hgeo hupper hZ hN hu hscale ht hw htotal hmesh
      (fun i hi=>hwm _ (originalPullback_member emb T i hi)) hround hB1 hlam hd hdc hh hQ hd₁ hd₂
      (by linarith only [hguard,he]) sel.hf₁ sel.hf₂ sel.hff
    obtain ⟨_,E,hE,hleft,hcost,hadmit⟩:=hchoice
    have htr:=htransport E hE w
    have hselect:=htr.1
    have himage:=htr.2.1
    have hfull:=htr.2.2.1
    have hret:=htr.2.2.2.1
    have herase:=htr.2.2.2.2
    refine ⟨E,hE,hselect,himage,hfull,hret,herase,?_,?_⟩
    · rw [herase];exact hcost
    · intro corner A₁ A₂ hA₁ hA₂ hAR havoid η height z
      by_cases hn : positiveCorner sel T corner A₁ A₂ plainUpper S A η height z=0
      · exact Or.inl hn
      · refine Or.inr ⟨hfloor corner A₁ A₂ hA₁ hA₂ hAR havoid η height z hn,?_⟩
        intro n₁ n₂ hn₁ hn₂ hc₁ hc₂
        have hsf:=positiveCorner_squarefree_nonzero sel T corner A₁ A₂ plainUpper S A η height z
          hA₁ hA₂ hAR hdpair hP havoid hn
        have ha:=hadmit _ _ (hcorner₁ corner) (hcorner₂ corner) (hprod corner)
          η (fixedBadMask*idealGenerator (finalPuncture sel*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)))
          1 z sel.finalInput.W₁ sel.finalInput.W₂ (fun j : T=>s.pools (Sum.inl j))
          (fun j : T=>originalCoefficient s j) (fun j : T=>s.P j) height n₁ n₂ hn₁ hn₂ hc₁ hc₂
        rw [hret]
        exact ha.resolve_left hsf
  · have htr:=htransport ∅ (Finset.empty_subset _) w
    have hselect:=htr.1
    have himage:=htr.2.1
    have hfull:=htr.2.2.1
    have hret:=htr.2.2.2.1
    have herase:=htr.2.2.2.2
    refine ⟨∅,Finset.empty_subset _,hselect,himage,hfull,hret,herase,?_,?_⟩
    · rw [herase,Finset.sum_empty]
      exact add_nonneg (le_max_left 0 _) hmesh
    · intro corner A₁ A₂ hA₁ hA₂ hAR havoid η height z
      apply Or.inl
      by_contra hn
      have hf:=hfloor corner A₁ A₂ hA₁ hA₂ hAR havoid η height z hn
      exact hQ (by linarith only [hf,he])
end
end QRH.Record1252270103Source.Admission.SelectedLowErasure
#print axioms QRH.Record1252270103Source.Admission.SelectedLowErasure.positiveCorner_squarefree_nonzero
#print axioms QRH.Record1252270103Source.Admission.SelectedLowErasure.selected_low_corner_erasure

#print axioms QRH.Record1252270103Source.Admission.SelectedLowErasure.positiveCorner_radial_floor
