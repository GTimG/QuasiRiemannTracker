/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The second allocation and complete forced-prime extraction preserve one
original row family before the joint Newton and collision estimate. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalFixedForcedFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalFixedResidualNewton
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentHeckeSlots CenteredMomentHeckeExpansion
open Record1252270103Source Record1252270103Second Collision Admission.JointForced
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O"=>ActualEisensteinCubic.O

/-- Both second-allocation cardinal factors, its frozen coefficient and
volume ratio enter the same cofactor-family weight. The residual ideal is fixed. -/
theorem uniform_fixed_plain_newton_supported (N:ℕ) (ε:ℝ) (hε:0<ε) :
    ∃K₀:ℝ,0<K₀ ∧ ∀{α Row:Type}[Fintype α]
      (rows:Finset Row)(ι:Row→Type)[∀r,Fintype (ι r)]
      (s:∀r,Input (ι r))(embedding:∀r,ι r↪α)
      (S₀:α→Finset (Ideal O))(β₀:α→Ideal O→ℂ)(P₀:α→ℝ),
    Fintype.card α≤N→
    (∀r i,(s r).slots i=S₀ (embedding r i))→
    (∀r i,restoredSlotCoeff (s r) i=β₀ (embedding r i))→
    (∀r i,(s r).P i=P₀ (embedding r i))→
    ∀(P:Finset (Ideal O))(A₁ A₂ D K C R seed:Row→Ideal O)(L:Ideal O),
    Squarefree L→(∀r,K r∣R r)→
    ∀(hC:∀r,Supported (C r))(hseed:∀r,seed r∣C r)
      (τ:Row→Character)(t:Row→ℝ)(z:Row→O)(weight:Row→ℝ),
    (∀r∈rows,0≤weight r)→
    let energy:=fun r=>fixedPlainEnergy (s r) (A₁ r) (A₂ r) (D r) (K r) (C r) (R r) (seed r) L
      (poolCorrection P) (hC r) (τ r) (t r) (z r)
    let live:=rows.filter (fun r=>energy r≠0)
    ∃alloc:∀r:live,actualAllocations (s r).pools (C r),
      (∀r,frozenCoefficient (alloc r).val (C r) (R r) (s r).ν (s r).W (s r).P≠0) ∧
      let s':=fun r:live=>child (s r) (C r) (R r) (alloc r) (τ r) (t r)
      let A₁':=fun r:live=>A₁ r*(alloc r).val (Sum.inr 0)
      let A₂':=fun r:live=>A₂ r*(alloc r).val (Sum.inr 1)
      let D':=fun r:live=>D r*C r
      let K':=fun r:live=>K r*markedProduct (alloc r).val
      let R':=fun r:live=>R r*C r
      let modifier':=fun r:live=>markedSourceModifier (A₁' r) (A₂' r) (D' r) (K' r) (poolCorrection P)
      ∃pick:∀r:live,ChildIndex (s' r) (modifier' r) (R' r) L,
      (∀r:live,frozenCoefficient (pick r).2 (pick r).1 (R' r) (s' r).ν (s' r).W (s' r).P≠0 ∧
        0<childValue (s' r) (modifier' r) (R' r) L (τ r) (t r) (z r) (pick r) ∧
        L∣((pick r).1:Ideal O) ∧ ((pick r).1:Ideal O)∣L^2) ∧
      let childInput:=fun r:live=>child (s' r) (pick r).1 (R' r) (pick r).2 (τ r) (t r)
      let childEmbedding:=fun r:live=>inheritedSlotEmbedding (pick r).2.val
        (inheritedSlotEmbedding (alloc r).val (embedding r))
      let childA₁:=fun r:live=>A₁' r*(pick r).2.val (Sum.inr 0)
      let childA₂:=fun r:live=>A₂' r*(pick r).2.val (Sum.inr 1)
      let childD:=fun r:live=>D' r*(pick r).1
      let childK:=fun r:live=>K' r*markedProduct (pick r).2.val
      let childR:=fun r:live=>R' r*(pick r).1
      let paidWeight:=fun r:live=>((actualAllocations (s r).pools (C r)).card:ℝ)^2*
        ‖frozenCoefficient (alloc r).val (C r) (R r) (s r).ν (s r).W (s r).P‖^2*
        (volume (s' r)/volume (s r))*forcedProfileCost (s' r)*weight r
      ∀(depth:ℕ)(b:live→ℝ)(E Bslot:ℝ),0≤E→1≤Bslot→
      (∀u,childA₁ u≠0)→(∀u,childA₂ u≠0)→
      (∀u,(childInput u).b₁≤b u)→(∀u,(childInput u).b₂≤b u)→
      (∀p∈P,Prime p)→(∀p∈P,16≤p.absNorm)→
      (∀u,∀v:(∀i,(childInput u).slots i),∀p∈P,¬p∣∏i,(v i:Ideal O))→
      (∀u,∀v:(∀i,(childInput u).slots i),
        markedNewtonCoefficient (childInput u) (childK u) (childR u) (τ u) (t u) (z u) v≠0→
        ∀n∈commonPool (b u) (childInput u).X₁ (childInput u).X₂ (childInput u).Y₁ (childInput u).Y₂,
        Squarefree ((childA₁ u*n.1)*(childA₂ u*n.2))→
        frozenProfile (childInput u).W₁ (childInput u).W₂ (childA₁ u) (childA₂ u)
          (childInput u).X₁ (childInput u).X₂ (childInput u).Y₁ (childInput u).Y₂ n≠0→
        rowWeight (τ u) (fixedBadMask*idealGenerator (childR u)) 1 (z u) (t u) (n.1*n.2)≠0→
        IsCoprime (childD u) ((∏i,(v i:Ideal O))*n.1*n.2) ∧
          (idealDividingPool P (n.1*n.2)).card≤depth ∧
          (idealDividingPool P (childD u*((∏i,(v i:Ideal O))*n.1*n.2))).card<P.card)→
      0<P.card→(∀u,2*((idealDividingPool P (childD u)).card+(depth:ℝ)+1)≤P.card)→
      (∀i,1≤P₀ i)→(∀i,∀p∈S₀ i,‖β₀ i p‖≤Bslot)→
      (∀i,∀p∈S₀ i,Prime p)→(∀i,∀p∈S₀ i,(p.absNorm:ℝ)≤2*P₀ i)→
      (∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,∀T:Finset α,
        (∑u∈Finset.univ.filter (fun u:live=>T⊆Finset.univ.map (childEmbedding u)),
          ‖newtonCofactorPlain (childInput u) (childA₁ u) (childA₂ u) (childR u) (b u) S A (τ u) (t u) (z u)*
            (∏j:T,normalizedSlot (τ u) (fixedBadMask*idealGenerator (childR u)) 1 (z u)
              (S₀ j) (β₀ j) (t u) (P₀ j))‖^2*paidWeight u)≤E)→
      (∑r∈rows,energy r*weight r)≤
        K₀*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*newtonMassBound depth^2*
          (collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E)) := by
  obtain ⟨K₀,hK₀,hselect⟩:=uniform_fixed_residual_original_forced_family N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro α Row _ rows ι _ s embedding S₀ β₀ P₀ hN hslots hcoeff hscale P A₁ A₂ D K C R seed L
    hL hKR hC hseed τ t z weight hw energy live
  obtain ⟨alloc,hf,pick,hpick,hbound⟩:=hselect rows ι s
    (fun r _=>(Fintype.card_le_of_injective (embedding r) (embedding r).injective).trans hN)
    A₁ A₂ D K C R seed L hL (fun _=>poolCorrection P) hC hseed τ t z weight hw
  refine ⟨alloc,hf,?_⟩
  intro s' A₁' A₂' D' K' R' modifier'
  refine ⟨pick,hpick,?_⟩
  intro childInput childEmbedding childA₁ childA₂ childD childK childR paidWeight depth b E Bslot
    hE hBslot hA₁ hA₂ hb₁ hb₂ hp hnorm havoid hsupport hP hbudget hP₀ hβ₀ hprime₀ hnorm₀ hcofactor
  have hw' (r:live):0≤paidWeight r := by
    have hr:=hw r (Finset.mem_filter.mp r.property).1
    have hv:0≤volume (s' r)/volume (s r):=div_nonneg (volume_pos _).le (volume_pos _).le
    have hfpc:=forcedProfileCost_nonneg (s' r)
    dsimp only [paidWeight]
    positivity
  have hfields (r:live):
      (∀i,(childInput r).slots i=S₀ (childEmbedding r i)) ∧
      (∀i,restoredSlotCoeff (childInput r) i=β₀ (childEmbedding r i)) ∧
      (∀i,(childInput r).P i=P₀ (childEmbedding r i)) := by
    have hfirst:=inherited_slot_fields (s r) (C r) (R r) (alloc r) (τ r) (t r)
      (embedding r) S₀ β₀ P₀ (hslots r) (hcoeff r) (hscale r)
    exact inherited_slot_fields (s' r) (pick r).1 (R' r) (pick r).2 (τ r) (t r)
      (inheritedSlotEmbedding (alloc r).val (embedding r)) S₀ β₀ P₀
      hfirst.1 hfirst.2.1 hfirst.2.2
  have hchildKR (r:live):childK r∣childR r := by
    have hfirst:K' r∣R' r:=marked_puncture_invariant (K r) (R r) (C r) (alloc r).val
      (hKR r) (Finset.mem_filter.mp (alloc r).property).2
    exact marked_puncture_invariant (K' r) (R' r) (pick r).1 (pick r).2.val hfirst
      (Finset.mem_filter.mp (pick r).2.property).2
  have hn:=actual_joint_corrected_newton_supported_subsets (Finset.univ:Finset live)
    (fun r=>liveIndices (pick r).2.val) childInput childEmbedding S₀ β₀ P₀
    (fun r=>(hfields r).1) (fun r=>(hfields r).2.1) (fun r=>(hfields r).2.2)
    P childA₁ childA₂ childD childK childR (fun r _=>hA₁ r) (fun r _=>hA₂ r) depth
    (fun r=>τ r) (fun r=>t r) (fun r=>z r) paidWeight (fun r _=>hw' r) b
    (fun r _=>hb₁ r) (fun r _=>hb₂ r) hp hnorm (fun r _=>havoid r)
    (fun r _=>hsupport r) hP (fun r _=>hbudget r) E hE hchildKR Bslot hBslot
    hP₀ hβ₀ hprime₀ hnorm₀ N hN hcofactor
  have hc:0≤K₀*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ)):=
    mul_nonneg hK₀.le (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
  apply hbound.trans
  calc
    _=(K₀*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ)))*
        ∑r:live,‖normalizedRow (childInput r)
          (markedSourceModifier (childA₁ r) (childA₂ r) (childD r) (childK r) (poolCorrection P))
          (childR r) 1 (τ r) (t r) (z r)‖^2*paidWeight r := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [selected_marked_child_value]
      dsimp only [paidWeight,childInput,childA₁,childA₂,childD,childK,childR]
      ring
    _≤(K₀*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ)))*
        (newtonMassBound depth^2*(collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E))) :=
      mul_le_mul_of_nonneg_left hn hc
    _=_:=by ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.uniform_fixed_plain_newton_supported
