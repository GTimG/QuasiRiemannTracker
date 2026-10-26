/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete forced-prime choice and Newton/collision reduction share one
original finite row family. Only literal cofactor families remain at the inlet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalForcedNewton
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

theorem uniform_fixed_residual_newton_supported (N:ℕ) (ε:ℝ) (hε:0<ε) :
    ∃K₀:ℝ,0<K₀ ∧ ∀{α Row:Type}[Fintype α]
      (rows:Finset Row)(ι:Row→Type)[∀u,Fintype (ι u)]
      (s:∀u,Input (ι u))(embedding:∀u,ι u↪α)
      (S₀:α→Finset (Ideal O))(β₀:α→Ideal O→ℂ)(P₀:α→ℝ),
    Fintype.card α≤N→
    (∀u i,(s u).slots i=S₀ (embedding u i))→
    (∀u i,restoredSlotCoeff (s u) i=β₀ (embedding u i))→
    (∀u i,(s u).P i=P₀ (embedding u i))→
    ∀(P:Finset (Ideal O))(A₁ A₂ D K R:Row→Ideal O)(L:Ideal O),
    Squarefree L→(∀u,K u∣R u)→
    ∀(τ:Row→Character)(t:Row→ℝ)(z:Row→O)(weight:Row→ℝ),
    (∀u∈rows,0≤weight u)→
    let modifier:=fun u=>markedSourceModifier (ι:=ι u) (A₁ u) (A₂ u) (D u) (K u) (poolCorrection P)
    let live:=nonzeroRows rows ι s modifier R (fun _=>L) τ t z
    ∃pick:(u:live)→ChildIndex (s u) (modifier u) (R u) L,
      (∀u:live,frozenCoefficient (pick u).2 (pick u).1 (R u) (s u).ν (s u).W (s u).P≠0 ∧
        0<childValue (s u) (modifier u) (R u) L (τ u) (t u) (z u) (pick u) ∧
        L∣((pick u).1:Ideal O) ∧ ((pick u).1:Ideal O)∣L^2) ∧
      let childInput:=fun u:live=>child (s u) (pick u).1 (R u) (pick u).2 (τ u) (t u)
      let childEmbedding:=fun u:live=>inheritedSlotEmbedding (pick u).2.val (embedding u)
      let childA₁:=fun u:live=>A₁ u*(pick u).2.val (Sum.inr 0)
      let childA₂:=fun u:live=>A₂ u*(pick u).2.val (Sum.inr 1)
      let childD:=fun u:live=>D u*(pick u).1
      let childK:=fun u:live=>K u*markedProduct (pick u).2.val
      let childR:=fun u:live=>R u*(pick u).1
      let paidWeight:=fun u:live=>forcedProfileCost (s u)*weight u
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
      (∑u∈rows,‖normalizedRow (s u) (modifier u) (R u) L (τ u) (t u) (z u)‖^2*weight u)≤
        K₀*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*newtonMassBound depth^2*(collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E)) := by
  obtain ⟨K₀,hK₀,hbase⟩:=uniform_joint_forced_newton_supported N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro α Row _ rows ι _ s embedding S₀ β₀ P₀ hN hslots hcoeff hscale P A₁ A₂ D K R L hL hKR τ t z weight hw
  intro modifier live
  obtain ⟨pick,hpick,hbound⟩:=hbase rows ι s embedding S₀ β₀ P₀ hN hslots hcoeff hscale
    P A₁ A₂ D K R (fun _=>L) (fun _ _=>hL) hKR τ t z weight hw
  refine ⟨pick,hpick,?_⟩
  intro childInput childEmbedding childA₁ childA₂ childD childK childR paidWeight depth b E Bslot
    hE hBslot hA₁ hA₂ hb₁ hb₂ hp hnorm havoid hsupport hP hbudget hP₀ hβ₀ hprime₀ hnorm₀ hcofactor
  let c:=(L.absNorm:ℝ)^ε/(L.absNorm:ℝ)
  have hc:0≤c:=div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  have hh:=hbound depth b (c*E) Bslot (mul_nonneg hc hE) hBslot hA₁ hA₂ hb₁ hb₂ hp hnorm
    havoid hsupport hP hbudget hP₀ hβ₀ hprime₀ hnorm₀ ?_
  · apply hh.trans_eq
    dsimp only [c]
    ring
  · intro S hS A hA T
    have ht:=mul_le_mul_of_nonneg_left (hcofactor S hS A hA T) hc
    rw [Finset.mul_sum] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [paidWeight,c,childInput,childA₁,childA₂,childR]
    ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.uniform_fixed_residual_newton_supported
