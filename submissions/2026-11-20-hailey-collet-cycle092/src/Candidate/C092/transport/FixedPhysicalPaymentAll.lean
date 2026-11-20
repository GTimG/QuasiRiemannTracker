/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedPhysicalPaymentTerm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentAll_892c80e5f8bffc20_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

open Filter CenteredMomentFiniteProfileExceptional

open CenteredMomentSourceLiveColumn CenteredMomentCommonRawCost

open CenteredMomentDivisorAllocation MixedCommonCoefficient

open MixedCommonHeights

abbrev allocationLabels (r:Source ι a b) (G L:Id) :=
  (B:commonAlloc r G) ×
    ((Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2)))×(fullPrimaryAlloc r G B L))

def allocationCount (r:Source ι a b) (G L:Id) : ℕ :=
  ∑B:commonAlloc r G,
    Fintype.card (Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2)))*(fullPrimaryAlloc r G B L).card

lemma allocationLabels_card (r:Source ι a b) (G L:Id) :
    Fintype.card (allocationLabels r G L)=allocationCount r G L:=by
  simp only [allocationLabels,allocationCount,Fintype.card_sigma,Fintype.card_prod,Fintype.card_coe]

lemma allocated_height_sum (r:Source ι a b) (ha:0<a) (hb:0≤b) (D:FixedCubeDatum)
    (ω₁ ω₂:Character) (G L:Id) (v:ℝ) :
    coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v=
      residualPhase (r.X₁*r.X₂) r.d G v*
        ∑l:allocationLabels r G L,nativePhysicalTerm r ha hb D ω₁ ω₂ G L l.1 l.2.1 l.2.2 v:=by
  unfold coloredFullyAllocatedPhysicalHeight coloredNativePrimaryPhysicalRow
  simp only [allocationLabels,Fintype.sum_sigma,Fintype.sum_prod_type,nativePhysicalTerm,
    Finset.mul_sum,mul_assoc]
  apply Finset.sum_congr
  · ext B;simp
  · intro B hB
    apply Finset.sum_congr
    · ext aL;simp
    · intro aL haL
      apply Finset.sum_congr
      · ext E;simp
      · intro E hE;rfl

lemma allocated_height_of_terms (r:Source ι a b) (ha:0<a) (hb:0≤b) (D:FixedCubeDatum)
    (ω₁ ω₂:Character) (G L:Id) (hG:G≠0) (v K:ℝ) (hK:0≤K)
    (hterm:∀(B:commonAlloc r G)
      (aL:Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2))) (E:fullPrimaryAlloc r G B L),
      ‖nativePhysicalTerm r ha hb D ω₁ ω₂ G L B aL E v‖^2≤K) :
    ‖coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v‖^2≤(allocationCount r G L:ℝ)^2*K:=by
  rw [allocated_height_sum,norm_mul,
    residual_phase_norm _ (r.hpX.symm ▸ r.total_pos) r.d r.hd G hG v,one_mul]
  have hh:=weighted_square_sum (fun _:allocationLabels r G L=>(1:ℂ))
    (fun l=>nativePhysicalTerm r ha hb D ω₁ ω₂ G L l.1 l.2.1 l.2.2 v) K hK
    (fun l=>hterm l.1 l.2.1 l.2.2)
  simpa only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    allocationLabels_card] using hh

/-- Native H15 on the full actual allocated physical height. All ordinary
heights, original full normalization and exact native allocation counts remain. -/
theorem allocated_physical_square (ha:0<a) (hb:0≤b) (ω₁ ω₂:Character)
    (ε Bcap:ℝ) (hε:0<ε) (hB:0≤Bcap) :
    ∃ J:ℕ,∃ S:Finset (ℕ×ℕ),∃ hS:(0,0)∈S,
    ∀ Q:Id,∃ C:ℝ,0<C ∧ ∀ᶠ U:ℝ in atTop,
    ∀ (r:Source ι a b) (D:FixedCubeDatum),D.Q=Q →
      (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ)≤U^Bcap →
    ∀ (G L:Id),G≠0 → Squarefree L →
      (∀ (B:commonAlloc r G) (E:fullPrimaryAlloc r G B L),
        (r.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*r.P i.val.val)*
          (r.R.absNorm:ℝ)*(G.absNorm:ℝ)*(L.absNorm:ℝ)≤U^Bcap) → ∀v:ℝ,
    ‖coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v‖^2≤
      (allocationCount r G L:ℝ)^2*fixedMarkCost r*
        (C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε*
          (1+‖r.t₁+v‖+‖r.t₂+v‖)^J)^2*(r.T*(∏i:ι,r.P i))*
        ((((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm)*max 1 r.L)⁻¹:=by
  obtain ⟨J,S,hS,h⟩:=native_term_square (ι:=ι) ha hb ω₁ ω₂ ε Bcap hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩:=h Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hCbound] with U hu
  intro r D hQ hcond G L hG hL hbudget v
  let K:=fixedMarkCost r*(C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε*
      (1+‖r.t₁+v‖+‖r.t₂+v‖)^J)^2*(r.T*(∏i:ι,r.P i))*
      ((((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm)*max 1 r.L)⁻¹
  have hK:0≤K:=mul_nonneg
    (mul_nonneg (mul_nonneg (fixedMarkCost_nonneg r) (sq_nonneg _))
      (mul_nonneg r.total_pos.le (Finset.prod_nonneg (fun i _=>zero_le_one.trans (r.hP i)))))
    (by positivity)
  have hh:=allocated_height_of_terms r ha hb D ω₁ ω₂ G L hG v K hK
    (fun B aL E=>hu r D hQ hcond G L hG hL B E (hbudget B E) aL v)
  exact hh.trans_eq (by dsimp only [K];ring)

#print axioms allocated_physical_square
#print axioms allocated_height_of_terms
end
end QRH.Cycle092.FixedCubeGauss
