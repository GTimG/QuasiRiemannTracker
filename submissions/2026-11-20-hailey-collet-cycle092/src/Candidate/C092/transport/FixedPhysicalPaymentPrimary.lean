/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedPhysicalPaymentH8

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
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentPrimary_b2a91ca8b3cb8847_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

open Filter CenteredMomentFiniteProfileExceptional

/-- Native sum over every surviving mark assignment. The label budget is
numerical and involves only the hole ideal, annulus product and R,G,L. -/
theorem primary_physical_square (ha : 0<a) (hb : 0≤b) (ω₁ ω₂ : Character)
    (ε Bcap : ℝ) (hε : 0<ε) (hB : 0≤Bcap) :
    ∃ J : ℕ,∃ S : Finset (ℕ×ℕ),∃ hS : (0,0)∈S,
    ∀ Q : Id,∃ C : ℝ,0<C ∧ ∀ᶠ U:ℝ in atTop,
    ∀ (r:Source ι a b) (D:FixedCubeDatum),D.Q=Q →
      (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ) ≤ U^Bcap →
    ∀ (G L:Id),G≠0 → L≠0 → ∀(B:commonAlloc r G) (E:fullPrimaryAlloc r G B L),
      (r.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*r.P i.val.val)*
        (r.R.absNorm:ℝ)*(G.absNorm:ℝ)*(L.absNorm:ℝ) ≤ U^Bcap → ∀v:ℝ,
    let qOrd:ℝ:=((primaryOrdinaryPrefix r G L B E).1.absNorm:ℝ)*
      (primaryOrdinaryPrefix r G L B E).2.absNorm
    ‖(Real.sqrt r.T:ℂ)⁻¹*coloredPrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v‖^2 ≤
      ((∏i:liveIndices E.val,256*r.M i.val.val*r.P i.val.val)*
        (C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε*
          (1+‖r.t₁+v‖+‖r.t₂+v‖)^J))^2*r.T*(qOrd*max 1 r.L)⁻¹ := by
  obtain ⟨J,S,hS,h⟩:=physical_pair_square (ι:=ι) ha hb ω₁ ω₂ ε Bcap hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩:=h Q
  refine ⟨C,hC,?_⟩
  filter_upwards [hCbound] with U hu
  intro r D hQ hcond G L hG hL B E hbudget v
  let d:=primaryOrdinaryPrefix r G L B E
  let pool:=fun i:liveIndices E.val=>r.pool i.val.val
  let w:=canonicalFrozenScalar D.row.χ ((r.R*G)*L) pool
    (fun i=>shiftedSlotCoefficient r v i.val.val) (fun i=>r.Wslot i.val.val) (fun i=>r.P i.val.val)
  let f:=fun p:(i:liveIndices E.val)→pool i=>
    let M:Id:=∏i,(p i).val
    let K:Id:=(punctureProduct r.S r.H*M)*((r.R*G)*L)
    let labels:=residualSuppliers M∪residualHoles K
    let allowed:=supplyingResidualPairs (D.twistColumn ω₁).row (D.twistColumn ω₂).row
      (residualSuppliers M) (residualHoles K) (residualHoles K)
    fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂)
      (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v)
      (fixedCubeBad (D.twistColumn ω₁) (D.twistColumn ω₂) labels) allowed
      (r.X₁/(d.1.absNorm:ℝ)) (r.X₂/(d.2.absNorm:ℝ))-
    fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂)
      (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v)
      (fixedCubeBad (D.twistColumn ω₁) (D.twistColumn ω₂) labels) allowed
      (r.Y₁/(d.1.absNorm:ℝ)) (r.Y₂/(d.2.absNorm:ℝ))
  let A:=C*(sourceControl S r.W₁*sourceControl S r.W₂)*U^ε*(1+‖r.t₁+v‖+‖r.t₂+v‖)^J
  let den:=r.T*(((d.1.absNorm:ℝ)*d.2.absNorm)*max 1 r.L)⁻¹
  have hden:0≤den:=mul_nonneg r.total_pos.le (inv_nonneg.mpr
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (zero_le_one.trans (le_max_left _ _))))
  have hf : ∀p,‖(Real.sqrt r.T:ℂ)⁻¹*f p‖^2 ≤ A^2*den:=by
    intro p
    have hM : (∏i,(p i).val)≠0:=Finset.prod_ne_zero_iff.mpr
      (fun i _=>(r.hp _ _ (p i).property).ne_zero)
    have hlabels:((∏P∈residualSuppliers (∏i,(p i).val)∪
      residualHoles ((punctureProduct r.S r.H*(∏i,(p i).val))*((r.R*G)*L)),P.val).absNorm:ℝ) ≤ U^Bcap:=by
      apply (actual_label_norm_cap r G L _ hG hL hM).trans
      apply le_trans _ hbudget
      gcongr
      exact remaining_mark_norm_cap r G L B E p
    have hh:=hu r D hQ hcond _ _ hlabels d
      (mul_ne_zero (commonLiveD_ne r G B).1 (fullPrimaryAlloc_ne r G B L E _))
      (mul_ne_zero (commonLiveD_ne r G B).2 (fullPrimaryAlloc_ne r G B L E _)) v
    exact hh.trans_eq (by dsimp [A,den];ring)
  have hsum:=weighted_square_sum w (fun p=>(Real.sqrt r.T:ℂ)⁻¹*f p) (A^2*den) (mul_nonneg (sq_nonneg A) hden) hf
  have hmass : (∑p,‖w p‖) ≤ ∏i:liveIndices E.val,256*r.M i.val.val*r.P i.val.val:=by
    convert residual_mark_mass r D G L B E v using 1
  calc
    _ = ‖∑p,w p*((Real.sqrt r.T:ℂ)⁻¹*f p)‖^2:=by
      unfold coloredPrimaryPhysicalSource
      dsimp only
      rw [Finset.mul_sum]
      congr 2
      apply Finset.sum_congr
      · ext p;simp
      · intro p hp
        dsimp [w,f,d,pool]
        ring
    _ ≤ (∑p,‖w p‖)^2*(A^2*den):=hsum
    _ ≤ (∏i:liveIndices E.val,256*r.M i.val.val*r.P i.val.val)^2*(A^2*den):=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hmass 2)
        (mul_nonneg (sq_nonneg A) hden)
    _ = _:=by dsimp only [A,den,d];ring

#print axioms primary_physical_square
end
end QRH.Cycle092.FixedCubeGauss
