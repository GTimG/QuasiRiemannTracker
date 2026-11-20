/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedPhysicalPaymentFrozen

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
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentOriginal_73762ff1f08936aa_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

open Filter CenteredMomentFiniteProfileExceptional

open CenteredMomentSourceLiveColumn CenteredMomentCommonRawCost

open CenteredMomentDivisorAllocation MixedCommonCoefficient

lemma mark_scale_split {κ:Type*} [Fintype κ] (B:Tuple κ) (P:κ→ℝ) :
    (∏i:κ with B (Sum.inl i)≠1,P i)*(∏j:liveIndices B,P j.val)=∏i:κ,P i := by
  rw [Finset.prod_coe_sort (liveIndices B) P,mul_comm]
  unfold liveIndices
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=>B (Sum.inl i)=1) P

lemma inject_product_le {κ κ₂:Type*} [Fintype κ] [Fintype κ₂] (f:κ→κ₂)
    (hf:Function.Injective f) (P:κ₂→ℝ) (hP:∀i,1≤P i) :
    (∏i:κ,P (f i))≤∏j:κ₂,P j := by
  classical
  rw [←Finset.prod_image (f:=P) (fun a _ b _ hab=>hf hab)]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (hP i)) (fun i _ _=>hP i)

lemma native_primary_full_payment (r:Source ι a b) (G L:Id) (hG:G≠0) (hL:Squarefree L)
    (B:commonAlloc r G) (E:fullPrimaryAlloc r G B L)
    (aL:Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2)))
    (hactive:allocationTerm L Finset.univ E.val aL≠0) :
    ((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm ≤
      (((primaryOrdinaryPrefix r G L B E).1.absNorm:ℝ)*
        (primaryOrdinaryPrefix r G L B E).2.absNorm)*
        (∏i:ι,(B.val (Sum.inl i)).absNorm:ℝ)*
        (∏i:liveIndices B.val,(E.val (Sum.inl i)).absNorm:ℝ) := by
  have hdiv:=allocationTerm_ne_zero_divides L hL E.val aL hactive
  have hn:=CenteredExceptionalCount.norm_le_of_dvd
    (Finset.prod_ne_zero_iff.mpr (fun j _=>fullPrimaryAlloc_ne r G B L E j)) hdiv
  have hBg:(G.absNorm:ℝ)=∏j,((B.val j).absNorm:ℝ):=by
    have hh:=congrArg (fun I:Id=>(I.absNorm:ℝ)) (commonAlloc_product r G B)
    simpa only [finiteTupleProduct,map_prod,Nat.cast_prod] using hh.symm
  have hh:=mul_le_mul_of_nonneg_left hn
    (show 0≤((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm by positivity)
  apply hh.trans_eq
  rw [hBg]
  simp only [map_prod,Nat.cast_prod,Fintype.prod_sum_type,Fin.prod_univ_two]
  unfold primaryOrdinaryPrefix commonLiveD
  simp only [Prod.fst,Prod.snd,map_mul,Nat.cast_mul,map_prod,Nat.cast_prod]
  ring

/-- Original normalization with both authentic frozen scalar factors. Only
numerical input bounds and the proved native primary source enter. -/
theorem original_primary_payment (r:Source ι a b) (G L:Id) (hG:G≠0) (hL:Squarefree L)
    (B:commonAlloc r G) (E:fullPrimaryAlloc r G B L)
    (aL:Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2)))
    (hactive:allocationTerm L Finset.univ E.val aL≠0)
    (v A:ℝ) (z:ℂ)
    (hsource:‖(Real.sqrt r.T:ℂ)⁻¹*z‖^2 ≤
      ((∏i:liveIndices E.val,256*r.M i.val.val*r.P i.val.val)*A)^2*r.T*
        ((((primaryOrdinaryPrefix r G L B E).1.absNorm:ℝ)*
          (primaryOrdinaryPrefix r G L B E).2.absNorm)*max 1 r.L)⁻¹) :
    ‖MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      frozenCoefficient B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P*
      frozenCoefficient E.val (finiteTupleProduct E.val) (r.R*G)
        (fun i:liveIndices B.val=>shiftedSlotCoefficient r v i.val)
        (fun i:liveIndices B.val=>r.Wslot i.val) (fun i:liveIndices B.val=>r.P i.val)*z‖^2 ≤
      ((∏i:ι,2*(r.M i)^2)^2*(∏i:ι,(256*r.M i)^2))*A^2*
        (r.T*(∏i:ι,r.P i))*
        ((((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm)*max 1 r.L)⁻¹ := by
  let cB:=frozenCoefficient B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P
  let cE:=frozenCoefficient E.val (finiteTupleProduct E.val) (r.R*G)
    (fun i:liveIndices B.val=>shiftedSlotCoefficient r v i.val)
    (fun i:liveIndices B.val=>r.Wslot i.val) (fun i:liveIndices B.val=>r.P i.val)
  let PB:=∏i:ι with B.val (Sum.inl i)≠1,r.P i
  let PE:=∏i:liveIndices B.val with E.val (Sum.inl i)≠1,r.P i.val
  let PR:=∏i:liveIndices E.val,r.P i.val.val
  let qB:ℝ:=∏i:ι,(B.val (Sum.inl i)).absNorm
  let qE:ℝ:=∏i:liveIndices B.val,(E.val (Sum.inl i)).absNorm
  let qO:ℝ:=((primaryOrdinaryPrefix r G L B E).1.absNorm:ℝ)*
    (primaryOrdinaryPrefix r G L B E).2.absNorm
  let K₀:=∏i:ι,2*(r.M i)^2
  let KE:=∏i:liveIndices B.val,2*(r.M i.val)^2
  let KR:=∏i:liveIndices E.val,(256*r.M i.val.val)^2
  let mass:=∏i:liveIndices E.val,256*r.M i.val.val*r.P i.val.val
  have hP(i):0<r.P i:=zero_lt_one.trans_le (r.hP i)
  have hPB:0<PB:=Finset.prod_pos (fun i _=>hP i)
  have hPE:0<PE:=Finset.prod_pos (fun i _=>hP i.val)
  have hPR:0<PR:=Finset.prod_pos (fun i _=>hP i.val.val)
  have hQB:0<qB:=by
    apply Finset.prod_pos
    intro i _
    have hh:0<(B.val (Sum.inl i)).absNorm:=Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonAlloc_ne r G B (Sum.inl i)))
    exact_mod_cast hh
  have hQE:0<qE:=by
    apply Finset.prod_pos
    intro i _
    have hh:0<(E.val (Sum.inl i)).absNorm:=Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (fullPrimaryAlloc_ne r G B L E (Sum.inl i)))
    exact_mod_cast hh
  have hBcost:PB⁻¹*‖cB‖^2≤K₀*qB⁻¹:=by
    simpa only [PB,cB,K₀,qB,Finset.prod_inv_distrib] using
      frozen_inverse_mark_cost B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P r.M
        (commonAlloc_ne r G B) hP r.hM
        (fun i=>shiftedSlotCoefficient_norm_le_one r v i _ (commonAlloc_ne r G B _))
        r.hWnorm (fun i x hx=>(r.hW i hx).2)
  have hEcost:PE⁻¹*‖cE‖^2≤KE*qE⁻¹:=by
    simpa only [PE,cE,KE,qE,Finset.prod_inv_distrib] using
      frozen_inverse_mark_cost E.val (finiteTupleProduct E.val) (r.R*G)
        (fun i:liveIndices B.val=>shiftedSlotCoefficient r v i.val)
        (fun i:liveIndices B.val=>r.Wslot i.val) (fun i:liveIndices B.val=>r.P i.val)
        (fun i:liveIndices B.val=>r.M i.val) (fullPrimaryAlloc_ne r G B L E)
        (fun i=>hP i.val) (fun i=>r.hM i.val)
        (fun i=>shiftedSlotCoefficient_norm_le_one r v i.val _ (fullPrimaryAlloc_ne r G B L E _))
        (fun i x=>r.hWnorm i.val x) (fun i x hx=>(r.hW i.val hx).2)
  have hscale:(∏i:ι,r.P i)=PB*PE*PR:=by
    rw [←mark_scale_split B.val r.P]
    rw [←mark_scale_split E.val (fun i:liveIndices B.val=>r.P i.val)]
    dsimp only [PB,PE,PR]
    ring
  have hmass:mass^2/PR=KR*PR:=by
    dsimp only [mass,KR,PR]
    rw [Finset.prod_mul_distrib,mul_pow,Finset.prod_pow]
    field_simp [(hPR.ne')]
  have hK(i):1≤2*(r.M i)^2:=by nlinarith [r.hM i,sq_nonneg (r.M i-1)]
  have hKE:KE≤K₀:=inject_product_le (fun i:liveIndices B.val=>i.val) Subtype.val_injective _ hK
  have hinc:Function.Injective (fun i:liveIndices E.val=>i.val.val):=
    Subtype.val_injective.comp Subtype.val_injective
  have hKR:KR≤∏i:ι,(256*r.M i)^2:=inject_product_le _ hinc (fun i:ι=>(256*r.M i)^2) (fun i=>by nlinarith [r.hM i,sq_nonneg (r.M i-1)])
  have hPRall:PR≤∏i:ι,r.P i:=inject_product_le _ hinc r.P r.hP
  have hfull:=native_primary_full_payment r G L hG hL B E aL hactive
  have hq0:0<(((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm):=by
    apply mul_pos
    · apply mul_pos
      · exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.hd.1))
          (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.hd.2))
      · exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
    · exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL.ne_zero)
  have hqO:0<qO:=by
    have hh:0<qO*qB*qE:=(hq0.trans_le hfull)
    exact pos_of_mul_pos_left (pos_of_mul_pos_left hh hQE.le) hQB.le
  have hnorm:
      ‖MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*cB*cE*z‖^2=
      (PB⁻¹*‖cB‖^2)*(PE⁻¹*‖cE‖^2)*(‖(Real.sqrt r.T:ℂ)⁻¹*z‖^2/PR):=by
    rw [r.hpX,norm_mul,norm_mul,norm_mul,mul_pow,mul_pow,mul_pow,
      MixedLiveNormalization.normalization_sq r.T r.total_pos r.P hP,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq r.T r.total_pos,hscale]
    field_simp
  have hT:0≤r.T:=r.total_pos.le
  have hK0:0≤K₀:=Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (sq_nonneg _))
  have hPall:0≤∏i:ι,r.P i:=Finset.prod_nonneg (fun i _=>(hP i).le)
  rw [hnorm]
  calc
    _ ≤ (K₀*qB⁻¹)*(KE*qE⁻¹)*((mass*A)^2*r.T*(qO*max 1 r.L)⁻¹/PR):=by
      apply mul_le_mul
      · exact mul_le_mul hBcost hEcost (mul_nonneg (inv_nonneg.mpr hPE.le) (sq_nonneg _)) (by positivity)
      · exact div_le_div_of_nonneg_right hsource hPR.le
      · exact div_nonneg (sq_nonneg _) hPR.le
      · positivity
    _ = K₀*KE*(mass^2/PR)*A^2*r.T*(qO*qB*qE*max 1 r.L)⁻¹:=by
      simp only [mul_inv];ring
    _ = K₀*KE*(KR*PR)*A^2*r.T*(qO*qB*qE*max 1 r.L)⁻¹:=by rw [hmass]
    _ ≤ K₀*K₀*((∏i:ι,(256*r.M i)^2)*(∏i:ι,r.P i))*A^2*r.T*
        (qO*qB*qE*max 1 r.L)⁻¹:=by
      gcongr
    _ ≤ _:=by
      have hinv: (qO*qB*qE*max 1 r.L)⁻¹ ≤
        ((((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm)*max 1 r.L)⁻¹:=
        (inv_le_inv₀ (by positivity) (by positivity)).mpr
          (mul_le_mul_of_nonneg_right hfull (zero_le_one.trans (le_max_left _ _)))
      have hh:=mul_le_mul_of_nonneg_left hinv
        (show 0≤K₀*K₀*((∏i:ι,(256*r.M i)^2)*(∏i:ι,r.P i))*A^2*r.T by
          exact mul_nonneg (by positivity) r.total_pos.le)
      exact hh.trans_eq (by dsimp only [K₀];ring)

#print axioms original_primary_payment
end
end QRH.Cycle092.FixedCubeGauss
