/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal actual-row common-witness detector count from natural and global ordinary source moments. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.CountMoments
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Assembly.Count.FromMoments
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.LewkoStage1Return
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber Cycle25DetectorBranchBudget
open Cycle25DetectorRawFiber Cycle25DetectorRowCount

theorem count_from_piecewise_moments
 (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
 (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
 (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
 (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
 (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
 (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
 (εm : ℝ) (hεm : 0<εm) :
 ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
 ∀Bsrc lam cap sourceCap mLo mHi : ℝ, 1<lam → 0≤mLo → 2/5≤mHi → mHi<1/2 →
 cap≤sourceCap → cap≤7/37 →
 ∀(a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
 1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
 1≤tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 →
 0<ν → ν≤1/100000 → 0≤C → 0≤height →
 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
 ∀{Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
 ∀cross target : ℝ, 23/37≤cross → cross≤1 → mLo+ε≤tstar-cross →
 1-(2*a-1)*((F.q/(2*a-1))+(1-F.q/(2*a-1))*cross)=target →
 plainCurve Bsrc lam cap (2*a-1) (F.q/(2*a-1)) (tstar-cross)≤target →
 1-2*(2*a-1)*mHi-2*((2*a-1)*(F.q/(2*a-1)))*(1-2*mHi)/(6*κplain)≤target →
 (∀m : ℝ,mLo≤m → m≤mHi → ν<min cap ((Bsrc-2*m)/lam)) →
 Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
 AffineMarkedMoment F (broadFace Bsrc lam sourceCap) C height εm →
 (F.rows.card:ℝ)≤fiberConstant C height K₀*
 U^(max target (1-(2*a-1)+(5/6-(2*a-1))*(tstar-1))+159*ε+εm+F.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro Bsrc lam cap sourceCap mLo mHi hlam hmLo hmHi hmHiHalf hcap hcapSmall a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hν1 hC hh hf
    Label Slot F cross target hrN hrN1 hmN hcross hplainCross htail hwidth moments affine
  let δ := 2*a-1
  let x := F.q/δ
  have hδ : 0<δ := by dsimp [δ]; linarith
  have ha' : 1/2≤a := by linarith
  have hδ1 : δ≤1 := by dsimp [δ]; linarith
  obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
  have hx : 0≤x := div_nonneg hq0 hδ.le
  have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ*x=F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  have hUp : 0<U := zero_lt_one.trans hU
  obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.original.inverse_raw
  have hI0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments.original hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23/37≤F.r → F.r<1 → ν<(1-F.r)/2 →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^((1-δ*(x+(1-x)*F.r))+commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rw [hqx] at hl
    simpa only [Parameters.inverseExp, inverseExponent] using hl
  have hA : mLo ≤ F.m → F.m ≤ mHi →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(plainCurve Bsrc lam cap δ x F.m+2*(δ*x)*ν+commonLoss ε εm F.mesh ν) := by
    intro hm1 hm2
    have hm0 : 0≤F.m := hmLo.trans hm1
    have hb := piecewise_marked_count F moments affine hU (by linarith) (by linarith) hC hh hf
      (hm2.trans_lt hmHiHalf) hm0 (by linarith) hν.le (hwidth F.m hm1 hm2) hcap hcapSmall
    change (F.rows.card:ℝ)≤192*(1+height)*C*
      U^(plainCurve Bsrc lam cap δ x F.m+2*F.q*ν+4*ε+δ*F.mesh+εm) at hb
    apply promote _ _ _ hconstP hb
    rw [←hqx]
    have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
    unfold commonLoss
    linarith
  have hP : mHi ≤ F.m → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^((1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*κplain))+commonLoss ε εm F.mesh ν) := by
    intro hm hm2 hv
    have hd : 0<6*κplain := by linarith only [hk]
    have hmHi : (2/5:ℝ) ≤ F.m := hmHi.trans hm
    have hc5 : (1-2*F.m)/(6*κplain) ≤ 5/42 := by
      rw [div_le_iff₀ hd]; linarith only [hmHi, hk]
    have hz : 0≤(1-2*F.m)/(6*κplain)-ν := by linarith only [hv]
    have hz' : (1-2*F.m)/(6*κplain)-ν≤7/37 := by linarith only [hc5, hν]
    have hκν : 0 ≤ 6*κplain*ν := mul_nonneg hd.le hν.le
    have hcap : 2*F.m+6*κplain*((1-2*F.m)/(6*κplain)-ν)≤1 := by
      rw [mul_sub,mul_div_cancel₀ _ hd.ne']
      linarith only [hκν]
    have hb := Cycle25DetectorRawFiber.plain_marked_count F moments hU ha'
      (by linarith only [hk]) hC hh hf ((1-2*F.m)/(6*κplain)-ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss F.m δ x κplain ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx, Parameters.oldPlainExp] using hl
  have hc' := common_witness_count_bound (F.rows.card:ℝ) (fiberConstant C height K₀) U δ x
    κplain tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε cross target mLo mHi
    (plainCurve Bsrc lam cap δ x)
    (fun u v h=>plainCurve_antitone hlam hδ.le hx hx' h)
    (fun u g hg=>plainCurve_shift hlam hδ.le hδ1 hx hx' hg)
    hplainCross hconst hU.le hδ.le (by dsimp [δ];linarith) hx hx' hk hk1 hν.le hε
    hgeom.1 hgeom.2.1 hrN hrN1 (by linarith) hcross htail hI0 hP0 hI hA hP
  convert hc' using 1 <;> congr 2
  unfold commonLoss
  ring

end
end QRH.LewkoStage1Return
#print axioms QRH.LewkoStage1Return.count_from_piecewise_moments
