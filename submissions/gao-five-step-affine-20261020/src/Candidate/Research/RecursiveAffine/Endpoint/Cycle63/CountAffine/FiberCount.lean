/- Detector fiber and batch counts with Collet's initial affine moment on the plain witness.
The structure follows Collet's Cycle25 `count_from_raw_moments` and the detector-affine
submission of DaysSky (both Apache-2.0); the branch combination is `merged_count_bound`.
Released under Apache 2.0. -/
import Candidate.Cycle25.Assembly.Count.Moments
import Candidate.Cycle25.Assembly.Count.Budget
import Candidate.Cycle25.Assembly.Count.Optimization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFixedAmplitudeCount
import Candidate.Cycle25.Assembly.Count.Endpoint
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Count.ArithmeticIdentity
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.Bernstein.Feedback
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.CountAffine.Branch
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.CountAffine.PlainFiber
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.Constants

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_CountAffine_FiberCount : Cycle63.AffineLedger := Cycle153.Root.rootLedger


namespace OAI.SevenEighths.Cycle153EndpointDetectorRawFiber
open OAI.SevenEighths.Cycle25DetectorRawFiber
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The marked plain moment at Collet's affine capacity, inside the window of his
initial affine moment. -/
def AffineMarkedMoment (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (C height εm : ℝ) : Prop := ∀ selected : Finset Slot, selected ⊆ F.slots →
    Cycle153Endpoint.CountAffine.windowBottom ≤ F.m → F.m ≤ Cycle153Endpoint.CountAffine.plainLengthTop →
    Cycle153.Root.floor ≤ (∑ s∈selected, F.widths s) → (∑ s∈selected, F.widths s) ≤ Cycle153.MarkedRootPrice.top →
    2*F.m+Cycle153Endpoint.Arithmetic.lambda*(∑ s∈selected, F.widths s) ≤ Cycle153Endpoint.Arithmetic.B →
    ∀ j k : ℕ, j+k ≤ 2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

theorem zS_window {m ν : ℝ} (_hm : Cycle153Endpoint.CountAffine.windowBottom ≤ m) (hm1 : m ≤ Cycle153Endpoint.CountAffine.plainTop)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1/100) :
    0 ≤ Cycle153Endpoint.CountAffine.zS m-ν ∧ Cycle153Endpoint.CountAffine.zS m-ν ≤ Cycle153.MarkedRootPrice.top ∧
      2*m+Cycle153Endpoint.Arithmetic.lambda*(Cycle153Endpoint.CountAffine.zS m-ν) ≤ Cycle153Endpoint.Arithmetic.B := by
  obtain ⟨hl, hl'⟩ := Cycle153Endpoint.Arithmetic.lambda_bounds
  have hB := Cycle153Endpoint.CountAffine.B_bounds
  simp only [Cycle153Endpoint.CountAffine.plainTop] at hm1
  have hq : (Cycle153Endpoint.Arithmetic.B-2*m)/Cycle153Endpoint.Arithmetic.lambda ≥ 1/50 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith)]
    nlinarith [hB.1]
  have hzlo : 1/50 ≤ Cycle153Endpoint.CountAffine.zS m := le_min (by norm_num [Cycle153.MarkedRootPrice.top]) hq
  have hzhi : Cycle153Endpoint.CountAffine.zS m ≤ Cycle153.MarkedRootPrice.top := min_le_left _ _
  have hzq : Cycle153Endpoint.CountAffine.zS m ≤ (Cycle153Endpoint.Arithmetic.B-2*m)/Cycle153Endpoint.Arithmetic.lambda :=
    min_le_right _ _
  refine ⟨by linarith, by linarith, ?_⟩
  have h1 : Cycle153Endpoint.Arithmetic.lambda*Cycle153Endpoint.CountAffine.zS m ≤ Cycle153Endpoint.Arithmetic.B-2*m := by
    have := mul_le_mul_of_nonneg_left hzq (by linarith : (0:ℝ) ≤ Cycle153Endpoint.Arithmetic.lambda)
    rwa [mul_div_cancel₀ _ (by linarith : Cycle153Endpoint.Arithmetic.lambda ≠ 0)] at this
  nlinarith

/-- A plain fiber in the affine window, counted with the affine capacity `zS m - ν`. -/
theorem affine_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c κinverse C height εm ν : ℝ} (moments : OAI.SevenEighths.Cycle25DetectorRawFiber.Moments F κplain c κinverse C height εm)
    (affine : AffineMarkedMoment F C height εm)
    (hU : 1 < U) (ha : 1/2 ≤ a) (hk0 : 0 ≤ κplain) (hk1 : κplain ≤ 3/4)
    (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1/100)
    (hmlo : Cycle153Endpoint.CountAffine.windowBottom ≤ F.m) (hmhi : F.m ≤ Cycle153Endpoint.CountAffine.plainTop) :
    (F.rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(1-2*(2*a-1)*F.m-2*F.q*(Cycle153Endpoint.CountAffine.zS F.m-ν)+4*ε+(2*a-1)*F.mesh+εm) := by
  obtain ⟨hz0, hz1, hz2⟩ := zS_window hmlo hmhi hν hν1
  have htop : Cycle153Endpoint.CountAffine.plainTop ≤ Cycle153Endpoint.CountAffine.plainLengthTop :=
    by norm_num [Cycle153Endpoint.CountAffine.plainTop,Cycle153Endpoint.CountAffine.plainLengthTop]
  exact Cycle153EndpointAffinePlainFiberCount.affine_plain_fiber_count M H F.rows F.nonempty F.family
    U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth
    (Cycle153Endpoint.CountAffine.zS F.m-ν) κplain εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz0 (by linarith [F.supply, (show Cycle153.MarkedRootPrice.top ≤ (1/20:ℝ) by norm_num [Cycle153.MarkedRootPrice.top])]) F.fixed_bin hk0 hk1 hC hh hf hmlo hmhi hz1 hz2
    (fun selected hsel hw1 hw2 hcap => affine selected hsel hmlo (hmhi.trans htop) hw1 hw2 hcap)
    moments.plain_marked

end
end OAI.SevenEighths.Cycle153EndpointDetectorRawFiber

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle153EndpointAffineCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorBranchBudget
open Cycle153EndpointDetectorRawFiber Cycle25DetectorRowCount
open Cycle153Endpoint.CountAffine

/-- Collet's fiber count, and the fiber count at the affine cutoff `tStar`, from one common
choice of inverse-moment parameters. -/
theorem count_from_raw_moments_affine
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      (∀ (a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (shortExponent (2*a-1) (F.q/(2*a-1)) κplain tstar) (longExponent (2*a-1) tstar)+
          159*ε+εm+F.mesh+7*ν)) ∧
      (∀ (a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      inRegion (2*a-1) (F.q/(2*a-1)) →
      tstar = max (tStar (2*a-1) (F.q/(2*a-1))) (tStarC (2*a-1) (F.q/(2*a-1))) →
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      AffineMarkedMoment F C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(newBranch κplain (2*a-1) (F.q/(2*a-1))+159*ε+εm+F.mesh+7*ν)) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  constructor
  · intro a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hC hh hf
      Label Slot F moments
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
          U^(inverseExponent δ x F.r+commonLoss ε εm F.mesh ν) := by
      intro hr hr1 hv
      obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
      have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
      apply promote _ _ _ hconstI hb
      have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rwa [hqx] at hl
    have hP : F.r≤ crossing x κplain tstar → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*κplain)+commonLoss ε εm F.mesh ν) := by
      intro hr hm hv
      obtain ⟨hz,hz',hcap⟩ := plain_requested_capacity κplain x tstar F.r F.m ε ν hk hk1 hx hx' ht ht'
        hr hgeom.1 (by linarith) hν.le hv
      have hb := Cycle25DetectorRawFiber.plain_marked_count F moments hU ha' (by linarith) hC hh hf
        ((1-2*F.m)/(6*κplain)-ν) hz hz' hcap
      apply promote _ _ _ hconstP hb
      have hl := plain_marked_loss F.m δ x κplain ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      simpa only [hqx] using hl
    have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x κplain
      tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith) hx hx' hk hk1
      ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
    convert hc' using 1; congr 2
    unfold commonLoss
    ring
  · intro a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall hk hk1 hν hν1 hC hh hf
      Label Slot F hreg htstar moments affine
    let δ := 2*a-1
    let x := F.q/δ
    have hδ : 0<δ := by dsimp [δ]; linarith
    have ha' : 1/2≤a := by linarith
    have hδ1 : δ≤1 := by dsimp [δ]; linarith
    obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
    have hx : 0≤x := div_nonneg hq0 hδ.le
    have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
    have hqx : δ*x=F.q := by dsimp [x]; field_simp
    have hfacts := facts_of_region hreg
    have hthi : tstar ≤ 3/2 := by
      rw [htstar]; exact max_le hfacts.affine.thi hfacts.capped.thi
    have htlo : cutoffFloor ≤ tstar := by
      rw [htstar]; exact le_max_of_le_left hfacts.affine.tlo
    unfold cutoffFloor inverseFloor windowBottom crossingSlack at htlo
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
    have hI : inverseFloor≤F.r → F.r<1 → ν<(1-F.r)/2 →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(1-δ*(x+(1-x)*F.r)+commonLoss ε εm F.mesh ν) := by
      intro hr hr1 hv
      unfold inverseFloor at hr
      obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
      have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
      apply promote _ _ _ hconstI hb
      have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rw [hqx] at hl
      have he : inverseExponent δ x F.r = 1-δ*(x+(1-x)*F.r) := by
        unfold inverseExponent; ring
      rwa [he] at hl
    have hPo : plainTop<F.m → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(plainOld κplain δ x F.m+commonLoss ε εm F.mesh ν) := by
      intro hm hm2 hv
      have hd : 0<6*κplain := by linarith only [hk]
      have hc5 : (1-2*F.m)/(6*κplain) ≤ 5/42 := by
        rw [div_le_iff₀ hd]; simp only [plainTop] at hm; linarith only [hm, hk]
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
      have he : plainOld κplain δ x F.m = 1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*κplain) := by
        unfold plainOld; ring
      rw [he]
      simpa only [hqx] using hl
    have hPn : windowBottom≤F.m → F.m≤plainTop →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(plainNew δ x F.m+2*ν+commonLoss ε εm F.mesh ν) := by
      intro hm1 hm2
      unfold windowBottom at hm1
      have hb := affine_marked_count F moments affine hU ha' (by linarith) hk1 hC hh hf hν.le hν1 hm1 hm2
      apply promote _ _ _ hconstP hb
      rw [← hqx]
      have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
      have hq2 : 2*(δ*x) ≤ 1 := by nlinarith only [mul_nonneg hδ.le (sub_nonneg.mpr hx'), hδ1]
      have hqν : 2*(δ*x)*ν ≤ ν := by nlinarith only [hq2, hν, mul_nonneg hδ.le hx]
      unfold plainNew commonLoss
      nlinarith only [hm, hqν, hε, hν]
    have hb := merged_count_bound (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x
      κplain tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith)
      hx hx' hk hk1 hν.le hε (by unfold crossingSlack; linarith) hfacts.affine hfacts.capped htstar
      hgeom.1 hgeom.2.1 hI0 hP0 hI hPo hPn
    have he : newBranch κplain δ x+commonLoss ε εm F.mesh ν+6*ν+5*ε =
        newBranch κplain δ x+159*ε+εm+F.mesh+7*ν := by
      unfold commonLoss; ring
    rw [he] at hb
    exact hb

end SevenEighths.Cycle153EndpointAffineCount
end
end OAI
