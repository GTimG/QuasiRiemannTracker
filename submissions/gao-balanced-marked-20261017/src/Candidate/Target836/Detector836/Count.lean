/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Cycle25.Assembly.Count.Optimization
import Candidate.Cycle25.Assembly.Count.FromMoments
import Candidate.Cycle25.Assembly.Count.FixedAmplitude
import Candidate.Cycle25.Assembly.Count.Adaptive
import Candidate.Target836.Detector836.Arith

/-! Per-fiber detector count with the affine marked plain moment.
The fiber count of Cycle25 (`count_from_raw_moments`) is repeated with one
extra branch: for plain length `m ∈ [mLo, mHi]` the marked plain moment is
requested at the affine capacity `(Bc-2m)/lam` (Cycle63 Theorem 2.2) instead
of `(1-2m)/(6κ)`. -/

namespace OAI.SevenEighths.Cycle25DetectorRawFiber
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open HeckeDetectorCoefficientTransfer
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDetectorPlainFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The marked plain moment at the affine capacity, in the affine window. -/
def AffineMarkedMoment836 (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (C height εm : ℝ) : Prop := ∀ selected : Finset Slot, selected ⊆ F.slots →
    41/100 ≤ F.m → F.m ≤ 44/100 →
    17/500 ≤ (∑ s∈selected, F.widths s) → (∑ s∈selected, F.widths s) ≤ 1/25 →
    2*F.m+Detector836.lam*(∑ s∈selected, F.widths s) ≤ Detector836.Bc →
    ∀ j k : ℕ, j+k ≤ 2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

/-- Count from the affine plain moment, supplemented below `17/500` by the
κ-marked moment. -/
theorem affine_marked_count836 (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c κinverse C height εm ν : ℝ} (moments : Moments F κplain c κinverse C height εm)
    (affine : AffineMarkedMoment836 F C height εm)
    (hU : 1 < U) (ha : 1/2 ≤ a) (hk : 7/10 ≤ κplain) (hk1 : κplain ≤ 3/4)
    (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1/100)
    (hmlo : Detector836.mLo ≤ F.m) (hmhi : F.m ≤ Detector836.mHi) :
    (F.rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(1-2*(2*a-1)*F.m-2*F.q*((Detector836.Bc-2*F.m)/Detector836.lam-ν)+
        4*ε+(2*a-1)*F.mesh+εm) := by
  set z := (Detector836.Bc-2*F.m)/Detector836.lam-ν with hzdef
  have hl := Detector836.lam_pos
  have hlo := Detector836.mLo_gt
  have hm2 : F.m < 1/2 := by unfold Detector836.mHi at hmhi; linarith
  -- capacity bounds
  have hzA : (Detector836.Bc-2*F.m)/Detector836.lam ≤ 1/25 := by
    rw [div_le_iff₀ hl]
    unfold Detector836.mLo at hmlo
    linarith
  have hzA' : 17/500 ≤ (Detector836.Bc-2*F.m)/Detector836.lam-1/1000 := by
    rw [sub_eq_add_neg, ← sub_eq_add_neg, le_sub_iff_add_le, le_div_iff₀ hl]
    unfold Detector836.mHi at hmhi
    unfold Detector836.Bc Detector836.lam
    linarith
  have hz : 0 ≤ z := by linarith
  have hz' : z ≤ 7/37 := by linarith
  have hzpos : 0 < z := by linarith
  set κ' := (1-2*F.m)/(6*z) with hκ'
  have hκ'0 : 0 ≤ κ' := div_nonneg (by linarith) (by positivity)
  have hcap : 2*F.m+6*κ'*z ≤ 1 := by
    have hz0 : z ≠ 0 := hzpos.ne'
    have e : 6*κ'*z = 1-2*F.m := by
      rw [hκ']; field_simp
    linarith
  have hraw : ∀ selected : Finset Slot, selected ⊆ F.slots →
      2*F.m+6*κ'*(∑ s∈selected, F.widths s) ≤ 1 →
      ∀ j k : ℕ, j+k ≤ 2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-height) height,
        ∑ u∈F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
          polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
            F.physicalProduct selected u‖^2 ≤ C*U^(1+εm) := by
    intro selected hsel hcap'
    have hw0 : 0 ≤ ∑ s∈selected, F.widths s :=
      Finset.sum_nonneg (fun s hs => (F.widths_pos s (hsel hs)).le)
    -- 6κ' = (1-2m)/z, so the cap says the selected width is at most z
    have hsum : (∑ s∈selected, F.widths s) ≤ z := by
      have hz0 : z ≠ 0 := hzpos.ne'
      have e : 6*κ' = (1-2*F.m)/z := by
        rw [hκ']; field_simp
      have h1 : (1-2*F.m)/z*(∑ s∈selected, F.widths s) ≤ 1-2*F.m := by
        rw [← e]; linarith
      have hpos : 0 < 1-2*F.m := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hzpos] at h1
      nlinarith
    by_cases hsmall : (∑ s∈selected, F.widths s) < 17/500
    · apply moments.plain_marked selected hsel
      have := mul_le_mul_of_nonneg_left hsmall.le (show (0:ℝ) ≤ 6*κplain by linarith)
      have h6 : 6*κplain*(17/500) ≤ 6*(3/4)*(17/500) := by nlinarith
      unfold Detector836.mHi at hmhi
      linarith
    · have hge : 17/500 ≤ ∑ s∈selected, F.widths s := le_of_not_gt hsmall
      apply affine selected hsel (by linarith) (by unfold Detector836.mHi at hmhi; linarith)
        hge (by linarith)
      have h2 : Detector836.lam*(∑ s∈selected, F.widths s) ≤ Detector836.lam*z :=
        mul_le_mul_of_nonneg_left hsum hl.le
      have h3 : Detector836.lam*z ≤ Detector836.Bc-2*F.m := by
        rw [hzdef, mul_sub, mul_div_cancel₀ _ hl.ne']
        nlinarith
      linarith
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z κ' εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hκ'0 hC hh hf hcap hraw

end
end OAI.SevenEighths.Cycle25DetectorRawFiber

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Detector836Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber Cycle25DetectorBranchBudget
open Cycle25DetectorRawFiber
open Cycle25DetectorRowCount

/-- The Cycle25 fiber count and the affine fiber count, for one common choice
of inverse-moment parameters. The affine cutoff `tstar` is free; the four
region hypotheses are the admissibility conditions of the new crossing. -/
theorem count_from_raw_moments_both836
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
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      1≤tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      23/37 ≤ Detector836.rN (F.q/(2*a-1)) tstar →
      Detector836.rN (F.q/(2*a-1)) tstar ≤ 1 →
      Detector836.mLo+1/100000 ≤ tstar-Detector836.rN (F.q/(2*a-1)) tstar →
      Detector836.oldPlainExp (2*a-1) (F.q/(2*a-1)) κplain Detector836.mHi ≤
        Detector836.shortNew (2*a-1) (F.q/(2*a-1)) tstar →
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      AffineMarkedMoment836 F C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (Detector836.shortNew (2*a-1) (F.q/(2*a-1)) tstar)
            (Detector836.longExp (2*a-1) tstar)+
          159*ε+εm+F.mesh+7*ν)) := by
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
    have hP : F.r≤crossing x κplain tstar → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
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
  · intro a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hν1 hC hh hf
      Label Slot F hrN hrN1 hmN htail moments affine
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
          U^(Detector836.inverseExp δ x F.r+commonLoss ε εm F.mesh ν) := by
      intro hr hr1 hv
      obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
      have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
      apply promote _ _ _ hconstI hb
      have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rw [hqx] at hl
      simpa only [Detector836.inverseExp, inverseExponent] using hl
    have hA : Detector836.mLo ≤ F.m → F.m ≤ Detector836.mHi →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(Detector836.affineExp δ x F.m+2*(δ*x)*ν+commonLoss ε εm F.mesh ν) := by
      intro hm1 hm2
      have hb := affine_marked_count836 F moments affine hU ha' hk hk1 hC hh hf hν.le hν1 hm1 hm2
      apply promote _ _ _ hconstP hb
      rw [← hqx]
      have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
      unfold Detector836.affineExp commonLoss
      have e : 2*(δ*x)*((Detector836.Bc-2*F.m)/Detector836.lam-ν) =
          2*(δ*x)*(Detector836.Bc-2*F.m)/Detector836.lam-2*(δ*x)*ν := by ring
      rw [e]
      linarith
    have hP : Detector836.mHi ≤ F.m → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(Detector836.oldPlainExp δ x κplain F.m+commonLoss ε εm F.mesh ν) := by
      intro hm hm2 hv
      have hd : 0<6*κplain := by linarith only [hk]
      have hmHi : (847/2000:ℝ) ≤ F.m := hm
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
      simpa only [hqx, Detector836.oldPlainExp] using hl
    have hc' := Detector836.affine_count_bound (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x
      κplain tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith)
      hx hx' hk hk1 hν.le hε hgeom.1 hgeom.2.1 hrN hrN1 (by linarith) htail hI0 hP0 hI hA hP
    convert hc' using 1; congr 2
    unfold commonLoss
    ring

end SevenEighths.Detector836Count
end
end OAI

#print axioms OAI.SevenEighths.Cycle25DetectorRawFiber.affine_marked_count836
#print axioms OAI.SevenEighths.Detector836Count.count_from_raw_moments_both836
