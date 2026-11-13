/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Explicit-line detector fiber counts, adapted from Sil's PR137 ImprovedFiber
(copyright (c) 2026 Sil, Apache-2.0), retaining the native and improved
same-supported-witness split and Hailey Collet's count inputs (Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineScheme
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Return.ImprovedFiber

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Qrh.TwoSlot.AnchorZeroLoss.Affine.Return
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths QRH.Record12518109Count QRH.Record1252270103Return
open Qrh.MarkedAnchor.Interface (anchorLeft anchorTop)
open Qrh.MarkedAnchor.Return (inverse_fiber_count_le fiber_inverse_width_count
  fiber_ordinary_width_count improved_witness_count_bound)
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber Cycle25DetectorBranchBudget
open Cycle25DetectorRawFiber Cycle25DetectorRowCount
open HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial

variable {line : Line} [CapacityBounds line]

theorem markCap_bounds {w ν : ℝ} (h1 : anchorLeft ≤ w) (h2 : w ≤ anchorTop)
    (hν : 0 < ν) (hν1 : ν ≤ 1/10000000) :
    0 < markCap line w-ν ∧ markCap line w-ν ≤ 7/37 := by
  obtain ⟨hlo,hhi⟩ := CapacityBounds.bounds (line := line) w h1 h2
  constructor <;> linarith

/-- **Fiber counts at native and improved windows** from one inverse amplifier. -/
theorem count_fiber_at_windows
    (M:Ideal O) [NeZero M] (H:Subgroup (O⧸M)ˣ)
    (hH:RayOrthogonality.globalUnits M≤H) (S:Finset (Ideal O))
    (φ:ℝ→ℝ) (hφ:ContDiff ℝ ∞ φ) (hφc:HasCompactSupport φ)
    (hφp:tsupport φ⊆Ioi 0) (hφ0:∀y,0≤φ y) (hφne:φ≠0)
    (a₀ b₀ B₀:ℝ) (ha₀:0<a₀) (hab₀:a₀≤b₀) (hB₀:0<B₀)
    (hφs:Function.support φ⊆Ioo a₀ b₀) (hφB:∀y,φ y≤B₀)
    (εm:ℝ) (hεm:0<εm) :
    ∃c κ K₀:ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU:ℝ in atTop,
    (∀naturalκ:ℝ,7/10≤naturalκ → naturalκ≤3/4 →
    ∀w:AdmittedWindow naturalκ,∀(a ε tstar T allowance ν C height:ℝ) (i:ℕ),
    1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
    0<ν → ν≤1/10000000 → 0≤C → 0≤height →
    2*Real.pi*allowance+(3*i:ℕ)*T≤height →
    ∀{Label Slot:Type} (F:Fiber M H Label Slot U a ε tstar T allowance i),
    w.Available (2*a-1) (F.q/(2*a-1)) →
    tstar=w.cutoff (2*a-1) (F.q/(2*a-1)) →
    Cycle25DetectorRawFiber.Moments F naturalκ c κ C height εm →
    AffineMarkedMoment F w.face C height εm →
    (F.rows.card:ℝ)≤fiberConstant C height K₀*
      U^(w.value (2*a-1) (F.q/(2*a-1))+159*ε+εm+F.mesh+7*ν)) ∧
    (∀naturalκ:ℝ,7/10≤naturalκ → naturalκ≤3/4 →
    ∀w:ImprovedWindow line naturalκ,∀(a ε tstar T allowance ν C height:ℝ) (i:ℕ),
    1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/10000000 →
    0<ν → ν≤1/10000000 → 0≤C → 0≤height →
    2*Real.pi*allowance+(3*i:ℕ)*T≤height →
    ∀{Label Slot:Type} (F:Fiber M H Label Slot U a ε tstar T allowance i),
    w.Available (2*a-1) (F.q/(2*a-1)) →
    tstar=w.cutoff (2*a-1) (F.q/(2*a-1)) →
    Cycle25DetectorRawFiber.Moments F naturalκ c κ C height εm →
    AffineMarkedMoment F w.face C height εm →
    ImprovedMoments line F ν C height εm →
    (F.rows.card:ℝ)≤fiberConstant C height K₀*
      U^(w.value (2*a-1) (F.q/(2*a-1))+159*ε+εm+F.mesh+7*ν)) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  constructor
  · -- the native window: Collet's `count_from_piecewise_moments` at the window's crossing
    intro naturalκ hk hk1 w a ε tstar T allowance ν C height i hU ha hδhi hε hεhi hν hνhi hC hh hf
      Label Slot F hg ht moments affine
    let δ := 2*a-1
    let x := F.q/δ
    have ht1 : 1≤tstar := by rw [ht]; exact (w.cutoff_bounds hg.1 hg.2).1
    have hδ : 0<δ := by dsimp [δ]; linarith
    have ha' : 1/2≤a := by linarith
    have hδ1 : δ≤1 := by dsimp [δ]; linarith
    obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
    have hx : 0≤x := div_nonneg hq0 hδ.le
    have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
    have hqx : δ*x=F.q := by dsimp [x]; field_simp
    have hgeom := F.lengths hU
    have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
    have hr2 : F.r≤2 := by linarith [hgeom.2.1, (w.cutoff_bounds hg.1 hg.2).2, ht]
    have hUp : 0<U := zero_lt_one.trans hU
    obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
    have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
        (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
        (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
      exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
    have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
      (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
      F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff
      moments.original.inverse_raw
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
      have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz'
        hcap1 hcap2
      apply promote _ _ _ hconstI hb
      have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rw [hqx] at hl
      simpa only [Parameters.inverseExp, inverseExponent] using hl
    have hA : w.mLo≤F.m → F.m≤w.mHi →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(plainCurve w.B w.lam w.cap δ x F.m+2*(δ*x)*ν+commonLoss ε εm F.mesh ν) := by
      intro hm1 hm2
      have hm0 : 0≤F.m := w.mLo_nonneg.trans hm1
      have hb := piecewise_marked_count F moments affine hU (by linarith) (by linarith) hC hh hf
        (hm2.trans_lt w.mHi_hi) hm0 (by linarith [w.lam_gt_one]) hν.le
        (w.widths hg.1 hg.2 ν hνhi F.m hm1 hm2) w.cap_le_source w.cap_small
      change (F.rows.card:ℝ)≤192*(1+height)*C*
        U^(plainCurve w.B w.lam w.cap δ x F.m+2*F.q*ν+4*ε+δ*F.mesh+εm) at hb
      apply promote _ _ _ hconstP hb
      rw [←hqx]
      have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
      unfold commonLoss
      linarith
    have hP : w.mHi≤F.m → F.m<1/2 → ν<(1-2*F.m)/(6*naturalκ) →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^((1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*naturalκ))+commonLoss ε εm F.mesh ν) := by
      intro hm hm2 hv
      have hd : 0<6*naturalκ := by linarith only [hk]
      have hmHi : (2/5:ℝ)≤F.m := w.mHi_lo.trans hm
      have hc5 : (1-2*F.m)/(6*naturalκ)≤5/42 := by
        rw [div_le_iff₀ hd]; linarith only [hmHi, hk]
      have hz : 0≤(1-2*F.m)/(6*naturalκ)-ν := by linarith only [hv]
      have hz' : (1-2*F.m)/(6*naturalκ)-ν≤7/37 := by linarith only [hc5, hν]
      have hκν : 0≤6*naturalκ*ν := mul_nonneg hd.le hν.le
      have hcap : 2*F.m+6*naturalκ*((1-2*F.m)/(6*naturalκ)-ν)≤1 := by
        rw [mul_sub,mul_div_cancel₀ _ hd.ne']
        linarith only [hκν]
      have hb := Cycle25DetectorRawFiber.plain_marked_count F moments hU ha'
        (by linarith only [hk]) hC hh hf ((1-2*F.m)/(6*naturalκ)-ν) hz hz' hcap
      apply promote _ _ _ hconstP hb
      have hl := plain_marked_loss F.m δ x naturalκ ε εm F.mesh ν hδ.le hδ1 hx hx' hε
        F.mesh_nonneg hν.le
      simpa only [hqx, Parameters.oldPlainExp] using hl
    have hc' := common_witness_count_bound (F.rows.card:ℝ) (fiberConstant C height K₀) U δ x
      naturalκ tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε (w.crossing δ x) (w.value δ x)
      w.mLo w.mHi (plainCurve w.B w.lam w.cap δ x)
      (fun u v h=>plainCurve_antitone w.lam_gt_one hδ.le hx hx' h)
      (fun u g hg=>plainCurve_shift w.lam_gt_one hδ.le hδ1 hx hx' hg)
      (by simpa only [ht] using w.plain_crossing hg.1 hg.2) hconst hU.le hδ.le
      (by dsimp [δ]; linarith) hx hx' hk hk1 hν.le hε
      hgeom.1 hgeom.2.1 (w.inverse_bounds hg.1 hg.2).1 (w.inverse_bounds hg.1 hg.2).2
      (by rw [ht]; linarith [w.plain_buffer hg.1 hg.2]) (w.inverse_crossing hg.1 hg.2)
      (w.natural_tail hg.1 hg.2) hI0 hP0 hI hA hP
    have hlong : 1-δ+(5/6-δ)*(tstar-1)=w.value δ x := by
      have htx' : tstar=w.cutoff δ x := ht
      rw [htx']; exact w.long_crossing hg.1 hg.2
    rw [hlong,max_self] at hc'
    have hval : w.value (2*a-1) (F.q/(2*a-1))=w.value δ x := rfl
    rw [hval]
    refine hc'.trans_eq ?_
    congr 2
    unfold commonLoss
    ring
  · -- the improved window
    intro naturalκ hk hk1 w a ε tstar T allowance ν C height i hU ha hδhi hε hεhi hν hνhi hC hh hf
      Label Slot F hg ht moments affine imp
    let δ := 2*a-1
    let x := F.q/δ
    have ht1 : 1≤tstar := by rw [ht]; exact (w.cutoff_bounds hg.1 hg.2).1
    have hδ : 0<δ := by dsimp [δ]; linarith
    have ha' : 1/2≤a := by linarith
    have hδ1 : δ≤1 := by dsimp [δ]; linarith
    obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
    have hx : 0≤x := div_nonneg hq0 hδ.le
    have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
    have hqx : δ*x=F.q := by dsimp [x]; field_simp
    have hq : 2*(δ*x)≤1 := by nlinarith [mul_le_mul hδ1 hx' hx (by norm_num : (0:ℝ)≤1)]
    have hgeom := F.lengths hU
    have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
    have hr2 : F.r≤2 := by linarith [hgeom.2.1, (w.cutoff_bounds hg.1 hg.2).2, ht]
    have hUp : 0<U := zero_lt_one.trans hU
    obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
    have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
        (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
        (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
      exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
    have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
      (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
      F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff
      moments.original.inverse_raw
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
      have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz'
        hcap1 hcap2
      apply promote _ _ _ hconstI hb
      have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rw [hqx] at hl
      simpa only [Parameters.inverseExp, inverseExponent] using hl
    have hJ : anchorLeft≤F.r → F.r≤anchorTop →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^((1-δ*(x*(1+2*line.g0)+(1-x*(1+2*line.g1))*F.r))+commonLoss ε εm F.mesh ν) := by
      intro h1 h2
      obtain ⟨hz,hz'⟩ := markCap_bounds (line := line) h1 h2 hν hνhi
      have hb : (F.rows.card : ℝ)≤(12*(1+height)*C)*
          U^(1-δ*F.r-2*F.q*(markCap line F.r-ν)+2*ε+δ*F.mesh+εm) :=
        fiber_inverse_width_count F hU ha' hC hh hf (markCap line F.r-ν) hz.le hz'
          (fun sel hsel hw => imp.inverse h1 h2 sel hsel hw)
      apply promote _ _ _ hconstI hb
      rw [←hqx]
      have hn := mul_le_mul_of_nonneg_right hq hν.le
      have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
      have key : 1-δ*F.r-2*(δ*x)*(markCap line F.r-ν)+2*ε+δ*F.mesh+εm=
          (1-δ*(x*(1+2*line.g0)+(1-x*(1+2*line.g1))*F.r))+2*(δ*x)*ν+2*ε+δ*F.mesh+εm := by
        unfold markCap; ring
      rw [key]
      unfold commonLoss
      linarith
    have hO : anchorLeft≤2*F.m → 2*F.m≤anchorTop →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^((1-δ*(x*(1+2*line.g0)+2*F.m*(1-x*(1+2*line.g1))))+commonLoss ε εm F.mesh ν) := by
      intro h1 h2
      obtain ⟨hz,hz'⟩ := markCap_bounds (line := line) h1 h2 hν hνhi
      have hmhalf : F.m<1/2 := by unfold anchorTop at h2; linarith
      have hb : (F.rows.card : ℝ)≤(192*(1+height)*C)*
          U^(1-2*δ*F.m-2*F.q*(markCap line (2*F.m)-ν)+4*ε+δ*F.mesh+εm) :=
        fiber_ordinary_width_count F hU ha' hC hh hf hmhalf hz hz'
          (fun sel hsel hw => imp.ordinary h1 h2 sel hsel hw)
      apply promote _ _ _ hconstP hb
      rw [←hqx]
      have hn := mul_le_mul_of_nonneg_right hq hν.le
      have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
      have key : 1-2*δ*F.m-2*(δ*x)*(markCap line (2*F.m)-ν)+4*ε+δ*F.mesh+εm=
          (1-δ*(x*(1+2*line.g0)+2*F.m*(1-x*(1+2*line.g1))))+2*(δ*x)*ν+4*ε+δ*F.mesh+εm := by
        unfold markCap; ring
      rw [key]
      unfold commonLoss
      linarith
    have hA : anchorTop/2≤F.m → F.m≤w.mHi →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(plainCurve w.B w.lam w.cap δ x F.m+2*(δ*x)*ν+commonLoss ε εm F.mesh ν) := by
      intro hm1 hm2
      have hm0 : 0≤F.m := le_trans (by unfold anchorTop; norm_num) hm1
      have hb := piecewise_marked_count F moments affine hU (by linarith) (by linarith) hC hh hf
        (hm2.trans_lt w.mHi_hi) hm0 (by linarith [w.lam_gt_one]) hν.le
        (w.widths ν hνhi F.m hm1 hm2) w.cap_le_source w.cap_small
      change (F.rows.card:ℝ)≤192*(1+height)*C*
        U^(plainCurve w.B w.lam w.cap δ x F.m+2*F.q*ν+4*ε+δ*F.mesh+εm) at hb
      apply promote _ _ _ hconstP hb
      rw [←hqx]
      have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
      unfold commonLoss
      linarith
    have hP : w.mHi≤F.m → F.m<1/2 → ν<(1-2*F.m)/(6*naturalκ) →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^((1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*naturalκ))+commonLoss ε εm F.mesh ν) := by
      intro hm hm2 hv
      have hd : 0<6*naturalκ := by linarith only [hk]
      have hmHi : (2/5:ℝ)≤F.m := w.mHi_lo.trans hm
      have hc5 : (1-2*F.m)/(6*naturalκ)≤5/42 := by
        rw [div_le_iff₀ hd]; linarith only [hmHi, hk]
      have hz : 0≤(1-2*F.m)/(6*naturalκ)-ν := by linarith only [hv]
      have hz' : (1-2*F.m)/(6*naturalκ)-ν≤7/37 := by linarith only [hc5, hν]
      have hκν : 0≤6*naturalκ*ν := mul_nonneg hd.le hν.le
      have hcap : 2*F.m+6*naturalκ*((1-2*F.m)/(6*naturalκ)-ν)≤1 := by
        rw [mul_sub,mul_div_cancel₀ _ hd.ne']
        linarith only [hκν]
      have hb := Cycle25DetectorRawFiber.plain_marked_count F moments hU ha'
        (by linarith only [hk]) hC hh hf ((1-2*F.m)/(6*naturalκ)-ν) hz hz' hcap
      apply promote _ _ _ hconstP hb
      have hl := plain_marked_loss F.m δ x naturalκ ε εm F.mesh ν hδ.le hδ1 hx hx' hε
        F.mesh_nonneg hν.le
      simpa only [hqx, Parameters.oldPlainExp] using hl
    have hk1' : 1-x*(1+2*line.g1)≤1 := by
      have : 0≤x*(1+2*line.g1) := mul_nonneg hx (by linarith [line.slope_nonneg])
      linarith
    have htx : tstar=w.cutoff δ x := ht
    have hpl : anchorLeft+1/1000000≤2*(w.cutoff δ x-w.crossing δ x) := w.plain_left hg.1 hg.2
    have hplainL : anchorLeft≤2*(tstar-w.crossing δ x-ε) := by
      rw [htx]; linarith
    have hord : 1-δ*(x*(1+2*line.g0)+2*(tstar-w.crossing δ x)*(1-x*(1+2*line.g1)))≤w.value δ x := by
      rw [htx]; exact w.ordinary_crossing hg.1 hg.2
    have hc' := improved_witness_count_bound (F.rows.card:ℝ) (fiberConstant C height K₀) U δ x
      naturalκ tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε (w.crossing δ x) (w.value δ x)
      w.mHi anchorLeft anchorTop (x*(1+2*line.g0)) (1-x*(1+2*line.g1))
      (plainCurve w.B w.lam w.cap δ x)
      (fun u v h=>plainCurve_antitone w.lam_gt_one hδ.le hx hx' h)
      (w.plain_top hg.1 hg.2) hconst hU.le hδ.le (by dsimp [δ]; linarith) hx hx' hk hk1 hν.le hε
      hgeom.1 hgeom.2.1 (by unfold anchorTop; norm_num) (by unfold anchorTop; norm_num)
      (w.slope_nonneg hg.1 hg.2) hk1' (w.crossing_left hg.1 hg.2) hplainL
      (w.inverse_crossing hg.1 hg.2) hord (w.native_top hg.1 hg.2) (w.natural_tail hg.1 hg.2)
      hI0 hP0 hI hJ hO hA hP
    have hlong : 1-δ+(5/6-δ)*(tstar-1)=w.value δ x := by
      have htx' : tstar=w.cutoff δ x := ht
      rw [htx']; exact w.long_crossing hg.1 hg.2
    rw [hlong,max_self] at hc'
    have hval : w.value (2*a-1) (F.q/(2*a-1))=w.value δ x := rfl
    rw [hval]
    refine hc'.trans_eq ?_
    congr 2
    unfold commonLoss
    ring

end
end Qrh.TwoSlot.AnchorZeroLoss.Affine.Return
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.count_fiber_at_windows
