/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Transport the exact edge-cover prices to the genuine admitted count envelope.
Retains the old-count conductor, native windows and exact marked window. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactReturnCover

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set IntervalPolynomial IntervalPolynomial.P2
open QRH.ArviReturnTuning
open Qrh.TwoSlot.AnchorZeroLoss
local instance : Affine.Return.ImprovedCountScheme exactLine := exactScheme

def kappa : ℝ := 2*theta-1
def envelope (d p : ℝ) : ℝ :=
  Affine.Return.ImprovedCount.envelope (line := exactLine) kappa d p
def oldDr (p : ℝ) : ℝ := 3-p-2*p/(3*kappa)
def oldCr (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappa))
def oldJr (d p : ℝ) : ℝ := (5/6-d)*oldDr p+d*oldCr p
def oldNr (d p : ℝ) : ℝ := (1-d)*oldJr d p+d*oldCr p*(5/6-d)/2

theorem kappa_bounds : (7/10:ℝ) ≤ kappa ∧ kappa < 3/4 := by
  have ht := theta_range
  unfold kappa
  constructor <;> linarith [ht.1,ht.2]

theorem ev_oldD (d p : ℝ) : ev oldD d p = oldDr p := by
  simp only [oldD,ev_sub,ev_C,ev_Y,ev_smul]
  dsimp [R,Coeff.rat,Coeff.div,k3,kappaC,Coeff.mul,Coeff.sub,Coeff.add,Coeff.neg,thetaC]
  norm_num
  unfold oldDr kappa
  ring

theorem ev_oldC (d p : ℝ) : ev oldC d p = oldCr p := by
  simp only [oldC,ev_mul,ev_sub,ev_C,ev_Y,ev_smul]
  dsimp [R,Coeff.rat,Coeff.div,k3,kappaC,Coeff.mul,Coeff.sub,Coeff.add,Coeff.neg,thetaC]
  norm_num
  unfold oldCr kappa
  have ht := theta_range.1
  have h1 : -1+theta*2 ≠ 0 := by linarith
  have h3 : -3+theta*6 ≠ 0 := by linarith
  ring_nf
  field_simp [h1,h3]
  ring_nf
  field_simp [h1,h3]
  ring

theorem ev_oldJ (d p : ℝ) : ev oldJ d p = oldJr d p := by
  simp only [oldJ,V,ev_add,ev_mul,ev_sub,ev_C,ev_X,ev_oldD,ev_oldC]
  norm_num [R,Coeff.rat]
  rfl

theorem ev_oldN (d p : ℝ) : ev oldN d p = oldNr d p := by
  simp only [oldN,V,ev_add,ev_mul,ev_sub,ev_C,ev_X,ev_smul,ev_oldJ,ev_oldC]
  norm_num [R,Coeff.rat]
  unfold oldNr
  ring

theorem old_factors_positive {p : ℝ} (hp : p ∈ Icc (0:ℝ) (1/2)) :
    0 < oldDr p ∧ 0 ≤ oldCr p := by
  have hk := kappa_bounds.1
  have hden : 0 < 3*kappa := by linarith
  have hfrac : p/(3*kappa) ≤ (1/4:ℝ) := (div_le_iff₀ hden).mpr (by linarith [hp.2])
  have hfrac0 : 0 ≤ p/(3*kappa) := div_nonneg hp.1 hden.le
  constructor
  · unfold oldDr
    have he : 2*p/(3*kappa) = 2*(p/(3*kappa)) := by ring
    rw [he]
    linarith [hp.2]
  · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [hp.2])) (by linarith)

theorem denominator_pos (b : Code) {d p : ℝ}
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) : 0 < ev (J b) d p := by
  cases b with
  | old =>
    rw [J,ev_oldJ]
    have hf := old_factors_positive hp
    have hm := mul_nonneg hd.1 hf.2
    have hv : 0 < (5/6:ℝ)-d := by linarith [hd.2]
    unfold oldJr
    exact add_pos_of_pos_of_nonneg (mul_pos hv hf.1) hm
  | native =>
    simpa only [J,ev_lift,RationalReturn.ReturnQ.J] using RationalReturn.ReturnQ.denominator_pos .native hd hp
  | nativeLow =>
    simpa only [J,ev_lift,RationalReturn.ReturnQ.J] using RationalReturn.ReturnQ.denominator_pos .native hd hp
  | improved =>
    rw [J,ev_markedJ]
    have ha0 : 0 ≤ 1+2*exactLine.g1 := by linarith [exactLine.slope_nonneg]
    have ha1 : 1+2*exactLine.g1 ≤ 2 := by linarith [exactLine.slope_le]
    have hm := mul_le_mul hp.2 ha1 ha0 (by norm_num : (0:ℝ) ≤ 1/2)
    have hK : 0 ≤ Affine.Return.ExactWindow.kI p := by unfold Affine.Return.ExactWindow.kI; linarith
    have hM := mul_nonneg hd.1 hK
    unfold Affine.Return.ExactWindow.JI
    linarith [hd.2]

theorem old_count_eq {d p : ℝ} (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    QRH.Record12518109Return.countingR kappa d p = ev (N .old) d p/ev (J .old) d p := by
  have hD := (old_factors_positive hp).1
  have hJ : 0 < oldJr d p := by simpa only [J,ev_oldJ] using denominator_pos .old hd hp
  simp only [N,J,ev_oldN,ev_oldJ]
  unfold QRH.Record12518109Return.countingR QRH.Record12518109Return.rowDen
  rw [QRH.Record12518109Return.canonical_counting_formula kappa_bounds.1]
  change 1-d+d*(oldCr p/oldDr p)*(5/6-d)/
    (2*((5/6-d)+d*(oldCr p/oldDr p))) = oldNr d p/oldJr d p
  have he : (5/6-d)+d*(oldCr p/oldDr p) = oldJr d p/oldDr p := by
    unfold oldJr
    field_simp [hD.ne']
    <;> ring
  rw [he]
  unfold oldNr
  field_simp [hD.ne',hJ.ne']
  <;> ring

theorem native_ratio (d p : ℝ) : ev (N .native) d p/ev (J .native) d p =
    QRH.PositiveGap.Return.branchCount .C d p := by
  simpa only [N,J,ev_lift,RationalReturn.ReturnQ.N,RationalReturn.ReturnQ.J] using
    RationalReturn.ReturnQ.native_ratio d p

theorem envelope_le_native (w : QRH.PositiveGap.ReturnTuning.WinQ)
    (hw : w ∈ RationalReturn.nativeQ) (hb : w.branch = .C) {d p : ℝ}
    (hd : d ∈ Icc (w.dlo:ℝ) w.dhi) (hp : p ∈ Icc (w.plo:ℝ) (1/2)) :
    envelope d p ≤ QRH.PositiveGap.Return.branchCount .C d p := by
  let v := QRH.PositiveGap.ReturnTuning.mkWindow 0 w
    (QRH.PositiveGap.ReturnTuning.ok_of_mem RationalReturn.native_ok hw)
  have hm : QRH.PositiveGap.Return.Tuning.ReturnCountWindow.toAdmitted v ∈ exactScheme.windows :=
    List.mem_map.mpr ⟨v,QRH.PositiveGap.ReturnTuning.mkWindow_mem RationalReturn.native_ok hw,rfl⟩
  have ha : (QRH.PositiveGap.Return.Tuning.ReturnCountWindow.toAdmitted v).Available d p := ⟨hd,hp⟩
  have hh := Affine.Return.ImprovedCount.envelope_le_window (line := exactLine)
    (S := exactScheme) hm (κ := kappa) ha
  change envelope d p ≤ QRH.PositiveGap.Return.branchCount w.branch d p at hh
  simpa only [hb] using hh

theorem envelope_le_cell (i : Fin 57) {d p : ℝ}
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2))
    (hd0 : ((RationalReturn.ReturnQ.cells i).dlo:ℝ) ≤ d)
    (hd1 : d ≤ ((RationalReturn.ReturnQ.cells i).dhi:ℝ))
    (hp0 : ((RationalReturn.ReturnQ.cells i).plo:ℝ) ≤ p)
    (hp1 : p ≤ ((RationalReturn.ReturnQ.cells i).phi:ℝ)) :
    envelope d p ≤ ev (N (codeOf (RationalReturn.ReturnQ.cells i).code)) d p/
      ev (J (codeOf (RationalReturn.ReturnQ.cells i).code)) d p := by
  have had := cell_admitted i
  cases hc : (RationalReturn.ReturnQ.cells i).code with
  | old =>
    simpa only [envelope,hc,codeOf] using
      (Affine.Return.ImprovedCount.envelope_le_base (line := exactLine) (S := exactScheme) kappa d p).trans_eq (old_count_eq hd hp)
  | native =>
    simp only [RationalReturn.ReturnQ.Cell.admitted,hc] at had
    obtain ⟨hd',hp'⟩ := RationalReturn.ReturnQ.cell_intervals _
      had.1 had.2.1 had.2.2.1 had.2.2.2 hd0 hd1 hp0 hp1
    simp only [hc,codeOf]
    rw [native_ratio]
    exact envelope_le_native ⟨.C,15/64,9/16,9/32⟩ (by simp [RationalReturn.nativeQ]) rfl
      (by simpa using hd') (by simpa using hp')
  | nativeLow =>
    simp only [RationalReturn.ReturnQ.Cell.admitted,hc] at had
    obtain ⟨hd',hp'⟩ := RationalReturn.ReturnQ.cell_intervals _
      had.1 had.2.1 had.2.2.1 had.2.2.2 hd0 hd1 hp0 hp1
    change envelope d p ≤ ev (N .native) d p/ev (J .native) d p
    rw [native_ratio]
    exact envelope_le_native ⟨.C,15/64,1/2,3/16⟩ (by simp [RationalReturn.nativeQ]) rfl
      (by simpa using hd') (by simpa using hp')
  | improved =>
    simp only [RationalReturn.ReturnQ.Cell.admitted,hc] at had
    obtain ⟨hd',hp'⟩ := RationalReturn.ReturnQ.cell_intervals _
      had.1 had.2.1 had.2.2.1 had.2.2.2 hd0 hd1 hp0 hp1
    have hh := Affine.Return.ImprovedCount.envelope_le_improved (line := exactLine)
      (S := exactScheme) (w := Affine.Return.ExactWindow.window)
      (by change _ ∈ [_]; exact List.mem_singleton_self _) (κ := kappa)
      (show Affine.Return.ExactWindow.window.Available d p from
        ⟨by simpa [Affine.Return.ExactWindow.window] using hd',by simpa [Affine.Return.ExactWindow.window] using hp'⟩)
    change envelope d p ≤ Affine.Return.ExactWindow.valueI d p at hh
    simpa only [hc,codeOf,J,N,ev_markedJ,ev_markedN,Affine.Return.ExactWindow.valueI] using hh

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.envelope_le_cell
