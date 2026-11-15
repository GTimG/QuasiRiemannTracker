/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Identify the rational certificate's branch prices with the actual finite count.
The old count is evaluated at the new kappa; native and marked windows retain
all their admission conditions. Uses Sil's and Collet's count identities. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ReturnData

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorContinuum.RationalReturn.ReturnQ
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss
open Set QRH.ArviReturnTuning QRH.ArviReturnTuning.Q2
open QRH.PositiveGap.ReturnTuning (ev_Jq ev_Nq cast_toQ)
local instance : Affine.Return.ImprovedCountScheme rationalLine := scheme

def envelope (δ p : ℝ) : ℝ :=
  Affine.Return.ImprovedCount.envelope (line := rationalLine) (kappaQ:ℝ) δ p

theorem denominator_checked (b : Code) : bernCheck (J b) 0 (3/4) 0 (1/2) = true := by
  cases b <;> decide +kernel

theorem denominator_pos (b : Code) {δ p : ℝ}
    (hd : δ ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    0 < Q2.ev (J b) δ p :=
  bernCheck_sound _ _ _ _ _ (denominator_checked b) (by simpa using hd.1)
    (by simpa using hd.2) (by simpa using hp.1) (by simpa using hp.2)

def oldDr (p : ℝ) : ℝ := 3-p-2*p/(3*(kappaQ:ℝ))
def oldCr (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*(kappaQ:ℝ)))
def oldJr (δ p : ℝ) : ℝ := (5/6-δ)*oldDr p+δ*oldCr p
def oldNr (δ p : ℝ) : ℝ := (1-δ)*oldJr δ p+δ*oldCr p*(5/6-δ)/2

theorem ev_oldD (δ p : ℝ) : Q2.ev oldD δ p = oldDr p := by
  simp only [oldD,ev_sub,ev_smul,ev_C,ev_Y]
  push_cast
  unfold oldDr
  ring

theorem ev_oldC (δ p : ℝ) : Q2.ev oldC δ p = oldCr p := by
  simp only [oldC,ev_mul,ev_sub,ev_smul,ev_C,ev_Y]
  push_cast
  unfold oldCr
  ring

theorem ev_oldJ (δ p : ℝ) : Q2.ev oldJ δ p = oldJr δ p := by
  simp only [oldJ,ev_add,ev_mul,ev_X,ev_oldD,ev_oldC,
    QRH.PositiveGap.ReturnTuning.ev_Vq]
  rfl

theorem ev_oldN (δ p : ℝ) : Q2.ev oldN δ p = oldNr δ p := by
  simp only [oldN,ev_add,ev_mul,ev_sub,ev_smul,ev_C,ev_X,ev_oldJ,ev_oldC,
    QRH.PositiveGap.ReturnTuning.ev_Vq]
  push_cast
  unfold oldNr QRH.PositiveGap.Return.V
  ring

theorem old_count_eq {δ p : ℝ}
    (hd : δ ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    QRH.Record12518109Return.countingR (kappaQ:ℝ) δ p =
      Q2.ev (N .old) δ p / Q2.ev (J .old) δ p := by
  have hk : (7/10:ℝ) ≤ (kappaQ:ℝ) := by norm_num [kappaQ,thetaQ]
  have hD : 0 < oldDr p := by
    norm_num [oldDr,kappaQ,thetaQ]
    nlinarith [hp.2]
  have hJ : 0 < oldJr δ p := by
    simpa only [J,ev_oldJ] using denominator_pos .old hd hp
  simp only [N,J,ev_oldN,ev_oldJ]
  unfold QRH.Record12518109Return.countingR QRH.Record12518109Return.rowDen
  rw [QRH.Record12518109Return.canonical_counting_formula hk]
  change 1-δ+δ*(oldCr p/oldDr p)*(5/6-δ)/
    (2*((5/6-δ)+δ*(oldCr p/oldDr p))) = oldNr δ p/oldJr δ p
  have he : (5/6-δ)+δ*(oldCr p/oldDr p) = oldJr δ p/oldDr p := by
    unfold oldJr
    field_simp [hD.ne']
    <;> ring
  rw [he]
  unfold oldNr
  field_simp [hD.ne',hJ.ne']
  <;> ring

theorem native_ratio (δ p : ℝ) :
    Q2.ev (N .native) δ p / Q2.ev (J .native) δ p =
      QRH.PositiveGap.Return.branchCount .C δ p := by
  obtain ⟨hB,hL,hCap,hBool⟩ := cast_toQ .C (by decide)
  simp only [N,J,ev_Jq,ev_Nq]
  rw [hB,hL,hCap,hBool,
    ←QRH.PositiveGap.ReturnTuning.countJ_eq δ p .C (by decide),
    ←QRH.PositiveGap.ReturnTuning.countN_eq δ p .C (by decide)]
  rfl

theorem envelope_le_native (w : QRH.PositiveGap.ReturnTuning.WinQ)
    (hw : w ∈ nativeQ) (hb : w.branch = .C) {δ p : ℝ}
    (hd : δ ∈ Icc (w.dlo:ℝ) w.dhi) (hp : p ∈ Icc (w.plo:ℝ) (1/2)) :
    envelope δ p ≤ QRH.PositiveGap.Return.branchCount .C δ p := by
  let v := QRH.PositiveGap.ReturnTuning.mkWindow 0 w
    (QRH.PositiveGap.ReturnTuning.ok_of_mem native_ok hw)
  have hm : QRH.PositiveGap.Return.Tuning.ReturnCountWindow.toAdmitted v ∈ scheme.windows :=
    List.mem_map.mpr ⟨v,QRH.PositiveGap.ReturnTuning.mkWindow_mem native_ok hw,rfl⟩
  have ha : (QRH.PositiveGap.Return.Tuning.ReturnCountWindow.toAdmitted v).Available δ p := ⟨hd,hp⟩
  have h := Affine.Return.ImprovedCount.envelope_le_window (line := rationalLine)
    (S := scheme) hm (κ := (kappaQ:ℝ)) ha
  change envelope δ p ≤ QRH.PositiveGap.Return.branchCount w.branch δ p at h
  simpa only [hb] using h

theorem cell_intervals (s : Cell) {lo hi pl ph : ℚ} {δ p : ℝ}
    (hlo : lo ≤ s.dlo) (hhi : s.dhi ≤ hi) (hpl : pl ≤ s.plo) (hph : s.phi ≤ ph)
    (hd0 : (s.dlo:ℝ) ≤ δ) (hd1 : δ ≤ s.dhi)
    (hp0 : (s.plo:ℝ) ≤ p) (hp1 : p ≤ s.phi) :
    δ ∈ Icc (lo:ℝ) hi ∧ p ∈ Icc (pl:ℝ) ph :=
  ⟨⟨(Rat.cast_le.mpr hlo).trans hd0,hd1.trans (Rat.cast_le.mpr hhi)⟩,
    ⟨(Rat.cast_le.mpr hpl).trans hp0,hp1.trans (Rat.cast_le.mpr hph)⟩⟩

/-- Every admitted certificate cell uses a count supplied by the actual finite
scheme; no branch is selected solely because its numerical value is smaller. -/
theorem envelope_le_cell (s : Cell) (hs : s.ok = true) {δ p : ℝ}
    (hd : δ ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2))
    (hd0 : (s.dlo:ℝ) ≤ δ) (hd1 : δ ≤ s.dhi)
    (hp0 : (s.plo:ℝ) ≤ p) (hp1 : p ≤ s.phi) :
    envelope δ p ≤ Q2.ev (N s.code) δ p / Q2.ev (J s.code) δ p := by
  have had : s.admitted := by
    have h := hs
    simp only [Cell.ok,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  cases hc : s.code with
  | old =>
      exact (Affine.Return.ImprovedCount.envelope_le_base (line := rationalLine)
        (S := scheme) (kappaQ:ℝ) δ p).trans_eq (old_count_eq hd hp)
  | native =>
      simp only [Cell.admitted,hc] at had
      obtain ⟨hd',hp'⟩ := cell_intervals s had.1 had.2.1 had.2.2.1 had.2.2.2 hd0 hd1 hp0 hp1
      rw [native_ratio]
      apply envelope_le_native ⟨.C,15/64,9/16,9/32⟩ (by simp [nativeQ]) rfl
      · simpa using hd'
      · simpa using hp'
  | nativeLow =>
      simp only [Cell.admitted,hc] at had
      obtain ⟨hd',hp'⟩ := cell_intervals s had.1 had.2.1 had.2.2.1 had.2.2.2 hd0 hd1 hp0 hp1
      change envelope δ p ≤ Q2.ev (N .native) δ p / Q2.ev (J .native) δ p
      rw [native_ratio]
      apply envelope_le_native ⟨.C,15/64,1/2,3/16⟩ (by simp [nativeQ]) rfl
      · simpa using hd'
      · simpa using hp'
  | improved =>
      simp only [Cell.admitted,hc] at had
      obtain ⟨hd',hp'⟩ := cell_intervals s had.1 had.2.1 had.2.2.1 had.2.2.2 hd0 hd1 hp0 hp1
      have h := Affine.Return.ImprovedCount.envelope_le_improved (line := rationalLine)
        (S := scheme) (w := Affine.Return.ContinuumQ.window)
        (by change _ ∈ [_]; exact List.mem_singleton_self _) (κ := (kappaQ:ℝ))
        (show Affine.Return.ContinuumQ.window.Available δ p from ⟨by simpa [Affine.Return.ContinuumQ.window] using hd',
          by simpa [Affine.Return.ContinuumQ.window] using hp'⟩)
      change envelope δ p ≤ Affine.Return.ContinuumQ.valueI δ p at h
      simpa only [N,J,Affine.Return.ContinuumQ.ev_NQ,Affine.Return.ContinuumQ.ev_JQ,
        Affine.Return.ContinuumQ.valueI] using h

end
end Qrh.TwoSlot.AnchorContinuum.RationalReturn.ReturnQ
#print axioms Qrh.TwoSlot.AnchorContinuum.RationalReturn.ReturnQ.old_count_eq

#print axioms Qrh.TwoSlot.AnchorContinuum.RationalReturn.ReturnQ.envelope_le_cell
