/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.FamilyGates
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PairedStage

/-! A genuine paired source step along the strict curve, with a common
positive tolerance and step size chosen before the arithmetic data. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Set Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData

theorem curve_step (F : ParentFace)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    {lam T gamma q R r : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hT : 3/4 ≤ T) (hT1 : T < 7/9)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1/100)
    (hq : 0 < q) (hqu : q ≤ 1/1000000000000) (hqg : q ≤ gamma/1000)
    (hR : R ∈ Icc (3/4:ℝ) T) (hr : r ∈ Icc (3/4:ℝ) R)
    (hreserve : 3*gamma ≤ Curve.D lam T R-Curve.flow R (Curve.W lam T R))
    (hstep : R-r ≤ 1/10000)
    (hdom : Curve.W lam T r ≤ fY R (Curve.W lam T R) (Curve.cut lam T gamma R) r)
    (hprev : AnchorAt R (Curve.W lam T R))
    (hprior : ∀ x : ℝ, R < x → x ≤ T → AnchorAt x (Curve.W lam T x)) :
    AnchorAt r (Curve.W lam T r) := by
  letI : Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift := ⟨q,hq,hqu⟩
  obtain ⟨hS,htiny,hclasses⟩ := curve_stage_gates hlam hlam1 hT hT1.le hR hr
    hg hg1 hq hqu hqg hreserve hstep
  have hd := Curve.D_bounds hlam hlam1 hT hT1.le hR
  have hseed := Curve.W_seed lam (T:=T) (by linarith)
  have htangent : Curve.W lam T R+Curve.D lam T R*(T-R) ≤ 0 := by
    rcases lt_or_eq_of_le hR.2 with hlt | heq
    · have h := Curve.tangent_previous hlam hR.1 hlt le_rfl
      simpa only [hseed] using h
    · rw [heq,sub_self,mul_zero,add_zero,hseed]
  have hline : (Curve.W lam T R-R*Curve.D lam T R-q/5)-(-Curve.D lam T R)*T ≤ 0 := by
    nlinarith
  have hprevious : ∀ x : ℝ, R < x → x ≤ T → ∃ gain : ℝ, 0 ≤ gain ∧
      (Curve.W lam T R-R*Curve.D lam T R-q/5)-(-Curve.D lam T R)*x ≤ gain ∧ AnchorAt x gain := by
    intro x hx hxT
    have hz := (Curve.W_bounds hlam hlam1 hT hT1.le ⟨by linarith [hR.1],hxT⟩).1
    have ht := Curve.tangent_previous hlam hR.1 hx hxT
    exact ⟨Curve.W lam T x,hz,by nlinarith,hprior x hx hxT⟩
  have hpaired := paired_anchor_of_earlier F hS hβ hres hparent hprev
    (wlo:=R+q) (T:=T)
    (by linarith) (by linarith [hR.1]) (by linarith)
    (by unfold Qrh.TwoSlot.AnchorZeroLoss.High.cutHi; linarith [hR.2]) hT hT1.le
    (by linarith [hd.2]) (by linarith [hd.1]) hline hprevious htiny hclasses
  exact hpaired.mono le_rfl (by linarith)

/-- One common positive step size supplies every stage of the finite curve
construction. The tolerance is fixed inside the proof before all stage data. -/
theorem uniform_curve_step (F : ParentFace)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    {lam T : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hT : 3/4 ≤ T) (hT1 : T < 7/9) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ R r : ℝ, R ∈ Icc (3/4:ℝ) T → r ∈ Icc (3/4:ℝ) R →
      R-r ≤ eta → AnchorAt R (Curve.W lam T R) →
      (∀ x : ℝ, R < x → x ≤ T → AnchorAt x (Curve.W lam T x)) →
      AnchorAt r (Curve.W lam T r) := by
  obtain ⟨gamma,hg,hg1,hreserve⟩ := Curve.uniform_reserve_small hlam1 hT hT1
  let q : ℝ := min (1/1000000000000) (gamma/1000)
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  obtain ⟨eta,heta,hdom⟩ := Curve.uniform_output_dominates lam T hT hg
  refine ⟨min eta (1/10000),lt_min heta (by norm_num),?_⟩
  intro R r hR hr hstep hprev hprior
  have hsmall : R-r ≤ 1/10000 := hstep.trans (min_le_right _ _)
  have hlength : R-r ≤ eta := hstep.trans (min_le_left _ _)
  apply curve_step F hβ hres hparent hlam hlam1.le hT hT1 hg hg1 hq
    (min_le_left _ _) (min_le_right _ _) hR hr (hreserve R hR) hsmall
    (hdom r R hr.1 hr.2 hR.2 hlength r ⟨le_rfl,hr.2⟩) hprev hprior

end
end Qrh.TwoSlot.AnchorContinuum
