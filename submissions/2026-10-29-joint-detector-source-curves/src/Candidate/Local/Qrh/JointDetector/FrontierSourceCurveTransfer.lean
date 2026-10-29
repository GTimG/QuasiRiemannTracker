/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Strict source-curve adapter at fixed selected gap 1/10^9.
Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FiniteReachability
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedStageHigh
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.ActualProvider

import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveTheorem
import Candidate.Local.Qrh.JointDetector.FrontierSourceFromCores
import Candidate.Local.Qrh.JointDetector.FrontierActualNorm

namespace Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
open Set RepeatedMarks RepeatedMarks.SourceCurve RepeatedMarks.CurvedSourceStep

/-- The exact finite-step HIGH payment. The uniform crossing reserve is
preserved; no source with a vanishing reserve is used. -/
theorem finite_high_payment {B0 L0 B L s n A ε ν a R w : ℝ}
    (hcross : B0-B=(L0-L)*s) (hL : 1 < L) (hn : n ≤ ν)
    (ha0 : 0 ≤ a) (ha : a ≤ ν) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hsmall : 5*A ≤ n*(L-1)) (hw : s ≤ w)
    (hgap : ε ≤ 1-ν*(B0-L0*s)-a*s-R) :
    ν*(B-L*w)+(R-1)*(1-6*(A*(w-s)))+a*(w-A*(w-s)) ≤ A*(w-s)-ε := by
  have hcoef : 0 ≤ ν*L-a+A*(6*R-5+a) := by
    have hν := mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ L-1)
    have hpos := mul_nonneg hA (show 0 ≤ 6*R+a by positivity)
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hw) hcoef
  have hid : A*(w-s)-(ν*(B-L*w)+(R-1)*(1-6*(A*(w-s)))+a*(w-A*(w-s))) =
      (1-ν*(B0-L0*s)-a*s-R)+(w-s)*(ν*L-a+A*(6*R-5+a)) := by
    have hBc : B=B0-(L0-L)*s := by linarith
    rw [hBc]
    ring
  linarith

/-- A positive continuous scalar gate on a compact domain has one fixed
positive reserve. This says nothing about arithmetic constants on a
continuum of sources. -/
theorem compact_positive_margin {α : Type*} [TopologicalSpace α]
    (K : Set α) (hK : IsCompact K) (hne : K.Nonempty) (f : α → ℝ)
    (hf : ContinuousOn f K) (hpos : ∀ x∈K, 0 < f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x∈K, ε ≤ f x := by
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne hf
  exact ⟨f x,hpos x hx,fun y hy => hmin hy⟩

/-- A uniform strict crossing reserve gives a genuine finite source step
through the proved natural-row count and packed supplier. -/
theorem source_step_of_crossing {p : Params} {phi floor n ε : ℝ}
    (g : GeometryCertificate p phi floor)
    (hfloor : (50001/100000:ℝ) ≤ floor)
    (hBmin : (9/10:ℝ) ≤ p.B0) (hL0 : (3/2:ℝ) ≤ p.L0)
    (hcap : (1/10:ℝ) ≤ p.c0) (hcapUpper : p.c0 ≤ 1/10)
    (hD : p.D=0) (hcut : matchedCut p phi 0=n)
    (hsmall : 5*p.A ≤ n*(p.L-1)) (hε : 0 < ε)
    (hcross : ∀ ν∈Icc n (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(p.B0-p.L0*crossing p)-a*crossing p-
        combineSelected (rawRepeatedCountRate p.B0 p.L0 (1/10)) ν a)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource p.B0 p.L0 p.c0) :
    QRH.Record1252270103Source.GlobalSource p.B p.L p.c := by
  have hq (w : ℝ) : cut p phi w=n := by
    unfold cut matchedCut
    simpa [matchedCut,hD] using hcut
  let F := fun w => repeatedFamily p.B0 p.L0 (1/10) (cut p phi w)
    g.B0_pos.le g.face.B₀_lt.le hL0 (by norm_num) (by norm_num)
    ⟨g.floor_pos.trans_le (g.cut_bounds w).1,(g.cut_bounds w).2⟩ true
  have hgates : Gates p (cut p phi) F := by
    apply g.gates F
    refine ⟨ε,hε,?_⟩
    intro w hw
    unfold F repeatedFamily
    apply familyOfRate_highReserve
    intro ν hν a ha
    simp only [ite_true]
    have hνn : n ≤ ν := by simpa [hq w] using hν.1
    have hνp : 0 < ν := (g.floor_pos.trans_le (g.cut_bounds w).1).trans_le hν.1
    have hr := rawRepeatedCountRate_bounds g.B0_pos.le g.face.B₀_lt.le hL0
      (by norm_num : (0:ℝ) ≤ 1/10) (by norm_num : (1/10:ℝ) ≤ 1/6)
      hνp hν.2 ha.1 ha.2
    have hR := (combineSelected_mem hν.2 ha
      (show rawRepeatedCountRate p.B0 p.L0 (1/10) ν a∈Icc (0:ℝ) 1 from
        ⟨by linarith [hr.1,hν.2],hr.2⟩)).1
    have hc : p.B0-p.B=(p.L0-p.L)*crossing p := by
      unfold crossing QRH.SilDensitySplit.Hybrid.cross
      field_simp [(sub_pos.mpr g.face.L_lt).ne']
    have hh := finite_high_payment hc (by linarith [g.face.one_lt_L]) hνn
      ha.1 ha.2 hR g.A_pos.le hsmall hw.1 (hcross ν ⟨hνn,hν.2⟩ a ha)
    simpa [QRH.SilDensitySplit.Hybrid.sel,hD] using hh
  have hnorm := FrontierCanonicalFromNorm.actual_norm NaturalSelectedNorm.natural_selected_cell_norm
  have hpSmall := RestartSourceChains.globalSource_cap_mono
    (by norm_num : (0:ℝ) ≤ 1/10) hcap hp
  have hcore := physicalCoreCount_of_globalSource floor p.B0 p.L0 (1/10)
    (by linarith) (by linarith [(g.cut_bounds 0).1,(g.cut_bounds 0).2])
    hBmin g.face.B₀_lt.le hL0 (by norm_num) (by norm_num) hpSmall hβ
  exact FrontierRepeatedMarks.CurvedSourceStep.source_step_of_physicalCoreCount p (1/10) floor
    g.face.B₀_lt.le hL0 (by norm_num) (by norm_num) (by linarith)
    (cut p phi) g.cut_bounds true (fun _ => hfloor) hnorm g.B0_pos.le hgates hcore hβ hp


theorem source_step_of_pure_crossing {p : Params} {phi floor n ε : ℝ}
    (g : GeometryCertificate p phi floor)
    (hfloor : (2/5:ℝ) ≤ floor)
    (hBmin : (9/10:ℝ) ≤ p.B0) (hL0 : (3/2:ℝ) ≤ p.L0)
    (hcap : (1/10:ℝ) ≤ p.c0) (hcapUpper : p.c0 ≤ 1/10)
    (hD : p.D=0) (hcut : matchedCut p phi 0=n)
    (hsmall : 5*p.A ≤ n*(p.L-1)) (hε : 0 < ε)
    (hcross : ∀ ν∈Icc n (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(p.B0-p.L0*crossing p)-a*crossing p-
        rawRepeatedCountRate p.B0 p.L0 (1/10) ν a)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource p.B0 p.L0 p.c0) :
    QRH.Record1252270103Source.GlobalSource p.B p.L p.c := by
  have hq (w : ℝ) : cut p phi w=n := by
    unfold cut matchedCut
    simpa [matchedCut,hD] using hcut
  let F := fun w => repeatedFamily p.B0 p.L0 (1/10) (cut p phi w)
    g.B0_pos.le g.face.B₀_lt.le hL0 (by norm_num) (by norm_num)
    ⟨g.floor_pos.trans_le (g.cut_bounds w).1,(g.cut_bounds w).2⟩ false
  have hgates : Gates p (cut p phi) F := by
    apply g.gates F
    refine ⟨ε,hε,?_⟩
    intro w hw
    unfold F repeatedFamily
    apply familyOfRate_highReserve
    intro ν hν a ha
    simp only [Bool.false_eq_true,ite_false]
    have hνn : n ≤ ν := by simpa [hq w] using hν.1
    have hνp : 0 < ν := (g.floor_pos.trans_le (g.cut_bounds w).1).trans_le hν.1
    have hr := rawRepeatedCountRate_bounds g.B0_pos.le g.face.B₀_lt.le hL0
      (by norm_num : (0:ℝ) ≤ 1/10) (by norm_num : (1/10:ℝ) ≤ 1/6)
      hνp hν.2 ha.1 ha.2
    have hR : 0 ≤ rawRepeatedCountRate p.B0 p.L0 (1/10) ν a := by
      linarith [hr.1,hν.2]
    have hc : p.B0-p.B=(p.L0-p.L)*crossing p := by
      unfold crossing QRH.SilDensitySplit.Hybrid.cross
      field_simp [(sub_pos.mpr g.face.L_lt).ne']
    have hh := finite_high_payment hc (by linarith [g.face.one_lt_L]) hνn
      ha.1 ha.2 hR g.A_pos.le hsmall hw.1 (hcross ν ⟨hνn,hν.2⟩ a ha)
    simpa [QRH.SilDensitySplit.Hybrid.sel,hD] using hh
  have hnorm := FrontierCanonicalFromNorm.actual_norm NaturalSelectedNorm.natural_selected_cell_norm
  have hpSmall := RestartSourceChains.globalSource_cap_mono
    (by norm_num : (0:ℝ) ≤ 1/10) hcap hp
  have hcore := physicalCoreCount_of_globalSource floor p.B0 p.L0 (1/10)
    (by linarith) (by linarith [(g.cut_bounds 0).1,(g.cut_bounds 0).2])
    hBmin g.face.B₀_lt.le hL0 (by norm_num) (by norm_num) hpSmall hβ
  exact FrontierRepeatedMarks.CurvedSourceStep.source_step_of_physicalCoreCount p (1/10) floor
    g.face.B₀_lt.le hL0 (by norm_num) (by norm_num) (by linarith)
    (cut p phi) g.cut_bounds false (by simp) hnorm g.B0_pos.le hgates hcore hβ hp

end
end Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve.finite_high_payment

#print axioms Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve.source_step_of_crossing
