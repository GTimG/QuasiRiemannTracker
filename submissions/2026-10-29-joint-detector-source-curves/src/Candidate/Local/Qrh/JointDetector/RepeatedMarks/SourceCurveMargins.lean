/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveCrossing
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveTransfer
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateContinuity

namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set

namespace RayCrossing
variable {B L s n r : ℝ} (h : RayCrossing B L s n r)
include h

/-- A fixed ray crossing has a positive reserve on the complete closed
amplitude-density domain, including both sides of the selected cutoff. -/
theorem uniform_crossing : ∃ ε : ℝ, 0 < ε ∧ ∀ ν∈Icc n (3/4:ℝ),
    ∀ a∈Icc (0:ℝ) ν, ε ≤ 1-ν*(B-L*s)-a*s-
      combineSelected (rawRepeatedCountRate B L (1/10)) ν a := by
  let low : Set (ℝ×ℝ) := rateDomain n ∩ {x | x.2 ≤ r*x.1}
  have hloCompact : IsCompact low := (rateDomain_compact n).inter_right
    (isClosed_le continuous_snd (continuous_const.mul continuous_fst))
  have hloNe : low.Nonempty := by
    refine ⟨(n,0),⟨?_,?_⟩⟩
    · exact ⟨le_rfl,h.n_upper.le,le_rfl,h.n_pos.le⟩
    · dsimp; exact (mul_pos h.ray_pos h.n_pos).le
  have hlowCont : ContinuousOn
      (fun x : ℝ×ℝ => 1-x.1*(B-L*s)-x.2*s-rawRepeatedCountRate B L (1/10) x.1 x.2) low := by
    have hr := (rawRate_continuousOn (B:=B) (c:=1/10) h.L_lower h.n_pos).mono
      (show low ⊆ rateDomain n from fun _ hx => hx.1)
    exact (((continuous_const.sub (continuous_fst.mul continuous_const)).sub
      (continuous_snd.mul continuous_const)).continuousOn).sub hr
  obtain ⟨εl,hεl,hlo⟩ := compact_positive_margin low hloCompact hloNe _ hlowCont (by
    intro x hx
    have hh := h.raw_crossing ⟨hx.1.1,hx.1.2.1⟩ ⟨hx.1.2.2.1,hx.2⟩
    linarith)
  let upper : ℝ → ℝ := fun ν => 1-ν*(B-L*s)-(r*ν)*s-detectorRate ν (r*ν)
  have huCont : ContinuousOn upper (Icc n (3/4:ℝ)) := by
    intro ν hν
    have hn := h.n_pos.trans_le hν.1
    have hra : r*ν ≤ ν := by nlinarith [h.ray_le]
    have hd : 3*(1-ν)+2*(ν-r*ν) ≠ 0 := by nlinarith [hν.2]
    have hc : ContinuousAt (fun ν => 1-ν*(B-L*s)-(r*ν)*s-
        jointCountExponent ν (r*ν)) ν := by
      unfold jointCountExponent witnessDen
      fun_prop (disch := assumption)
    apply hc.continuousWithinAt.congr
    · intro x hx
      have hxpos := h.n_pos.trans_le hx.1
      have hrx : r*x ≤ x := by nlinarith [h.ray_le]
      simp [upper,detectorRate,hrx]
    · simp [upper,detectorRate,hra]
  obtain ⟨εu,hεu,hu⟩ := compact_positive_margin (Icc n (3/4:ℝ)) isCompact_Icc
    ⟨n,le_rfl,h.n_upper.le⟩ upper huCont (by
      intro ν hν; have hh := h.selected_crossing hν; dsimp [upper]; linarith)
  refine ⟨min εl εu,lt_min hεl hεu,?_⟩
  intro ν hν a ha
  have hn := h.n_pos.trans_le hν.1
  have hra : r*ν ≤ ν := by nlinarith [h.ray_le]
  by_cases hla : a ≤ r*ν
  · have hl := hlo (ν,a) ⟨⟨hν.1,hν.2,ha.1,ha.2⟩,hla⟩
    have hc := combineSelected_le_raw (rawRepeatedCountRate B L (1/10)) ν a
    have hm := min_le_left εl εu
    dsimp at hl
    linarith
  · have hal : r*ν ≤ a := le_of_lt (lt_of_not_ge hla)
    have hcut : (500001/1000000:ℝ) < r*ν := by
      have := mul_le_mul_of_nonneg_left hν.1 h.ray_pos.le
      linarith [h.selected_gap]
    have hm := selectedTerm_antitone (P:=B-L*s) (H:=1) (S:=s) hν.2
      (show (1/2:ℝ) ≤ r*ν by linarith) (by norm_num) (by linarith [h.s_cap])
      (show r*ν∈Icc (r*ν) ν from ⟨le_rfl,hra⟩)
      (show a∈Icc (r*ν) ν from ⟨hal,ha.2⟩) hal
    have hh := hu ν hν
    have hc := combineSelected_le_selected (rawRepeatedCountRate B L (1/10)) (ν:=ν) (hcut.le.trans hal)
    have hmin := min_le_right εl εu
    dsimp [upper] at hh
    nlinarith

/-- A small secant-crossing perturbation spends only half the fixed reserve. -/
theorem nearby_crossing {ε s' : ℝ} (hε : 0 < ε)
    (hmargin : ∀ ν∈Icc n (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε ≤ 1-ν*(B-L*s)-a*s-combineSelected (rawRepeatedCountRate B L (1/10)) ν a)
    (hclose : |s'-s| ≤ ε/(2*L)) :
    ∀ ν∈Icc n (3/4:ℝ), ∀ a∈Icc (0:ℝ) ν,
      ε/2 ≤ 1-ν*(B-L*s')-a*s'-combineSelected (rawRepeatedCountRate B L (1/10)) ν a := by
  intro ν hν a ha
  have hn := h.n_pos.trans_le hν.1
  have hLp : 0 < L := by linarith [h.L_lower]
  have hcoef : 0 ≤ ν*L-a := by nlinarith [ha.2,h.L_lower]
  have hcoefhi : ν*L-a ≤ L := by nlinarith [ha.1,hν.2]
  have hd := (abs_le.mp hclose).1
  have heq : L*(ε/(2*L))=ε/2 := by field_simp
  have hp1 := mul_le_mul_of_nonneg_left hd hcoef
  have hp2 := mul_le_mul_of_nonneg_right hcoefhi
    (show 0 ≤ ε/(2*L) by positivity)
  have hg := hmargin ν hν a ha
  nlinarith

/-- The strict ray certificate supplies a fixed neighborhood of secant
crossings in which every sufficiently small, geometrically valid finite
step is an actual source transfer. -/
theorem local_source_step : ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (p : CurvedSourceStep.Params) (phi floor : ℝ),
      p.B0=B → p.L0=L →
      (g : CurvedSourceStep.GeometryCertificate p phi floor) →
      (50001/100000:ℝ) ≤ floor → (9/10:ℝ) ≤ B →
      (1/10:ℝ) ≤ p.c0 → p.c0 ≤ 1/10 → p.D=0 →
      CurvedSourceStep.matchedCut p phi 0=n →
      5*p.A ≤ n*(p.L-1) → |CurvedSourceStep.crossing p-s| ≤ ρ →
      (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource p.B0 p.L0 p.c0 →
      QRH.Record1252270103Source.GlobalSource p.B p.L p.c := by
  obtain ⟨ε,hε,hmargin⟩ := h.uniform_crossing
  refine ⟨ε/(2*L),by have := h.L_lower; positivity,?_⟩
  intro p phi floor hB hL g hf hBmin hcap hcapu hD hcut hsmall hclose hβ hp
  apply source_step_of_crossing g hf (by simpa [hB] using hBmin)
    (by simpa [hL] using h.L_lower) hcap hcapu hD hcut hsmall (half_pos hε) _ hβ hp
  simpa only [hB,hL] using h.nearby_crossing hε hmargin hclose

end RayCrossing
end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.RayCrossing.uniform_crossing
