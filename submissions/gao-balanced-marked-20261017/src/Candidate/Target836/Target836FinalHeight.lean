import Candidate.Target836.Target836BaselineMoments
import Candidate.Target836.Target836DetectorInput
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Candidate.Target836.Target836TransportParameters
import Candidate.Cycle63.Assembly.Count.ChosenHeight

                                        
                                          

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open scoped Classical
open Filter
open OAI.SevenEighths Target836DetectorCount HeckeFamily

def HeightAdmissible (D : BaselineData) (P : TransportParameters D) (J τ : ℝ) : Prop :=
  0< τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ 2*τ≤ D.t ∧
    τ*(2+4*P.eps)< D.t ∧ 2*τ*(1+J)≤ D.t

theorem choose_height (D : BaselineData) (P : TransportParameters D)
    (J : ℝ) (hJ : 0≤ J) : ∃τ : ℝ,HeightAdmissible D P J τ := by
  have ht:=D.t_pos
  have hcost:=D.cost_pos
  have heps:=P.eps_pos
  let τ : ℝ := min ((1/200:ℝ)*D.cost/16)
    (min (1/800) (min (D.t/(8*(J+1))) (D.t/(4*(2+4*P.eps)))))
  have hp : 0< τ := lt_min (by positivity)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hc : τ≤(1/200:ℝ)*D.cost/16 := min_le_left _ _
  have hd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hj : τ≤ D.t/(8*(J+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he : τ≤ D.t/(4*(2+4*P.eps)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hjm : τ*(8*(J+1))≤ D.t := (le_div_iff₀ (by positivity)).mp hj
  have hem : τ*(4*(2+4*P.eps))≤ D.t := (le_div_iff₀ (by positivity)).mp he
  refine ⟨τ,hp,by linarith,by linarith,?_,by nlinarith,by nlinarith⟩
  nlinarith [mul_nonneg hp.le hJ]

/-- The common height follows every fixed polynomial degree. -/
theorem height_admissible_mono {D : BaselineData} {P : TransportParameters D}
    {J J' τ : ℝ} (h : HeightAdmissible D P J τ) (hle : J'≤ J) :
    HeightAdmissible D P J' τ := by
  rcases h with ⟨ht,hd,hc,hs,he,hJ⟩
  exact ⟨ht,hd,hc,hs,he,(mul_le_mul_of_nonneg_left (by linarith : 1+J'≤1+J)
    (by linarith : 0≤2*τ)).trans hJ⟩

/-- The same height absorbs a genuine count degree and any fixed source degree. -/
theorem actual_joint_height (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D)
    (counts : Target836Count.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤ D.momentKappa)
    (hfine : ∀j,D.length j≤ Cycle25.sourceMesh D.t/200)
    (hdet : Target836InitialTransport.DetectorAffineInput)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hfineA : ∀j,D.length j≤ DetectorAffine.detectorMesh D.t/200)
    (Jw : ℝ) (hJw : 0≤ Jw) :
    ∀η : Character,∃τ : ℝ,HeightAdmissible D P Jw τ ∧
      ∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound D.toData (baselineSource D F) counts η Z τ
          (C*Z^D.t) (Z^(2*τ)) := by
  intro η
  obtain ⟨J,hJ,C,hC,hbound⟩ := actual_baseline_source_moments D F counts hβ hκβ hfine (hdet F hβ hβhi hfineA) η
  obtain ⟨τ,hheight⟩ := choose_height D P (J+Jw) (by positivity)
  have hw : HeightAdmissible D P Jw τ := height_admissible_mono hheight (by linarith)
  have hc : HeightAdmissible D P J τ := height_admissible_mono hheight (by linarith)
  refine ⟨τ,hw,?_⟩
  refine ⟨max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hbound τ hc.1 (by linarith [hc.2.1]),eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply hm.mono_constant (by linarith)
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z τ J D.t hC.le hZ hc.1.le hJ
    (by linarith [hc.2.2.2.2.2])).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
end
end Target836.FinalAssembly


#print axioms Target836.FinalAssembly.choose_height
#print axioms Target836.FinalAssembly.height_admissible_mono
#print axioms Target836.FinalAssembly.actual_joint_height
