import Candidate.Cycle63.Assembly.Count.BaselineMoments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput

namespace OAI.SevenEighths.Cycle63DetectorCount
noncomputable section
open scoped Classical
open Filter HeckeFamily

/-- One height exponent is chosen after the fixed polynomial degree and before
all live rows and all physical amplitude classes. -/
theorem actual_chosen_height (D : BaselineData) (F : BaselineSourceData D)
    (counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200) :
    ∃τ:ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ 2*τ≤D.t ∧
      ∀η:Character,∃C:ℝ,1≤C ∧ ∀ᶠZ:ℝ in atTop,
        SourceMomentBound D.toData (baselineSource D F) counts η Z τ
          (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩:=actual_baseline_source_moments D F counts hβ hκβ hfine
  let τ : ℝ:=min ((1/200:ℝ)*D.cost/16) (min (1/800) (D.t/(4*(J+1))))
  have ht : 0<τ:=lt_min (by have:=D.cost_pos;positivity)
    (lt_min (by norm_num) (by have:=D.t_pos;positivity))
  have hcost : τ≤(1/200:ℝ)*D.cost/16:=min_le_left _ _
  have hd : τ≤1/800:=(min_le_right _ _).trans (min_le_left _ _)
  have hsmall : τ≤D.t/(4*(J+1)):=(min_le_right _ _).trans (min_le_right _ _)
  have hb : τ*(4*(J+1))≤D.t:=(le_div_iff₀ (by positivity)).mp hsmall
  have hτJ : 0≤τ*J:=mul_nonneg ht.le hJ
  refine ⟨τ,ht,by linarith,by linarith [D.cost_pos],by nlinarith,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hbound τ ht (by linarith),eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply hm.mono_constant (by linarith)
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z τ J D.t hC.le hZ ht.le hJ
    (by nlinarith)).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
end
end OAI.SevenEighths.Cycle63DetectorCount
