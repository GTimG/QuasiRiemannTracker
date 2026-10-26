/- Repeated marks: fork of Collet's generic return module Transport.FinalHeight (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.Transport.TransportParameters

                                        
                                          

set_option autoImplicit false
namespace QRH.RepeatedMarks.Return.GenericPhysical.FinalAssembly
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
open scoped Classical
open Filter
open OAI.SevenEighths HeckeFamily
open QRH.Record1252270103Return.GenericPhysical QRH.RepeatedMarks.Return.GenericPhysical.Assembly

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

end
end QRH.RepeatedMarks.Return.GenericPhysical.FinalAssembly
