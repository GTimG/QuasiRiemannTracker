import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowReflectedLength
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate

/- Original reflectedExponent with the extra loss required by total>1/6.
   This is the geometric inequality, not its analytic energy producer. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.LowExtension
noncomputable section
open OAI OAI.SevenEighths InverseTerminalWidths ProbeLowReflected

theorem compensated_reflected_exponent_with_length (total d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0≤d) (_hd1 : d≤total) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤((1-total)-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hell : ell₀≤total-d+ε) (hz : za≤ell₀+ε)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀)≤(1-total)-2*d+max 0 (5*total+d-1)/4+40*ε := by
  have hpen0 := le_max_left 0 (5*total+d-1)
  have hpen1 := le_max_right 0 (5*total+d-1)
  let Td := 2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀
  have hθlo : -ε≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤ε := (abs_le.mp hθ).2
  have hTd : Td≤H-3*d+6*ε := by dsimp [Td];linarith
  have hcol : v+ell≤H+10*ε := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)≤H+10*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  by_cases hu : hybridSaving v za=za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-max 0 (Td-v-3*ell-el)/2≤_
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td≤
        O₀/2+H-S₀-B₀+za-Td/4+(10+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td≤_
    apply hbound.trans
    dsimp [Td]
    linarith


theorem unselected_decay_absorbs_reflection_loss (total d : ℝ)
    (htotal : total≤1/5) (hd : 0≤d) :
    -d/2+max 0 (5*total+d-1)/8≤0 := by
  have hp : max 0 (5*total+d-1)≤d := max_le hd (by linarith)
  linarith

theorem rational_total_admissible : 0<ellRat ∧ ellRat<1/5 := by
  norm_num [ellRat]

#print axioms compensated_reflected_exponent_with_length
#print axioms unselected_decay_absorbs_reflection_loss
end
end BelowSevenEighthsTight.LowExtension
