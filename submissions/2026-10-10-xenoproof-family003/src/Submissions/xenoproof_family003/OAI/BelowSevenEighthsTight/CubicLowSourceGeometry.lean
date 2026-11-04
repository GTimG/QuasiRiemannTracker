import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CubicEndpoint
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedLowSourceScales

/- Algebraic source geometry for the already defined limiting cubic point.
   This is not a physical-probe growth theorem. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.LowExtension
noncomputable section

def cubicLX (r : ℝ) : ℝ := (1-ellOptimal r-bOptimal r)/2

private lemma coarse_root_bounds :
    (38858/100000:ℝ)≤deltaRoot ∧ deltaRoot≤(38859/100000:ℝ) := by
  constructor
  · exact (show (38858/100000:ℝ)≤rootLower by norm_num [rootLower]).trans deltaRoot_spec.1.1
  · exact deltaRoot_spec.1.2.trans (show rootUpper≤(38859/100000:ℝ) by norm_num [rootUpper])

theorem cubic_parameter_window :
    (1/6:ℝ)≤ellOptimal deltaRoot ∧ ellOptimal deltaRoot≤17/100 ∧
    (3/25:ℝ)≤bOptimal deltaRoot ∧ bOptimal deltaRoot≤1/8 := by
  have hl := coarse_root_bounds.1
  have hu := coarse_root_bounds.2
  have hsqlo : (38858/100000:ℝ)^2≤deltaRoot^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl)
      (show 0≤deltaRoot+(38858/100000:ℝ) by linarith)]
  have hsqhi : deltaRoot^2≤(38859/100000:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu)
      (show 0≤(38859/100000:ℝ)+deltaRoot by linarith)]
  dsimp only [ellOptimal,bOptimal]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem cubic_source_geometry :
    0<ellOptimal deltaRoot ∧ ellOptimal deltaRoot≤1/5 ∧
    cubicLX deltaRoot+lyOptimal deltaRoot=1-ellOptimal deltaRoot ∧
    0<lyOptimal deltaRoot-cubicLX deltaRoot ∧
    0<2*cubicLX deltaRoot-lyOptimal deltaRoot-ellOptimal deltaRoot ∧
    lyOptimal deltaRoot≤1 := by
  obtain ⟨hel,heu,hbl,hbu⟩ := cubic_parameter_window
  dsimp only [cubicLX,lyOptimal]
  refine ⟨by linarith,by linarith,by ring,by linarith,by linarith,by linarith⟩

theorem cubic_gram_exponent :
    (5*cubicLX deltaRoot+lyOptimal deltaRoot)/12=
      sigmaRoot+(-2/3-bOptimal deltaRoot/6) := by
  rw [←sigmaOptimal_root]
  dsimp only [cubicLX,lyOptimal,ellOptimal,sigmaOptimal]
  ring

#print axioms cubic_parameter_window
#print axioms cubic_source_geometry
#print axioms cubic_gram_exponent
end
end BelowSevenEighthsTight.LowExtension
