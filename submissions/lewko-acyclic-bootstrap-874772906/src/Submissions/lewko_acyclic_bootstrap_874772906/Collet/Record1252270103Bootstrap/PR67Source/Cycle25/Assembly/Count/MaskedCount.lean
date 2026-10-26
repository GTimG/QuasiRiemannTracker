import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Assembly.Count.Endpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section
open HeckeDetectorPhysicalSelection
open scoped Classical BigOperators

theorem coefficient_antitone {κ x y : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) : coefficient y κ≤ coefficient x κ := by
  have hdx : 0<denominator x κ := lt_of_lt_of_le (by norm_num) (denominator_lower hx (hxy.trans hy) hk hk1)
  have hdy : 0<denominator y κ := lt_of_lt_of_le (by norm_num) (denominator_lower (hx.trans hxy) hy hk hk1)
  let a : ℝ := 1/(3*κ)
  have ha : 0≤a := by dsimp [a]; positivity
  have ha1 : a≤10/21 := (div_le_iff₀ (show 0<3*κ by linarith)).mpr (by linarith)
  have hbx : b x κ=x*a := by unfold b; dsimp [a]; ring
  have hby : b y κ=y*a := by unfold b; dsimp [a]; ring
  have he : primeWeight x κ*denominator y κ-primeWeight y κ*denominator x κ=
      (y-x)*(4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y) := by
    unfold primeWeight denominator
    rw [hbx,hby]
    ring
  have hsum : x+y≤1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum ha
  have hp : 0≤4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y := by
    have hp := mul_nonneg (mul_nonneg (mul_nonneg ha (by linarith : 0≤1+2*a)) hx) (hx.trans hxy)
    nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hxy) hp
  unfold coefficient
  apply (div_le_div_iff₀ hdy hdx).mpr
  linarith

theorem rowCount_antitone {δ κ x y : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) : rowCount δ y κ≤ rowCount δ x κ := by
  have hc := coefficient_antitone hk hk1 hx hxy hy
  have hcx := coefficient_nonneg hx (hxy.trans hy) hk hk1
  have hcy := coefficient_nonneg (hx.trans hxy) hy hk hk1
  have hv : 0<V δ := by unfold V; linarith
  have hdx : 0<2*(V δ+δ*coefficient x κ) := by positivity
  have hdy : 0<2*(V δ+δ*coefficient y κ) := by positivity
  unfold rowCount
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ hdy hdx).mpr
  have hh := mul_nonneg (mul_nonneg hδ (sq_nonneg (V δ))) (sub_nonneg.mpr hc)
  nlinarith

end
end OAI.SevenEighths.Cycle25DetectorRowCount

end Record1252270103Bootstrap.PR67
