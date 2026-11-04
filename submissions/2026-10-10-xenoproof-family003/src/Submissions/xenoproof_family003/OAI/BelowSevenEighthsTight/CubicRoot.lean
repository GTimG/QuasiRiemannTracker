import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 0
namespace BelowSevenEighthsTight
noncomputable section

def deltaPolynomial (r : ℝ) : ℝ := 1188*r^3-2160*r^2+171*r+190
def rootLower : ℝ := 388583354266034666797427991064892817399675065 / 10^45
def rootUpper : ℝ := 388583354266034666797427991064892817399675066 / 10^45

theorem root_interval_signs :
    rootLower < rootUpper ∧ (19/50 : ℝ) < rootLower ∧ rootUpper < 2/5 ∧
    0 < deltaPolynomial rootLower ∧ deltaPolynomial rootUpper < 0 := by
  norm_num [rootLower, rootUpper, deltaPolynomial]

theorem delta_root_exists :
    ∃ r : ℝ, r ∈ Set.Icc rootLower rootUpper ∧ deltaPolynomial r = 0 := by
  have hcont : Continuous deltaPolynomial := by unfold deltaPolynomial; fun_prop
  have hz : (0 : ℝ) ∈ Set.Icc (deltaPolynomial rootUpper) (deltaPolynomial rootLower) :=
    ⟨root_interval_signs.2.2.2.2.le, root_interval_signs.2.2.2.1.le⟩
  exact intermediate_value_Icc' root_interval_signs.1.le hcont.continuousOn hz

theorem delta_root_unique (r t : ℝ)
    (hr : r ∈ Set.Icc (19/50 : ℝ) (2/5))
    (ht : t ∈ Set.Icc (19/50 : ℝ) (2/5))
    (hr0 : deltaPolynomial r = 0) (ht0 : deltaPolynomial t = 0) : r = t := by
  have hrl := hr.1
  have hru := hr.2
  have htl := ht.1
  have htu := ht.2
  have hr2 : r^2 ≤ 4/25 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (by linarith : 0 ≤ 2/5+r)]
  have ht2 : t^2 ≤ 4/25 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith : 0 ≤ 2/5+t)]
  have hrt : r*t ≤ 4/25 := by
    have hm := mul_nonneg (sub_nonneg.mpr hr.2) (by linarith : 0 ≤ t)
    nlinarith
  have hk : 1188*(r^2+r*t+t^2)-2160*(r+t)+171 < 0 := by nlinarith
  have he : (r-t)*(1188*(r^2+r*t+t^2)-2160*(r+t)+171) = 0 := by
    calc
      _ = deltaPolynomial r-deltaPolynomial t := by unfold deltaPolynomial; ring
      _ = 0 := by rw [hr0, ht0]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_lt hk))

def deltaRoot : ℝ := Classical.choose delta_root_exists
theorem deltaRoot_spec :
    deltaRoot ∈ Set.Icc rootLower rootUpper ∧ deltaPolynomial deltaRoot = 0 :=
  Classical.choose_spec delta_root_exists

def sigmaRoot : ℝ := (7+18*deltaRoot)/(9+18*deltaRoot)

theorem sigmaRoot_enclosure :
    (87495701942009/100000000000000 : ℝ) < sigmaRoot ∧
    sigmaRoot < (87495701942010/100000000000000 : ℝ) := by
  have hr := deltaRoot_spec.1
  have hrl := hr.1
  have hru := hr.2
  have hl := root_interval_signs.2.1
  have hd : 0 < 9+18*deltaRoot := by linarith
  constructor
  · apply (lt_div_iff₀ hd).mpr
    norm_num [rootLower] at hrl
    norm_num [rootLower] at hl
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    norm_num [rootUpper] at hru
    nlinarith

theorem sigmaRoot_cubic :
    7884*sigmaRoot^3-18819*sigmaRoot^2+14643*sigmaRoot-3686 = 0 := by
  have hr := deltaRoot_spec.2
  have hlo := deltaRoot_spec.1.1
  have hpos := root_interval_signs.2.1
  have hd : 9+18*deltaRoot ≠ 0 := ne_of_gt (by linarith)
  unfold sigmaRoot
  field_simp
  dsimp [deltaPolynomial] at hr
  nlinarith [hr]

#print axioms delta_root_exists
#print axioms delta_root_unique
#print axioms sigmaRoot_cubic
end
end BelowSevenEighthsTight
