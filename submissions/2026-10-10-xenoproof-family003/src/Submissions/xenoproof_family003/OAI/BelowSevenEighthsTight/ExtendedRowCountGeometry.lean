import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CapacityBounds

/- Parameterized numerical row-count geometry. These statements supply the
   algebra needed to retune DetectorRowCountCrossing; they do not assert an
   analytic bound for a set of rows. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.RowCountExtension
noncomputable section

def denominator (c x : ℝ) : ℝ := 3-(1+2*c)*x
def primeWeight (c x : ℝ) : ℝ := (2-2*c*x)*(1-x)
def crossing (c x t : ℝ) : ℝ := ((2-2*c*x)*t-(1-c)*x)/denominator c x
def inverseExponent (δ x r : ℝ) : ℝ := 1-δ*(x+(1-x)*r)
def plainExponent (c δ x t r : ℝ) : ℝ := 1-δ*(c*x+(2-2*c*x)*(t-r))
def shortExponent (c δ x t : ℝ) : ℝ :=
  1-δ+δ*primeWeight c x/denominator c x*(3/2-t)

theorem reciprocal_range (κ : ℝ) (hk : 13/18 ≤ κ) (hku : κ ≤ 3/4) :
    (4/9 : ℝ) ≤ 1/(3*κ) ∧ 1/(3*κ) ≤ 6/13 := by
  have hp : 0 < 3*κ := by linarith
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

theorem denominator_lower {c x : ℝ} (hc : 4/9 ≤ c) (hcu : c ≤ 6/13)
    (hx : 0 ≤ x) (hxu : x ≤ 1/2) : 53/26 ≤ denominator c x := by
  have h := mul_le_mul hcu hxu hx (by norm_num : (0:ℝ) ≤ 6/13)
  unfold denominator
  nlinarith

theorem crossing_bounds {c x t : ℝ} (hc : 4/9 ≤ c) (hcu : c ≤ 6/13)
    (hx : 0 ≤ x) (hxu : x ≤ 1/2) (ht : 1 ≤ t) (htu : t ≤ 3/2) :
    23/37 ≤ crossing c x t ∧ crossing c x t ≤ 1 ∧
      1/3 ≤ t-crossing c x t ∧ t-crossing c x t ≤ 1/2 := by
  have hd : 0 < denominator c x := lt_of_lt_of_le (by norm_num) (denominator_lower hc hcu hx hxu)
  have hcx := mul_le_mul hcu hxu hx (by norm_num : (0:ℝ) ≤ 6/13)
  have hp : 0 ≤ 2-2*c*x := by nlinarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hptu := mul_le_mul_of_nonneg_left htu hp
  have hmt := mul_le_mul_of_nonneg_left ht (by linarith : 0 ≤ 1-x)
  have hmtu := mul_le_mul_of_nonneg_left htu (by linarith : 0 ≤ 1-x)
  have hcl := mul_le_mul_of_nonneg_right hc hx
  have hcu' := mul_le_mul_of_nonneg_right hcu hx
  have he : t-crossing c x t = ((1-x)*t+(1-c)*x)/denominator c x := by
    unfold crossing
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hd.ne']
    unfold denominator
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_, (div_le_iff₀ hd).mpr ?_, ?_, ?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

theorem inverse_at_crossing (c δ x t : ℝ) (hd : denominator c x ≠ 0) :
    inverseExponent δ x (crossing c x t) = shortExponent c δ x t := by
  unfold inverseExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

theorem plain_at_crossing (c δ x t : ℝ) (hd : denominator c x ≠ 0) :
    plainExponent c δ x t (crossing c x t) = shortExponent c δ x t := by
  unfold plainExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

theorem selected_short_bound {c δ x t r : ℝ}
    (hc : 4/9 ≤ c) (hcu : c ≤ 6/13) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxu : x ≤ 1/2) :
    (r ≤ crossing c x t → plainExponent c δ x t r ≤ shortExponent c δ x t) ∧
    (crossing c x t ≤ r → inverseExponent δ x r ≤ shortExponent c δ x t) := by
  have hd : denominator c x ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num) (denominator_lower hc hcu hx hxu))
  have hcx := mul_le_mul hcu hxu hx (by norm_num : (0:ℝ) ≤ 6/13)
  constructor
  · intro hr
    rw [← plain_at_crossing c δ x t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (by nlinarith : 0 ≤ 2-2*c*x)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [← inverse_at_crossing c δ x t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 1-x)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

theorem plain_capacity_bound {m κ : ℝ}
    (hm : 1/3 ≤ m) (hmu : m ≤ 1/2) (hk : 13/18 ≤ κ) :
    0 ≤ (1-2*m)/(6*κ) ∧ (1-2*m)/(6*κ) ≤ 1/13 := by
  have hp : 0 < 6*κ := by linarith
  constructor
  · exact div_nonneg (by linarith) hp.le
  · apply (div_le_iff₀ hp).mpr
    nlinarith

theorem strict_inverse_capacity {r ν : ℝ} (hr : 23/37 ≤ r) (hν : 0 < ν) :
    r+2*((1-r)/2-ν) < 1 ∧ 2*r+8*((1-r)/2-ν) < 3 ∧
      (1-r)/2 ≤ 7/37 ∧ 9/37 ≤ 3-2*r-8*((1-r)/2-ν) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem source_coordinate_identities (c y : ℝ) :
    denominator c (1/2-y) = 5/2-c+(1+2*c)*y ∧
    primeWeight c (1/2-y) = 1-c/2+2*y+2*c*y^2 := by
  constructor <;> simp only [denominator, primeWeight] <;> ring

theorem generalized_J_lower (c d y : ℝ)
    (hc : 4/9 ≤ c) (hcu : c ≤ 6/13) (hd : 0 ≤ d) (hdu : d ≤ 5/6)
    (hy : 0 ≤ y) (hyu : y ≤ 1/2) :
    25/39 ≤ (5/6-d)*(5/2-c+(1+2*c)*y)+d*(1-c/2+2*y+2*c*y^2) := by
  have hD := denominator_lower hc hcu (by linarith : 0 ≤ 1/2-y) (by linarith : 1/2-y ≤ 1/2)
  rw [(source_coordinate_identities c y).1] at hD
  have hP : 10/13 ≤ 1-c/2+2*y+2*c*y^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ c) (sq_nonneg y)]
  have h1 := mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 5/6-d)
  have h2 := mul_le_mul_of_nonneg_left hP hd
  nlinarith

#print axioms crossing_bounds
#print axioms selected_short_bound
#print axioms generalized_J_lower
end
end BelowSevenEighthsTight.RowCountExtension
