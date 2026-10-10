import Cycle25.Arithmetic.Certificate

namespace Cycle25.Arithmetic

noncomputable def certJ (d u : ℝ) : ℝ :=
  (300*kappa0-40)+(120*kappa0+80)*u+d*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2)
noncomputable def certB (u : ℝ) : ℝ := (24*kappa0-4)+(48*kappa0)*u+16*u^2
noncomputable def certR (d u : ℝ) : ℝ := 1-d+d*certB u*(5-6*d)/(2*certJ d u)
noncomputable def boundaryF (d p : ℝ) : ℝ :=
  (1+ell0)/2+d/2+h0*(3*certR d (1/2-p)/4-5/12)+d*p*certT
noncomputable def certA1 (d : ℝ) : ℝ := certA10+certA11*d+certA12*d^2
noncomputable def certA2 (d : ℝ) : ℝ := certA20*d+certA21*d^2

theorem certJ_bounds {d u : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hu : 0 ≤ u ∧ u ≤ 1/2) :
    69 < certJ d u ∧ certJ d u ≤ 270 := by
  have hk := kappa0_short_interval
  have hk0 : 0 ≤ kappa0 := by linarith
  have hku0 : 0 ≤ kappa0*u := mul_nonneg hk0 hu.1
  have hj11 : 0 ≤ 144*kappa0-96 := by linarith
  have hu2 : u^2 ≤ (1:ℝ)/4 := by nlinarith
  have hju : (144*kappa0-96)*u ≤ (144*kappa0-96)*(1/2) :=
    mul_le_mul_of_nonneg_left hu.2 hj11
  have hder : (24-216*kappa0)+(144*kappa0-96)*u+96*u^2 ≤ 0 := by
    nlinarith
  have hdm : d*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hd.1 hder
  have hdl : (5/6)*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2) ≤
      d*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2) :=
    mul_le_mul_of_nonpos_right hd.2 hder
  have hbase : (120*kappa0+80)*u ≤ (120*kappa0+80)*(1/2) :=
    mul_le_mul_of_nonneg_left hu.2 (by linarith)
  unfold certJ
  constructor <;> nlinarith [sq_nonneg u]

theorem certA1_pos {d : ℝ} (hd : 0 ≤ d) : 0 < certA1 d := by
  have hc := coefficient_minorants
  have h1 : (-174:ℝ)*d ≤ certA11*d := mul_le_mul_of_nonneg_right (le_of_lt hc.2.1) hd
  have h2 : (347:ℝ)*d^2 ≤ certA12*d^2 :=
    mul_le_mul_of_nonneg_right (le_of_lt hc.2.2.1) (sq_nonneg d)
  unfold certA1
  linarith [hc.1, positive_A1_minorant d]

theorem certA2_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ certA2 d := by
  have hc := coefficient_minorants
  have ha : 0 ≤ certA20 := by linarith [hc.2.2.2.1]
  have hb : 0 ≤ certA21 := by linarith [hc.2.2.2.2.1]
  unfold certA2
  positivity

/-- The full bivariate identity B0.49, with no grid or rounding argument. -/
theorem global_certificate {d u : ℝ} (hJ : certJ d u ≠ 0) :
    8*certJ d u*(b0-boundaryF d (1/2-u)) =
      certK*(d-delta0)^2+u*certA1 d+u^2*certA2 d+768*certT*u^3*d^2 := by
  have hexpand : 8*certJ d u*(b0-boundaryF d (1/2-u)) =
      8*(300*kappa0-40)*certk0+
      (8*((300*kappa0-40)*certk1+(24-216*kappa0)*certk0)-15*h0*(24*kappa0-4))*d+
      certK*d^2+u*certA1 d+u^2*certA2 d+768*certT*u^3*d^2 := by
    unfold boundaryF certR
    rw [show (1/2:ℝ)-(1/2-u) = u by ring]
    field_simp [hJ]
    simp only [certJ, certB, certk0, certk1, certK, certA1, certA2,
      certA10, certA11, certA12, certA20, certA21]
    ring
  rw [hexpand, tangency_constant, tangency_linear]
  ring

theorem boundaryF_le_b0 {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    boundaryF d p ≤ b0 := by
  let u : ℝ := 1/2-p
  have hu : 0 ≤ u ∧ u ≤ 1/2 := by dsimp [u]; constructor <;> linarith
  have hJ : 0 < certJ d u := by linarith [(certJ_bounds hd hu).1]
  have heq := global_certificate (ne_of_gt hJ)
  have hc := coefficient_minorants
  have hK : 0 ≤ certK := by linarith [hc.2.2.2.2.2.1]
  have hT : 0 ≤ certT := by linarith [hc.2.2.2.2.2.2.2.1]
  have hA1 : 0 ≤ certA1 d := le_of_lt (certA1_pos hd.1)
  have hA2 : 0 ≤ certA2 d := certA2_nonneg hd.1
  have hu0 : 0 ≤ u := hu.1
  have hnonneg : 0 ≤ certK*(d-delta0)^2+u*certA1 d+u^2*certA2 d+768*certT*u^3*d^2 := by
    positivity
  have hL : 0 ≤ 8*certJ d u*(b0-boundaryF d (1/2-u)) := by rw [heq]; exact hnonneg
  have hdiff : 0 ≤ b0-boundaryF d (1/2-u) :=
    (mul_nonneg_iff_of_pos_left (by positivity : 0 < 8*certJ d u)).mp hL
  have hpu : (1/2:ℝ)-u = p := by dsimp [u]; ring
  rw [hpu] at hdiff
  linarith

theorem boundaryF_binding : boundaryF delta0 (1/2) = b0 := by
  have hd : 0 ≤ delta0 ∧ delta0 ≤ 5/6 := by
    constructor <;> linarith [delta0_interval.1, delta0_interval.2]
  have hJ : 0 < certJ delta0 0 := by linarith [(certJ_bounds hd ⟨le_refl 0, by norm_num⟩).1]
  have heq := global_certificate (d := delta0) (u := 0) (ne_of_gt hJ)
  norm_num at heq
  have hdif : b0-boundaryF delta0 (1/2) = 0 :=
    heq.resolve_left (ne_of_gt hJ)
  linarith

theorem boundaryF_eq_iff {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    boundaryF d p = b0 ↔ d = delta0 ∧ p = 1/2 := by
  constructor
  · intro he
    let u : ℝ := 1/2-p
    have hu : 0 ≤ u ∧ u ≤ 1/2 := by dsimp [u]; constructor <;> linarith
    have hu0 := hu.1
    have hJ : 0 < certJ d u := by linarith [(certJ_bounds hd hu).1]
    have heq := global_certificate (d := d) (u := u) (ne_of_gt hJ)
    have hpu : (1/2:ℝ)-u = p := by dsimp [u]; ring
    rw [hpu, he] at heq
    have hc := coefficient_minorants
    have hK : 0 < certK := by linarith [hc.2.2.2.2.2.1]
    have hT : 0 ≤ certT := by linarith [hc.2.2.2.2.2.2.2.1]
    have hA1 : 0 < certA1 d := certA1_pos hd.1
    have hA2 : 0 ≤ certA2 d := certA2_nonneg hd.1
    have ht0 : 0 ≤ 768*certT*u^3*d^2 := by positivity
    have ht1 : 0 ≤ u^2*certA2 d := by positivity
    have ht2 : 0 ≤ u*certA1 d := by positivity
    have ht3 : 0 ≤ certK*(d-delta0)^2 := by positivity
    have huA : u*certA1 d = 0 := by linarith
    have hsA : certK*(d-delta0)^2 = 0 := by linarith
    have hue : u = 0 := (mul_eq_zero.mp huA).resolve_right (ne_of_gt hA1)
    have hs : (d-delta0)^2 = 0 := (mul_eq_zero.mp hsA).resolve_left (ne_of_gt hK)
    constructor
    · nlinarith
    · dsimp [u] at hue; linarith
  · rintro ⟨rfl, rfl⟩
    exact boundaryF_binding

end Cycle25.Arithmetic
