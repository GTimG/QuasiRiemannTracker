/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurveHighTemplates
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.AffineHighCertificate
namespace Qrh.JointDetector.RepeatedMarks.CurveHighTemplates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open BernsteinBox HighTemplates AuxHighTemplates Set

private theorem scalar_coordinates (s A D v : ℝ) (hW : 1+D*v≠0) :
  (1+(D-6*A)*v)=(1+D*v)*(1-6*(A*v/(1+D*v))) ∧
  (s+v)*(1+D*v)-A*v=(1+D*v)*(s+v-A*v/(1+D*v)) ∧
  A*v=(1+D*v)*(A*v/(1+D*v)) := by
  have hu : (1+D*v)*(A*v/(1+D*v))=A*v := by
    rw [mul_comm (1+D*v),div_mul_cancel₀ _ hW]
  constructor
  · nlinarith only [hu]
  constructor
  · nlinarith only [hu]
  · exact hu.symm


theorem cap_homogeneous (B0 L0 c a0 a1 W H P S u rho nu : ℝ) :
  affineCapHigh B0 L0 c a0 a1 (W*H) (W*P) (W*S) (W*u) (W*rho) nu =
    W*affineCapHigh B0 L0 c a0 a1 H P S u rho nu := by
  unfold affineCapHigh
  ring


theorem cap_scalar_nonneg (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v)
    (hp : 0 ≤ powerEval (capPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    0 ≤ affineCapHigh B0 L0 c a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
  rw [cap_power] at hp
  obtain ⟨hH,hS,hu⟩ := scalar_coordinates s A D v hW.ne'
  have hP : (B-L*(s+v))*(1+D*v)=(1+D*v)*(B-L*(s+v)) := mul_comm _ _
  have hr : rho*(1+D*v)=(1+D*v)*rho := mul_comm _ _
  have he :
    affineCapHigh B0 L0 c a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu =
    (1+D*v)*affineCapHigh B0 L0 c a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
    calc
      _ = affineCapHigh B0 L0 c a0 a1 ((1+D*v)*(1-6*(A*v/(1+D*v))))
        ((1+D*v)*(B-L*(s+v))) ((1+D*v)*(s+v-A*v/(1+D*v)))
        ((1+D*v)*(A*v/(1+D*v))) ((1+D*v)*rho) nu := by
          congr 1
      _ = _ := cap_homogeneous _ _ _ _ _ _ _ _ _ _ _ _
  rw [he] at hp
  exact (mul_nonneg_iff_of_pos_left hW).1 hp


theorem budget_homogeneous (B0 L0 c a0 a1 W H P S u rho nu : ℝ) :
  affineBudgetHigh B0 L0 c a0 a1 (W*H) (W*P) (W*S) (W*u) (W*rho) nu =
    W*affineBudgetHigh B0 L0 c a0 a1 H P S u rho nu := by
  unfold affineBudgetHigh
  ring


theorem budget_scalar_nonneg (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v)
    (hp : 0 ≤ powerEval (budgetPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    0 ≤ affineBudgetHigh B0 L0 c a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
  rw [budget_power] at hp
  obtain ⟨hH,hS,hu⟩ := scalar_coordinates s A D v hW.ne'
  have hP : (B-L*(s+v))*(1+D*v)=(1+D*v)*(B-L*(s+v)) := mul_comm _ _
  have hr : rho*(1+D*v)=(1+D*v)*rho := mul_comm _ _
  have he :
    affineBudgetHigh B0 L0 c a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu =
    (1+D*v)*affineBudgetHigh B0 L0 c a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
    calc
      _ = affineBudgetHigh B0 L0 c a0 a1 ((1+D*v)*(1-6*(A*v/(1+D*v))))
        ((1+D*v)*(B-L*(s+v))) ((1+D*v)*(s+v-A*v/(1+D*v)))
        ((1+D*v)*(A*v/(1+D*v))) ((1+D*v)*rho) nu := by
          congr 1
      _ = _ := budget_homogeneous _ _ _ _ _ _ _ _ _ _ _ _
  rw [he] at hp
  exact (mul_nonneg_iff_of_pos_left hW).1 hp


theorem selected_homogeneous (a0 a1 W H P S u rho nu : ℝ) :
  selectedHigh a0 a1 (W*H) (W*P) (W*S) (W*u) (W*rho) nu =
    W*selectedHigh a0 a1 H P S u rho nu := by
  unfold selectedHigh selectedSave selectedDen
  ring


theorem selected_scalar_nonneg (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v)
    (hp : 0 ≤ powerEval (selectedPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    0 ≤ selectedHigh a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
  rw [selected_power] at hp
  obtain ⟨hH,hS,hu⟩ := scalar_coordinates s A D v hW.ne'
  have hP : (B-L*(s+v))*(1+D*v)=(1+D*v)*(B-L*(s+v)) := mul_comm _ _
  have hr : rho*(1+D*v)=(1+D*v)*rho := mul_comm _ _
  have he :
    selectedHigh a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu =
    (1+D*v)*selectedHigh a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
    calc
      _ = selectedHigh a0 a1 ((1+D*v)*(1-6*(A*v/(1+D*v))))
        ((1+D*v)*(B-L*(s+v))) ((1+D*v)*(s+v-A*v/(1+D*v)))
        ((1+D*v)*(A*v/(1+D*v))) ((1+D*v)*rho) nu := by
          congr 1
      _ = _ := selected_homogeneous _ _ _ _ _ _ _ _ _
  rw [he] at hp
  exact (mul_nonneg_iff_of_pos_left hW).1 hp


theorem tail_homogeneous (B0 a0 a1 W H P S u rho nu : ℝ) :
  tailHigh B0 a0 a1 (W*H) (W*P) (W*S) (W*u) (W*rho) nu =
    W*tailHigh B0 a0 a1 H P S u rho nu := by
  unfold tailHigh
  ring


theorem tail_scalar_nonneg (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v)
    (hp : 0 ≤ powerEval (tailPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    0 ≤ tailHigh B0 a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
  rw [tail_power] at hp
  obtain ⟨hH,hS,hu⟩ := scalar_coordinates s A D v hW.ne'
  have hP : (B-L*(s+v))*(1+D*v)=(1+D*v)*(B-L*(s+v)) := mul_comm _ _
  have hr : rho*(1+D*v)=(1+D*v)*rho := mul_comm _ _
  have he :
    tailHigh B0 a0 a1 (1+(D-6*A)*v) ((B-L*(s+v))*(1+D*v))
      ((s+v)*(1+D*v)-A*v) (A*v) (rho*(1+D*v)) nu =
    (1+D*v)*tailHigh B0 a0 a1 (1-6*(A*v/(1+D*v))) (B-L*(s+v))
      (s+v-A*v/(1+D*v)) (A*v/(1+D*v)) rho nu := by
    calc
      _ = tailHigh B0 a0 a1 ((1+D*v)*(1-6*(A*v/(1+D*v))))
        ((1+D*v)*(B-L*(s+v))) ((1+D*v)*(s+v-A*v/(1+D*v)))
        ((1+D*v)*(A*v/(1+D*v))) ((1+D*v)*rho) nu := by
          congr 1
      _ = _ := tail_homogeneous _ _ _ _ _ _ _ _ _ _
  rw [he] at hp
  exact (mul_nonneg_iff_of_pos_left hW).1 hp

theorem cap_weighted_divider (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v) (hnu : 0<nu) (hnuhi : nu≤3/4)
    (ha : 0<a0+a1*nu) (hahi : a0+a1*nu≤nu)

    (hp : 0 ≤ powerEval (capPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    nu*(B-L*(s+v))+(capCrossingRate c nu ((a0+a1*nu)/(2*nu))-1)*
      (1-6*(A*v/(1+D*v)))+(a0+a1*nu)*(s+v-A*v/(1+D*v))≤A*v/(1+D*v)-rho := by
  have hs := cap_scalar_nonneg B0 L0 c a0 a1 B L s A D rho nu v hW hp
  rw [affineCap_high_identity] at hs
  have hd := affineCap_den_pos (B:=B0) (L:=L0) (c:=c) (s:=0) (z:=1)
    hnu hnuhi ha hahi  ⟨by norm_num,le_rfl⟩
  have hb := affine_rational_high_of_polynomial hd hs

  have hr := capCrossingRate_eq_affine (B:=B0) (L:=L0) (c:=c) (s:=0) (z:=1)
    hnu.ne'  hd.ne'
  simp only [mul_one] at hr
  rw [←hr] at hb
  exact hb

theorem budget_weighted_divider (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v) (hnu : 0<nu) (hnuhi : nu≤3/4)
    (ha : 0<a0+a1*nu) (hahi : a0+a1*nu≤nu)
    (hL0 : 3/2≤L0)
    (hp : 0 ≤ powerEval (budgetPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    nu*(B-L*(s+v))+(budgetCrossingRate B0 L0 nu ((a0+a1*nu)/(2*nu))-1)*
      (1-6*(A*v/(1+D*v)))+(a0+a1*nu)*(s+v-A*v/(1+D*v))≤A*v/(1+D*v)-rho := by
  have hs := budget_scalar_nonneg B0 L0 c a0 a1 B L s A D rho nu v hW hp
  rw [affineBudget_high_identity] at hs
  have hd := affineBudget_den_pos (B:=B0) (L:=L0) (c:=c) (s:=0) (z:=1)
    hnu hnuhi ha hahi hL0 ⟨by norm_num,le_rfl⟩
  have hb := affine_rational_high_of_polynomial hd hs
  have hLne : L0≠0 := by linarith
  have hr := budgetCrossingRate_eq_affine (B:=B0) (L:=L0) (c:=c) (s:=0) (z:=1)
    hnu.ne' hLne hd.ne'
  simp only [mul_one] at hr
  rw [←hr] at hb
  exact hb

theorem selected_weighted_divider (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v) (hnuhi : nu≤3/4) (hahi : a0+a1*nu≤nu)
    (hp : 0 ≤ powerEval (selectedPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    nu*(B-L*(s+v))+(detectorRate nu (a0+a1*nu)-1)*
      (1-6*(A*v/(1+D*v)))+(a0+a1*nu)*(s+v-A*v/(1+D*v))≤A*v/(1+D*v)-rho := by
  have hs := selected_scalar_nonneg B0 L0 c a0 a1 B L s A D rho nu v hW hp
  have hd : 0<selectedDen a0 a1 nu := by unfold selectedDen;linarith
  have hs' : 0 ≤ (1-6*(A*v/(1+D*v)))*selectedSave a0 a1 nu-
      nu*(B-L*(s+v))*selectedDen a0 a1 nu-
      (a0+a1*nu)*(s+v-A*v/(1+D*v))*selectedDen a0 a1 nu+
      (A*v/(1+D*v))*selectedDen a0 a1 nu-rho*selectedDen a0 a1 nu := by
    unfold selectedHigh at hs
    nlinarith only [hs]
  have hb := affine_rational_high_of_polynomial hd hs'
  rw [←selected_rate_eq_affine hd.ne' hahi] at hb
  exact hb

theorem tail_weighted_divider (B0 L0 c a0 a1 B L s A D rho nu v : ℝ)
    (hW : 0<1+D*v)
    (hp : 0 ≤ powerEval (tailPower B0 L0 c a0 a1 B L s A D rho) nu v) :
    nu*(B-L*(s+v))+((1-nu*B0)-1)*(1-6*(A*v/(1+D*v)))+
      (a0+a1*nu)*(s+v-A*v/(1+D*v))≤A*v/(1+D*v)-rho := by
  have hs := tail_scalar_nonneg B0 L0 c a0 a1 B L s A D rho nu v hW hp
  unfold tailHigh at hs
  nlinarith only [hs]

end
end Qrh.JointDetector.RepeatedMarks.CurveHighTemplates

#print axioms Qrh.JointDetector.RepeatedMarks.CurveHighTemplates.cap_weighted_divider

#print axioms Qrh.JointDetector.RepeatedMarks.CurveHighTemplates.budget_weighted_divider

#print axioms Qrh.JointDetector.RepeatedMarks.CurveHighTemplates.selected_weighted_divider

#print axioms Qrh.JointDetector.RepeatedMarks.CurveHighTemplates.tail_weighted_divider
