/- Copyright (c) 2026 Sil. Apache-2.0.
Scalar variable-kappa feedback for the same fixed conductor join and the
same seventeen windows. This is not an analytic count or Mellin theorem.
 -/
import Candidate.SilPrior.FourthPower.ReturnEnvelopeBridge
import Candidate.SilPrior.FourthPower.ReturnContinuous

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnFeedback
noncomputable section
open ReturnCertificate ReturnContinuous ReturnEnvelopeBridge

def variableCapacity (k d : ℝ) : ℝ :=
  if d ≤ ds then oldCapacity k d else newCapacity d

def energy (k d δ p : ℝ) : ℝ :=
  returnValue d (variableCapacity k d) δ p (variableEnvelope k δ p)

theorem inverse_gap {k : ℝ} (hk : kappa ≤ k) :
    0 ≤ 1/kappa-1/k ∧ 1/kappa-1/k ≤ (100/49)*(k-kappa) := by
  have ha : 7/10 ≤ kappa := by linarith [complementary_guards.feedback_k]
  have ha0 : 0 < kappa := by linarith
  have hk0 : 0 < k := ha0.trans_le hk
  have hden : (49/100:ℝ) ≤ kappa*k := by
    nlinarith [mul_le_mul ha (ha.trans hk) (by norm_num : (0:ℝ) ≤ 7/10) ha0.le]
  have he : 1/kappa-1/k = (k-kappa)/(kappa*k) := by
    field_simp [ha0.ne', hk0.ne']
    <;> ring
  rw [he]
  refine ⟨div_nonneg (sub_nonneg.mpr hk) (mul_nonneg ha0.le hk0.le), ?_⟩
  calc
    _ ≤ (k-kappa)/(49/100) := div_le_div_of_nonneg_left
      (sub_nonneg.mpr hk) (by norm_num) hden
    _ = _ := by ring

theorem old_capacity_cost {k d δ p : ℝ} (hk : kappa ≤ k)
    (hd : d ∈ Set.Icc d0 dplus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    δ*p/2*(oldCapacity kappa d-oldCapacity k d) ≤ (25/784)*(k-kappa) := by
  have hd0 : 0 ≤ d := (by norm_num [d0] : (0:ℝ) ≤ d0).trans hd.1
  have hd2 : d ≤ 2*y := hd.2.trans (le_of_lt conductor_order.2.2.2.2)
  have hm0 : 0 ≤ min d (2*y-d) := le_min hd0 (sub_nonneg.mpr hd2)
  have hm : min d (2*y-d) ≤ (1/2:ℝ) := by
    have hm₁ := min_le_left d (2*y-d)
    have hm₂ := min_le_right d (2*y-d)
    have hy := complementary_guards.feedback_y
    linarith
  have hδp : δ*p ≤ (3/8:ℝ) := by
    nlinarith [mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)]
  have hweight0 : 0 ≤ δ*p*min d (2*y-d)/12 :=
    div_nonneg (mul_nonneg (mul_nonneg hδ.1 hp.1) hm0) (by norm_num)
  have hweight : δ*p*min d (2*y-d)/12 ≤ (1/64:ℝ) := by
    have hh := mul_le_mul hδp hm hm0 (by norm_num : (0:ℝ) ≤ 3/8)
    linarith
  have hi := inverse_gap hk
  calc
    _ = (δ*p*min d (2*y-d)/12)*(1/kappa-1/k) := by
      dsimp only [oldCapacity]
      ring
    _ ≤ (1/64)*((100/49)*(k-kappa)) :=
      mul_le_mul hweight hi.2 hi.1 (by norm_num)
    _ = _ := by ring

theorem selected_capacity_cost {k d δ p : ℝ} (hk : kappa ≤ k)
    (hd : d ∈ Set.Icc d0 dplus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    δ*p/2*(selectedCapacity d-variableCapacity k d) ≤ (25/784)*(k-kappa) := by
  by_cases hs : d ≤ ds
  · simpa only [selectedCapacity,variableCapacity,if_pos hs] using old_capacity_cost hk hd hδ hp
  · simp only [selectedCapacity,variableCapacity,if_neg hs,sub_self,mul_zero]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hk)

theorem count_cost {k d δ p : ℝ} (hk : kappa ≤ k)
    (hd : d ∈ Set.Icc d0 dplus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    (3/4)*d*(variableEnvelope k δ p-ReturnFinite.envelope δ p) ≤
      (5/288)*(k-kappa) := by
  have hd0 : 0 ≤ d := (by norm_num [d0] : (0:ℝ) ≤ d0).trans hd.1
  have hd1 : d ≤ 1 := by linarith [hd.2,complementary_guards.feedback_d]
  have hgap0 : 0 ≤ k-kappa := sub_nonneg.mpr hk
  have hg := variableEnvelope_gap_from_target hk hδ hp
  calc
    _ ≤ (3/4)*d*((5/12)*((k-kappa)/18)) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ ≤ (3/4)*((5/12)*((k-kappa)/18)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem energy_return {k d δ p : ℝ} (hk : kappa ≤ k)
    (hd : d ∈ Set.Icc d0 dplus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    energy k d δ p ≤ theta-reserve+(1/8)*(k-kappa) := by
  have hbase := complete_return hδ hp hd
  have hcap := selected_capacity_cost hk hd hδ hp
  have hcount := count_cost hk hd hδ hp
  have hsum : (5/288+25/784)*(k-kappa) ≤ (1/8)*(k-kappa) :=
    mul_le_mul_of_nonneg_right
      (by linarith [complementary_guards.feedback_cost]) (sub_nonneg.mpr hk)
  have he : energy k d δ p-
      returnValue d (selectedCapacity d) δ p (ReturnFinite.envelope δ p) =
      δ*p/2*(selectedCapacity d-variableCapacity k d)+
        (3/4)*d*(variableEnvelope k δ p-ReturnFinite.envelope δ p) := by
    dsimp only [energy,returnValue]
    ring
  linarith

/-- Strict contrary-parameter margin, on the entire fixed conductor interval.
The actual analytic energy must still be connected to this scalar expression. -/
theorem contrary_return {β d δ p : ℝ} (hβ : theta < β)
    (hd : d ∈ Set.Icc d0 dplus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    energy (2*β-1) d δ p-β ≤ -reserve-(3/4)*(β-theta) := by
  have hk : kappa ≤ 2*β-1 := by dsimp only [kappa];linarith
  have he := energy_return hk hd hδ hp
  dsimp only [kappa] at he
  linarith

end
end Candidate.SilPrior.FourthPower.ReturnFeedback
