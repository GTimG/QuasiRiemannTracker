/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The two inverse and three ordinary thresholds of supplied C31, HF3--HF5.
These statements concern witness lengths; they assume no counting estimate. -/
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

def inverseThreshold (x S Q : ℝ) : ℝ := max (x-S) (2*x-Q)
def plainThreshold (B lam h x S Q : ℝ) : ℝ :=
  max (x-S) (max (x-h*Q) ((lam*x-B*Q)/(lam-1)))

theorem inverse_threshold_iff {x S Q r : ℝ} :
    inverseThreshold x S Q ≤ r ↔ x ≤ r+min S ((Q-r)/2) := by
  simp only [inverseThreshold,max_le_iff,add_min,le_min_iff]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem plain_threshold_iff {B lam h x S Q y : ℝ} (hlam : 1<lam) :
    plainThreshold B lam h x S Q ≤ y ↔
      x ≤ y+min S (min (h*Q) ((B*Q-y)/lam)) := by
  have hl : 0<lam := by linarith
  simp only [plainThreshold,max_le_iff,add_min,le_min_iff]
  rw [div_le_iff₀ (by linarith : 0<lam-1)]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    refine ⟨by linarith,by linarith,?_⟩
    have hh : x-y ≤ (B*Q-y)/lam := (le_div_iff₀ hl).mpr (by nlinarith)
    linarith
  · rintro ⟨h₁,h₂,h₃⟩
    have hh : (x-y)*lam ≤ B*Q-y :=
      (le_div_iff₀ hl).mp (by linarith)
    exact ⟨by linarith,by linarith,by nlinarith⟩

theorem inverse_width_admissible {S Q r : ℝ} (hS : 0≤S) (hr : r≤Q) :
    0≤min S ((Q-r)/2) ∧ min S ((Q-r)/2)≤S ∧
      r+2*min S ((Q-r)/2)≤Q := by
  have hc := min_le_right S ((Q-r)/2)
  exact ⟨le_min hS (by linarith),min_le_left _ _,by linarith⟩

theorem plain_width_admissible {B lam h S Q y : ℝ}
    (hlam : 1<lam) (hS : 0≤S) (hhQ : 0≤h*Q) (hy : y≤B*Q) :
    let z := min S (min (h*Q) ((B*Q-y)/lam))
    0≤z ∧ z≤S ∧ z≤h*Q ∧ y+lam*z≤B*Q := by
  have hl : 0<lam := by linarith
  have hc := (min_le_right S (min (h*Q) ((B*Q-y)/lam))).trans
    (min_le_right (h*Q) ((B*Q-y)/lam))
  refine ⟨le_min hS (le_min hhQ (div_nonneg (by linarith) hl.le)),
    min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),?_⟩
  have := (le_div_iff₀ hl).mp hc
  nlinarith

theorem amplitude_credit {nu p S z : ℝ} (hnu : 0≤nu)
    (hp : p≤1/2) (hz : z≤S) :
    nu*z ≤ 2*nu*p*z+nu*(1-2*p)*S := by
  nlinarith [mul_nonneg (mul_nonneg hnu (show 0≤1-2*p by linarith))
    (sub_nonneg.mpr hz)]

/-- A single original zero supplies the alternative. The cutoff and parent
are fixed before either witness is inspected. -/
theorem same_zero_alternative {B lam h x S Q r m eps : ℝ}
    (hlen : inverseThreshold x S Q+plainThreshold B lam h x S Q/2-eps≤r+m) :
    inverseThreshold x S Q-eps≤r ∨ plainThreshold B lam h x S Q≤2*m := by
  by_cases hr : inverseThreshold x S Q-eps≤r
  · exact Or.inl hr
  · exact Or.inr (by linarith)

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.inverse_threshold_iff
#print axioms QRH.Record1252270103Source.High.plain_threshold_iff
#print axioms QRH.Record1252270103Source.High.plain_width_admissible
#print axioms QRH.Record1252270103Source.High.same_zero_alternative
