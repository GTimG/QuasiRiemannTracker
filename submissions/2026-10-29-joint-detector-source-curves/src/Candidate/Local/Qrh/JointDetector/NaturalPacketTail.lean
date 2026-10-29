/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.SelectedTails

/-! Absolute tails for the complete natural mixed-Poisson packet.

The puncture labels may depend on BOTH original rows. Their cardinality is
charged only in the far tail. The raw frequency cutoff stays within the
fixed auxiliary source cap; a stronger tail changes the Schwartz order,
not that cutoff. Near frequencies require the separate signed assembly.
-/
namespace Qrh.JointDetector.NaturalPacketTail
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def maskedTail {R : Type*} [Fintype R] (Λ : R → R → Type*)
    [∀ r t, Fintype (Λ r t)] (W : 𝓢(ℝ,ℂ)) (frequencies : Set O)
    (scale : (r t : R) → Λ r t → ℝ)
    (q : (r t : R) → Λ r t → O → ℂ) (a : R → ℂ) : ℂ :=
  ∑ r, ∑ t, (a r*star (a t))*
    ∑ l : Λ r t, ∑' h : frequencies,
      q r t l h.val*paperRadialFourier W (scale r t l*‖eisEmbedding h.val‖^2)

/-- Uniform Schwartz tail with the literal pair-dependent puncture labels. -/
theorem masked_radial_tail (n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {R : Type*} [Fintype R] (Λ : R → R → Type*) [∀ r t, Fintype (Λ r t)]
      (W : 𝓢(ℝ,ℂ)) (frequencies : Set O) (K₀ T Γ m : ℝ),
      0 < K₀ → 0 ≤ T → 0 ≤ Γ → 0 ≤ m →
      (∀ r t, (Fintype.card (Λ r t):ℝ) ≤ m) →
      (∀ h ∈ frequencies, T ≤ K₀*‖eisEmbedding h‖^2) →
      ∀ (scale : (r t : R) → Λ r t → ℝ), (∀ r t l, K₀ ≤ scale r t l) →
      ∀ (q : (r t : R) → Λ r t → O → ℂ),
      (∀ r t l h, h ∈ frequencies → ‖q r t l h‖ ≤ Γ) →
      ∀ a : R → ℂ,
      ‖maskedTail Λ W frequencies scale q a‖ ≤
        Γ*(Fintype.card R:ℝ)*m*(∑ r, ‖a r‖^2)*
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 K₀)^2*(1+T)^n) := by
  obtain ⟨s,C,hC,htail⟩ := CenteredMomentTail.uniform_sector_lattice_tail n
  refine ⟨s,C,hC,?_⟩
  intro R _ Λ _ W frequencies K₀ T Γ m hK hT hΓ hm hlabels hfreq scale hscale q hq a
  let budget := Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 K₀)^2*(1+T)^n)
  have hbudget : 0 ≤ budget := by
    dsimp [budget]
    exact div_nonneg (mul_nonneg hΓ (mul_nonneg hC.le (apply_nonneg _ _))) (by positivity)
  have hlabel (r t : R) (l : Λ r t) :
      ‖∑' h : frequencies, q r t l h.val*
        paperRadialFourier W (scale r t l*‖eisEmbedding h.val‖^2)‖ ≤ budget := by
    have hh := htail W frequencies K₀ T Γ hK hT hΓ hfreq
      (scale r t l) (hscale r t l) (q r t l) (fun _ => 1) (hq r t l) (by simp)
    simpa only [one_mul] using hh
  have hpair (r t : R) :
      ‖∑ l : Λ r t, ∑' h : frequencies, q r t l h.val*
        paperRadialFourier W (scale r t l*‖eisEmbedding h.val‖^2)‖ ≤ m*budget := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun l _ => hlabel r t l)).trans
      (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right (hlabels r t) hbudget))
  have hmass : (∑ r, ‖a r‖)^2 ≤ (Fintype.card R:ℝ)*(∑ r, ‖a r‖^2) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ:Finset R)
      (fun _ => (1:ℝ)) (fun r => ‖a r‖)
  unfold maskedTail
  calc
    _ ≤ ∑ r, ∑ t, ‖(a r*star (a t))*
        ∑ l : Λ r t, ∑' h : frequencies, q r t l h.val*
          paperRadialFourier W (scale r t l*‖eisEmbedding h.val‖^2)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun r _ => norm_sum_le _ _
    _ ≤ ∑ r, ∑ t, ‖a r‖*‖a t‖*(m*budget) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro t ht
      simp only [norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_left (hpair r t) (by positivity)
    _ = m*budget*(∑ r, ‖a r‖)^2 := by
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul,mul_comm,mul_assoc]
    _ ≤ m*budget*((Fintype.card R:ℝ)*(∑ r, ‖a r‖^2)) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hm hbudget)
    _ = _ := by dsimp [budget]; ring

/-- The fixed raw cutoff lies inside P≥3A+1. -/
theorem cutoff_le_source_cap (Z A P η : ℝ) (hZ : 1 ≤ Z)
    (hP : 3*A+1 ≤ P) (hη : 2*η ≤ A+1) :
    Z^(2*A+2*η) ≤ Z^P :=
  Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem cutoff_has_radial_gain (Z A η : ℝ) (hZ : 0 < Z) :
    Z^η=Z^(-(2*A+η))*Z^(2*A+2*η) := by
  rw [← Real.rpow_add hZ]
  congr 1
  ring

/-- Exact polynomial budget: increase n to strengthen the tail, retaining
the same raw cutoff and same auxiliary source cap. -/
theorem tail_power_budget (Z A P η M : ℝ) (n : ℕ) (hZ : 1 ≤ Z)
    (hA : 0 ≤ A) (hη : 0 < η)
    (hn : M+P+10*A+3*η ≤ η*(n:ℝ)) :
    Z^(P+6*A+η)/((min 1 (Z^(-(2*A+η))))^2*(1+Z^η)^n) ≤ Z^(-M) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsmall : Z^(-(2*A+η)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
  rw [min_eq_right hsmall]
  have hden : (Z^η)^n ≤ (1+Z^η)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.rpow_pos_of_pos hZ0 η]) n
  have hbound :
      Z^(P+6*A+η)/((Z^(-(2*A+η)))^2*(1+Z^η)^n) ≤
        Z^(P+6*A+η)/((Z^(-(2*A+η)))^2*(Z^η)^n) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hden (by positivity))
  apply hbound.trans
  rw [← Real.rpow_mul_natCast hZ0.le,← Real.rpow_mul_natCast hZ0.le,
    ← Real.rpow_add hZ0,← Real.rpow_sub hZ0]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  norm_num at *
  linarith

/-- Complete uniform tail consumer. The hypotheses on scale and label count
are elementary bounds for the actual mixed packet, rather than any estimate
for its oscillation. The cutoff does not depend on the desired tail power. -/
theorem polynomial_masked_tail (A P η M : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {R : Type*} [Fintype R] (Λ : R → R → Type*) [∀ r t, Fintype (Λ r t)]
      (W : 𝓢(ℝ,ℂ)) (frequencies : Set O) (Z Crows Cmask : ℝ),
      1 ≤ Z → 0 ≤ Crows → 0 ≤ Cmask →
      (Fintype.card R:ℝ) ≤ Crows*Z^(5*A) →
      (∀ r t, (Fintype.card (Λ r t):ℝ) ≤ Cmask*Z^(A+η)) →
      (∀ h ∈ frequencies, Z^(2*A+2*η) ≤ ‖eisEmbedding h‖^2) →
      ∀ (scale : (r t : R) → Λ r t → ℝ),
      (∀ r t l, Z^(-(2*A+η)) ≤ scale r t l) →
      ∀ (q : (r t : R) → Λ r t → O → ℂ),
      (∀ r t l h, h ∈ frequencies → ‖q r t l h‖ ≤ Z^P) →
      ∀ a : R → ℂ,
      ‖maskedTail Λ W frequencies scale q a‖ ≤
        C*Crows*Cmask*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          Z^(-M)*(∑ r, ‖a r‖^2) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((M+P+10*A+3*η)/η)
  have hn' : M+P+10*A+3*η ≤ η*(n:ℝ) := by
    have hh := (div_lt_iff₀ hη).mp hn
    nlinarith
  obtain ⟨s,C,hC,htail⟩ := masked_radial_tail n
  refine ⟨s,C,hC,?_⟩
  intro R _ Λ _ W frequencies Z Crows Cmask hZ hCrows hCmask hrows hlabels hfreq scale hscale q hq a
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hseminorm : 0 ≤ s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  have hmass : 0 ≤ ∑ r, ‖a r‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfreq' (h : O) (hh : h ∈ frequencies) :
      Z^η ≤ Z^(-(2*A+η))*‖eisEmbedding h‖^2 := by
    rw [cutoff_has_radial_gain Z A η hZ0]
    exact mul_le_mul_of_nonneg_left (hfreq h hh) (by positivity)
  have ht := htail Λ W frequencies (Z^(-(2*A+η))) (Z^η) (Z^P)
    (Cmask*Z^(A+η)) (by positivity) (by positivity) (by positivity)
    (by positivity) hlabels hfreq' scale hscale q hq a
  have hnum : Z^P*(Fintype.card R:ℝ)*(Cmask*Z^(A+η))*(∑ r, ‖a r‖^2)*
      (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ≤
      Z^P*(Crows*Z^(5*A))*(Cmask*Z^(A+η))*(∑ r, ‖a r‖^2)*
      (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
    gcongr
  calc
    _ ≤ Z^P*(Fintype.card R:ℝ)*(Cmask*Z^(A+η))*(∑ r, ‖a r‖^2)*
        (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (Z^(-(2*A+η))))^2*(1+Z^η)^n) := ht
    _ ≤ Z^P*(Crows*Z^(5*A))*(Cmask*Z^(A+η))*(∑ r, ‖a r‖^2)*
        (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (Z^(-(2*A+η))))^2*(1+Z^η)^n) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (C*Crows*Cmask*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(∑ r, ‖a r‖^2))*
        (Z^(P+6*A+η)/((min 1 (Z^(-(2*A+η))))^2*(1+Z^η)^n)) := by
      have hpow : Z^(P+6*A+η)=Z^P*Z^(5*A)*Z^(A+η) := by
        rw [show P+6*A+η=(P+5*A)+(A+η) by ring,
          Real.rpow_add hZ0 (P+5*A) (A+η),Real.rpow_add hZ0 P (5*A)]
      rw [hpow]
      ring
    _ ≤ (C*Crows*Cmask*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(∑ r, ‖a r‖^2))*
        Z^(-M) := mul_le_mul_of_nonneg_left
      (tail_power_budget Z A P η M n hZ hA hη hn') (by positivity)
    _ = _ := by ring

end
end Qrh.JointDetector.NaturalPacketTail

#print axioms Qrh.JointDetector.NaturalPacketTail.masked_radial_tail
#print axioms Qrh.JointDetector.NaturalPacketTail.tail_power_budget
#print axioms Qrh.JointDetector.NaturalPacketTail.polynomial_masked_tail
