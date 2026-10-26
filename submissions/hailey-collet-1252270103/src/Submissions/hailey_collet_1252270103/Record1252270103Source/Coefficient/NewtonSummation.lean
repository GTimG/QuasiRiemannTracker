/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal filtered Newton sum has the checked fixed-depth mass, including
the central normalization and the actual norm of each cofactor. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.NewtonWeightedMass
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FrozenSource
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CorrectedCenteredRows

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open QRH.Record1252270103KernelMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => ActualEisensteinCubic.O

theorem sum_powerset_card_le {ι : Type*} (P : Finset ι) (R : ℕ) (f : Finset ι→ℝ) :
    (∑S∈P.powerset.filter (fun S=>S.card≤R),f S)=
      ∑j∈Finset.range (R+1),∑S∈P.powersetCard j,f S := by
  have h := Finset.sum_fiberwise_eq_sum_filter P.powerset (Finset.range (R+1)) Finset.card f
  simpa only [Finset.mem_range,Nat.lt_succ_iff,Finset.powersetCard_eq_filter] using h.symm

theorem newton_filtered_weighted_mass (P : Finset (Ideal O))
    (hP : 0<P.card) (hnz : ∀p∈P,p≠0) (r σ : ℝ) (R : ℕ)
    (hσ : 0≤σ) (hbudget : 2*(r+R+1)≤P.card)
    (ψ : Ideal O→ℂ) (hψ : ∀I,‖ψ I‖≤1) :
    (∑S∈P.powerset.filter (fun S=>S.card≤R),∑A∈S.powerset,
      ‖(newtonCoefficient P.card r S.card:ℂ)*ψ ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)‖/
        (pairNorm (newtonDivisorPair S A))^σ)≤newtonMassBound R := by
  rw [sum_powerset_card_le]
  exact newton_assignment_weighted_mass P hP hnz r σ R hσ hbudget ψ hψ

theorem normalized_centered_child_term (d₁ d₂ T L α C : ℝ) (w v : ℂ)
    (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hT : 0<T) (hL : 0<L)
    (hv : ‖v‖≤C*Real.sqrt (T/(d₁*d₂))*(L/(d₁*d₂))^(-α)) :
    ‖(w/(Real.sqrt (d₁*d₂):ℂ))*v‖≤
      (C*Real.sqrt T*L^(-α))*(‖w‖/(d₁*d₂)^(1-α)) := by
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hv (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).trans_eq
  calc
    _=(‖w‖*C)*((Real.sqrt (d₁*d₂))⁻¹*
        (Real.sqrt (T/(d₁*d₂))*(L/(d₁*d₂))^(-α))) := by ring
    _=_ := by rw [centered_divisor_scalar T L (d₁*d₂) α hT hL (mul_pos hd₁ hd₂)];ring

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.newton_filtered_weighted_mass
#print axioms OAI.SevenEighths.Record1252270103Source.normalized_centered_child_term
