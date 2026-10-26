/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Sum the exact normalized Newton children in the original centered row. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.NewtonFrozenGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredZeroRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103KernelMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => ActualEisensteinCubic.O

theorem newton_centered_norm_bound (P : Finset (Ideal O)) (D M A₁ A₂ : Ideal O) (depth : ℕ)
    (ψ : Ideal O→*₀ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ T L α C : ℝ)
    (hT : 0<T) (hL : 0<L) (hα : α≤1) (hC : 0≤C)
    (hP : 0<P.card) (hp : ∀p∈P,Prime p) (hN : ∀p∈P,16≤p.absNorm)
    (hψ : ∀I,‖ψ I‖≤1) (havoid : ∀p∈P,¬p∣M)
    (hbudget : 2*((idealDividingPool P D).card+depth+1:ℝ)≤P.card)
    (hsupport : ∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
      frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→ ψ (n.1*n.2)≠0→
      IsCoprime D (M*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*(M*n.1*n.2))).card<P.card)
    (hchild : ∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,
      let d:=newtonDivisorPair S A
      ‖frozenCenteredRow ψ W₁ W₂ (A₁*d.1) (A₂*d.2) b
        (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) (T/pairNorm d)‖≤
        C*Real.sqrt (T/pairNorm d)*(L/pairNorm d)^(-α)) :
    ‖correctedCenteredRow P D M A₁ A₂ ψ W₁ W₂ b X₁ X₂ Y₁ Y₂ T‖≤
      C*Real.sqrt T*L^(-α)*newtonMassBound depth := by
  let E:=P.powerset.filter (fun S=>S.card≤depth)
  let w:=fun (S A : Finset (Ideal O))=>
    (newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
      ψ ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)
  let f:=fun (S A : Finset (Ideal O))=>
    frozenCenteredRow ψ W₁ W₂ (A₁*(newtonDivisorPair S A).1) (A₂*(newtonDivisorPair S A).2) b
      (X₁/(newtonDivisorPair S A).1.absNorm) (X₂/(newtonDivisorPair S A).2.absNorm)
      (Y₁/(newtonDivisorPair S A).1.absNorm) (Y₂/(newtonDivisorPair S A).2.absNorm)
      (T/pairNorm (newtonDivisorPair S A))
  have hmass : (∑S∈E,∑A∈S.powerset,‖w S A‖/(pairNorm (newtonDivisorPair S A))^(1-α))≤
      newtonMassBound depth := newton_filtered_weighted_mass P hP
        (fun p hp'=>(hp p hp').ne_zero) (idealDividingPool P D).card (1-α) depth
          (by linarith) hbudget ψ hψ
  rw [normalized_centered_newton_nonzero P D M A₁ A₂ depth ψ W₁ W₂ b X₁ X₂ Y₁ Y₂ T hT hp hN havoid hsupport]
  change ‖∑S∈E,∑A∈S.powerset,(w S A/(Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*f S A‖≤_
  apply (norm_sum_le _ _).trans
  calc
    _≤∑S∈E,∑A∈S.powerset,‖(w S A/(Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*f S A‖ :=
      Finset.sum_le_sum (fun S _=>norm_sum_le _ _)
    _≤(C*Real.sqrt T*L^(-α))*(∑S∈E,∑A∈S.powerset,
        ‖w S A‖/(pairNorm (newtonDivisorPair S A))^(1-α)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro S hS
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro A hA
      have hd:=newton_divisor_pair_good P S A
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) (Finset.mem_powerset.mp hA) hp hN
      exact normalized_centered_child_term _ _ T L α C (w S A) (f S A)
        (zero_lt_one.trans_le (ideal_norm_one_le hd.1))
        (zero_lt_one.trans_le (ideal_norm_one_le hd.2.1)) hT hL (hchild S hS A hA)
    _≤_ := mul_le_mul_of_nonneg_left hmass (by positivity)

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.newton_centered_norm_bound
