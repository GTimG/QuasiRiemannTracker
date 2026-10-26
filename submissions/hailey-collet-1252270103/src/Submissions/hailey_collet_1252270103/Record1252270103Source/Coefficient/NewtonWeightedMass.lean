/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual ideal norms and character zeros in the finite Newton allocation mass.
This controls both the central exponent1/2 and centered exponent501/1000. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.NewtonMass
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.FiniteReindex

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103KernelMass
local notation "O" => ActualEisensteinCubic.O

theorem newton_assignment_weighted_mass (P : Finset (Ideal O))
    (hP : 0<P.card) (hnz : ∀p∈P,p≠0) (r σ : ℝ) (R : ℕ)
    (hσ : 0≤σ) (hbudget : 2*(r+R+1)≤P.card)
    (ψ : Ideal O→ℂ) (hψ : ∀I,‖ψ I‖≤1) :
    (∑j∈Finset.range (R+1),∑S∈P.powersetCard j,∑A∈S.powerset,
      ‖(newtonCoefficient P.card r S.card:ℂ)*ψ ((∏p∈A,p)*(∏p∈S\A,p))‖/
        ((Ideal.absNorm (∏p∈A,p):ℝ)*(Ideal.absNorm (∏p∈S\A,p):ℝ))^σ)≤newtonMassBound R := by
  apply le_trans _ (newton_total_mass P r R hP hbudget)
  apply Finset.sum_le_sum
  intro j hj
  have hjR : (j:ℝ)≤R:=by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  apply Finset.sum_le_sum
  intro S hS
  obtain ⟨hSP,hSj⟩:=Finset.mem_powersetCard.mp hS
  have hPpos : (0:ℝ)<P.card:=Nat.cast_pos.mpr hP
  have hc : 0≤newtonCoefficient P.card r S.card:=
    newtonCoefficient_nonneg _ _ _ hPpos.le (by rw [hSj];linarith)
  calc
    _≤∑A∈S.powerset,newtonCoefficient P.card r S.card := by
      apply Finset.sum_le_sum
      intro A hA
      have hAS:=Finset.mem_powerset.mp hA
      have h₁ : (∏p∈A,p)≠0:=Finset.prod_ne_zero_iff.mpr (fun p hp=>hnz p (hSP (hAS hp)))
      have h₂ : (∏p∈S\A,p)≠0:=Finset.prod_ne_zero_iff.mpr (fun p hp=>hnz p (hSP (Finset.mem_sdiff.mp hp).1))
      have hbase : (1:ℝ)≤(Ideal.absNorm (∏p∈A,p):ℝ)*(Ideal.absNorm (∏p∈S\A,p):ℝ):=
        one_le_mul_of_one_le_of_one_le (ideal_norm_one_le h₁) (ideal_norm_one_le h₂)
      have hw : ‖(newtonCoefficient P.card r S.card:ℂ)*ψ ((∏p∈A,p)*(∏p∈S\A,p))‖≤
          newtonCoefficient P.card r S.card := by
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hc]
        exact mul_le_of_le_one_right hc (hψ _)
      exact (div_le_self (norm_nonneg _) (Real.one_le_rpow hbase hσ)).trans hw
    _=newtonCoefficient P.card r S.card*2^S.card := by
      rw [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul]
      push_cast
      ring

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.newton_assignment_weighted_mass
