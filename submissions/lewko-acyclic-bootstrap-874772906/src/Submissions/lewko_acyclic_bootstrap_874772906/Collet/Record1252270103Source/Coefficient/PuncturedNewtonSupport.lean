/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original puncture supplies Newton coprimality only on surviving character
terms. The strict pole bound follows from the actual residual count and budget. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.CorrectedRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CenteredMomentHeckeExpansion
open CenteredMomentSourceRectangleMask CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily
open QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O

theorem punctured_row_nonzero_coprime (η : Character) (R I : Ideal O) (A z : O) (t : ℝ)
    (hne : rowWeight η (fixedBadMask*idealGenerator R) A z t I≠0) : IsCoprime I R := by
  by_contra h
  have he := rowWeight_ideal_mask η fixedBadMask A z t (dvd_mul_right _ _) (dvd_mul_left _ _) R I
  rw [if_neg h,zero_mul] at he
  exact hne he.symm

theorem punctured_newton_support (η : Character) (R D M I J : Ideal O)
    (hDR : D∣R) (A z : O) (t : ℝ)
    (hM : rowWeight η (fixedBadMask*idealGenerator R) A z t M≠0)
    (hIJ : rowWeight η (fixedBadMask*idealGenerator R) A z t (I*J)≠0)
    (P : Finset (Ideal O)) (depth : ℕ) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,¬p∣M) (hcount : (idealDividingPool P (I*J)).card≤depth)
    (hbudget : 2*((idealDividingPool P D).card+depth+1:ℝ)≤P.card) :
    IsCoprime D (M*I*J) ∧ (idealDividingPool P (I*J)).card≤depth ∧
      (idealDividingPool P (D*(M*I*J))).card<P.card := by
  have hrow : rowWeight η (fixedBadMask*idealGenerator R) A z t (M*I*J)≠0 := by
    simpa only [mul_assoc,map_mul] using mul_ne_zero hM hIJ
  have hc : IsCoprime D (M*I*J) :=
    (punctured_row_nonzero_coprime η R _ A z t hrow).symm.of_isCoprime_of_dvd_left hDR
  refine ⟨hc,hcount,?_⟩
  rw [ideal_dividing_pool_count P D (M*I*J) hp hc,
    ideal_dividing_pool_drop_marked P M I J hp havoid]
  have hb : 2*((idealDividingPool P D).card+depth+1)≤P.card := by exact_mod_cast hbudget
  omega

theorem input_pool_avoids_marked {ι : Type*} [Fintype ι] (s : Input ι)
    (P : Finset (Ideal O)) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,∀i I,I∈s.slots i→¬p∣I) (v : ∀i,s.slots i) :
    ∀p∈P,¬p∣∏i,(v i:Ideal O) := by
  intro p hpin
  apply (hp p hpin).not_dvd_finsetProd
  intro i hi
  exact havoid p hpin i (v i) (v i).property

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.punctured_newton_support
#print axioms OAI.SevenEighths.Record1252270103Source.input_pool_avoids_marked
