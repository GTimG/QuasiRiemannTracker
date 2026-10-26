/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal first allocation polynomial pays its complete allocation count
before corrected MAIN; no modified coefficient is discarded. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstChildPolynomial
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalCorrectedMain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.WeightedEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentAddedZeroUniform
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily Record1252270103Source Record1252270103Source.Collision
open CenteredMomentSourceLiveColumn
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem actual_allocation_dyadic_energy (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R seed L : Ideal O) (τ : Character) (t T : ℝ) (n : ℤ) :
    (∑'z:O,dyadicWeight n (normValue z)*
      ‖CoupledFirst.allocatedPolynomial (original s R seed) modifier C L τ t T z‖^2)≤
      ((actualAllocations s.pools C).card:ℝ)*
        ∑B:actualAllocations s.pools C,‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
          (∑'z:O,dyadicWeight n (normValue z)*
            ‖CoupledFirst.childPolynomial s modifier C R L B τ t T z‖^2) := by
  rw [dyadic_energy_eq_sum]
  simp_rw [CoupledFirst.allocatedPolynomial_child,dyadic_energy_eq_sum]
  calc
    _≤∑z∈dyadRows n,dyadicWeight n (normValue z)*
        (((actualAllocations s.pools C).card:ℝ)*
          ∑B:actualAllocations s.pools C,‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
            ‖CoupledFirst.childPolynomial s modifier C R L B τ t T z‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (dyadicWeight_bounds n (normValue z)).1
      have hh:=norm_weighted_sum_sq (Finset.univ:Finset (actualAllocations s.pools C))
        (fun _=>1) (fun _=>1)
        (fun B=>frozenCoefficient B.val C R s.ν s.W s.P*
          CoupledFirst.childPolynomial s modifier C R L B τ t T z)
        (fun _ _=>by norm_num) (fun _ _=>by norm_num)
      simpa only [one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
        nsmul_eq_mul,mul_one,norm_mul,mul_pow] using hh
    _=_ := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro z hz
      ring

/-- Both squarefree projectors, the ordinary hole and their frozen marked
product are the actual child coefficient after common extraction. -/
theorem actual_marked_child_polynomial (s : Input ι)
    (A₁ A₂ D K C R L : Ideal O) (F : Ideal O→ℂ)
    (B : actualAllocations s.pools C) (τ : Character) (t T : ℝ) (z : O) :
    CoupledFirst.childPolynomial s (markedSourceModifier A₁ A₂ D K F) C R L B τ t T z=
      let s':=child s C R B τ t
      let S:=finiteColumns (Fintype.piFinset s'.pools)
      gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I:supportedColumns S=>
          CoupledFirst.coefficient s'
            (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
              (D*C) (K*markedProduct B.val) F) (R*C) L I*
            ((Real.sqrt T:ℂ)⁻¹*rowWeight τ fixedBadMask 1 1 t I)) z := by
  have hprod : finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2
  have hm:=funext (markedSourceModifier_common_allocation A₁ A₂ D K C F B.val hprod)
  unfold CoupledFirst.childPolynomial
  rw [hm]
  dsimp only
  have hpool : @Fintype.piFinset
      (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2) (Classical.decEq _) _
      (fun _=>Ideal O) (child s C R B τ t).pools=
      Fintype.piFinset (child s C R B τ t).pools := by
    ext v
    simp
  rw [hpool]
  unfold gaussPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_allocation_dyadic_energy
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_marked_child_polynomial
