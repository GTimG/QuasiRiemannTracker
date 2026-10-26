/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal corrected child rows and their inherited common-puncture invariants. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.CoupledAllocation
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SourceModifier
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.NewtonRowsActual
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentRowNorm
open CenteredMomentSourceRectangleEnergy CenteredMomentSourceRectangle CenteredMomentHeckeExpansion
open Record1252270103Source QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance restoredRowsDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The literal CA5 correction; the denominator is not bounded or replaced. -/
def poolCorrection (P : Finset (Ideal O)) (I : Ideal O) : ℂ :=
  ((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P I).card):ℝ)

theorem plain_product_dvd_tuple (B : Tuple ι) :
    B (Sum.inr 0)*B (Sum.inr 1)∣finiteTupleProduct B := by
  refine ⟨∏i,B (Sum.inl i),?_⟩
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two]
  ring

/-- Both invariants are propagated from the actual original puncture. -/
theorem puncture_invariants_allocation (A₁ A₂ D R C : Ideal O) (B : Tuple ι)
    (hA : A₁*A₂∣R) (hD : D∣R) (hB : finiteTupleProduct B=C) :
    (A₁*B (Sum.inr 0))*(A₂*B (Sum.inr 1))∣R*C ∧ D*C∣R*C := by
  have hb : B (Sum.inr 0)*B (Sum.inr 1)∣C := hB ▸ plain_product_dvd_tuple B
  constructor
  · convert mul_dvd_mul hA hb using 1 <;> ring
  · exact mul_dvd_mul hD (dvd_refl C)

def modifiedSourceRow (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (τ : Character) (t : ℝ) (z : O) : ℂ :=
  ∑v∈Fintype.piFinset s.pools,
    modifier v*profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v*
      rowWeight τ CenteredMomentSecondHeightFamily.fixedBadMask 1 z t (finiteTupleProduct v)

/-- Exact completed positive energy, with its original keep and divisor seed. -/
theorem source_energy_eq_modified_rows (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (τ : Character) (t : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed) (heightCoeff τ t) Φ H=
      ∑'z : O,if keep z then ‖modifiedSourceRow s modifier R seed τ t z‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0 := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row]
  unfold QRH.Record1252270103Source.High.CoupledFirst.coefficient
    QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient
  rw [finite_column_regroup]
  rfl

/-- Literal child inlet after common extraction. In particular D is updated
by C, while the forced seed L and every original row remain present. -/
theorem corrected_child_energy_eq_rows (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D C R L : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    childDivisorEnergy s (sourceModifier A₁ A₂ D (poolCorrection P)) C R L B τ t keep Φ H=
      ∑'z : O,if keep z then
        ‖modifiedSourceRow (child s C R B τ t)
          (sourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (D*C) (poolCorrection P))
          (R*C) L τ t z‖^2*(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0 := by
  have hb : finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2
  have hm := funext (sourceModifier_common_allocation A₁ A₂ D C (poolCorrection P) B.val hb)
  unfold childDivisorEnergy
  rw [hm]
  exact source_energy_eq_modified_rows _ _ _ _ _ _ _ _ _

end
end OAI.SevenEighths.Record1252270103Second

#print axioms OAI.SevenEighths.Record1252270103Second.puncture_invariants_allocation
#print axioms OAI.SevenEighths.Record1252270103Second.source_energy_eq_modified_rows
#print axioms OAI.SevenEighths.Record1252270103Second.corrected_child_energy_eq_rows
