/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified second child rows with the original parent normalization.
The volume ratio is an equality, not a contraction of a modified coefficient. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.Projector
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceRectangle CenteredMomentHeckeColumnWindow
open Record1252270103Source Record1252270103Second Collision
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance secondChildRowsSumDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem modified_child_plain_row (s : Input ι) (modifier : Tuple ι→ℂ) (C R L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t T : ℝ) (z : O) :
    modifiedChildPlain s modifier C R L B τ t T z=
      (Real.sqrt T:ℂ)⁻¹*modifiedSourceRow (child s C R B τ t)
        (pulledModifier B.val modifier) (R*C) L τ t z := by
  dsimp only [modifiedChildPlain]
  rw [height_source_row]
  unfold CoupledFirst.coefficient CoupledFirst.tupleCoefficient
  rw [finite_column_regroup]
  rfl

lemma normalized_row_volume_ratio (x : ℂ) (T V : ℝ) (hT : 0<T) (hV : 0<V) :
    ‖(Real.sqrt T:ℂ)⁻¹*x‖^2=(V/T)*‖(Real.sqrt V:ℂ)⁻¹*x‖^2 := by
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt hT.le,Real.sq_sqrt hV.le]
  field_simp

theorem modified_child_normalized_row (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R L : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t T : ℝ) (hT : 0<T) (z : O) :
    let s':=child s C R B τ t
    ‖modifiedChildPlain s modifier C R L B τ t T z‖^2=
      (volume s'/T)*‖(Real.sqrt (volume s'):ℂ)⁻¹*
        modifiedSourceRow s' (pulledModifier B.val modifier) (R*C) L τ t z‖^2 := by
  rw [modified_child_plain_row]
  exact normalized_row_volume_ratio _ T _ hT (volume_pos _)

theorem marked_child_normalized_row (s : Input ι) (A₁ A₂ D K C R L : Ideal O)
    (F : Ideal O→ℂ) (B : actualAllocations s.pools C)
    (τ : Character) (t T : ℝ) (hT : 0<T) (z : O) :
    let s':=child s C R B τ t
    ‖modifiedChildPlain s (markedSourceModifier A₁ A₂ D K F) C R L B τ t T z‖^2=
      (volume s'/T)*‖(Real.sqrt (volume s'):ℂ)⁻¹*modifiedSourceRow s'
        (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
          (D*C) (K*markedProduct B.val) F) (R*C) L τ t z‖^2 := by
  rw [modified_child_normalized_row s (markedSourceModifier A₁ A₂ D K F) C R L B τ t T hT z]
  rw [funext (markedSourceModifier_common_allocation A₁ A₂ D K C F B.val
    (Finset.mem_filter.mp B.property).2)]

/-- The exact second common extraction reaches the literal fully normalized
child rows, with both the original frozen coefficient and volume ratio. -/
theorem marked_plain_allocation_rows (s : Input ι) (A₁ A₂ D K C R seed L : Ideal O)
    (F : Ideal O→ℂ) (hC : Supported C) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (z : O) :
    ‖modifiedPlainColumn s (markedSourceModifier A₁ A₂ D K F) C hC R seed L τ t z‖^2≤
      ((actualAllocations s.pools C).card:ℝ)*∑B:actualAllocations s.pools C,
        ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
          ((volume (child s C R B τ t)/volume s)*
            ‖(Real.sqrt (volume (child s C R B τ t)):ℂ)⁻¹*
              modifiedSourceRow (child s C R B τ t)
                (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
                  (D*C) (K*markedProduct B.val) F) (R*C) L τ t z‖^2) := by
  have hh:=modified_plain_allocation_bound s (markedSourceModifier A₁ A₂ D K F)
    C hC R seed L hseed τ t z
  simpa only [marked_child_normalized_row s A₁ A₂ D K C R L F _ τ t (volume s) (volume_pos s) z] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_child_plain_row
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.normalized_row_volume_ratio
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_child_normalized_row
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_child_normalized_row
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_plain_allocation_rows
