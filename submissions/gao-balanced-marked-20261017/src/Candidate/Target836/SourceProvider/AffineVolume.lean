import Candidate.Target836.SourceProvider.CellGeometry
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
set_option autoImplicit false
namespace Target874836.SourceProvider.Physical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional Cycle63InitialSource ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM ≤ H)
theorem affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z n₁ n₂ slots : ℝ)
    (hvolume : Real.logb Z (volume s)=n₁+n₂+slots)
    (hslots : (17/500:ℝ) ≤ slots ∧ slots ≤ 1/25)
    (hcone : n₁+n₂+Named.lam*slots ≤ Named.B) :
    Real.logb Z (volume s) ≤ Named.total
      (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell slots)) := by
  have hh:=Target874836.SourceProvider.normalized_cell_bounds (M:=1) (n₁:=n₁) (n₂:=n₂)
    (z:=slots) (by norm_num) (by simpa only [mul_one] using hslots)
    (by simpa only [mul_one] using hcone)
  simpa only [div_one,one_mul,hvolume] using hh.2.2.2.1

/-- The canonical-cell ledger applied to the literal affine input; the
volume identity is proved here, rather than supplied as a source premise. -/
theorem actual_affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (θ : ι→RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hZ : 1<Z)
    (hlo₁ : (41/100:ℝ) ≤ length Z X₁) (hlo₂ : (41/100:ℝ) ≤ length Z X₂)
    (hslots : (17/500:ℝ) ≤ ∑i,w i ∧ (∑i,w i) ≤ 1/25)
    (hcone : length Z X₁+length Z X₂+Named.lam*(∑i,w i) ≤ Named.B) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    Real.logb Z (volume inp) ≤ Named.total
      (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i))) := by
  intro inp
  apply affine_exceptional_volume_cell inp Z (length Z X₁) (length Z X₂) (∑i,w i) _ hslots hcone
  exact affine_volume_log_exact rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂ hZ
    (by norm_num) (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hlo₂)

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.actual_affine_exceptional_volume_cell
