import Candidate.Cycle62.Assembly.MeshChoice
import Candidate.Cycle62.Numerator.Finite.Bridge

set_option autoImplicit false
namespace Cycle62.FinalAssembly
noncomputable section
open OAI.SevenEighths

/-- The genuine initial affine theorem is needed for one fixed choice of data. -/
def ChosenAffineInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
    ∃A : ChosenData,Numerator.Source.ActualAffineInput A

/-- An analytic mesh cap is chosen before constructing slots and source data. -/
def MeshAffineInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
    ∃meshCap : ℝ,0 < meshCap ∧ ∀A : ChosenData,A.P.mesh ≤ meshCap →
      Numerator.Source.ActualAffineInput A

theorem chosen_affine_of_mesh (hinput : MeshAffineInput) : ChosenAffineInput := by
  intro hβ
  obtain ⟨meshCap,hmesh,haffine⟩:=hinput hβ
  obtain ⟨A,hA⟩:=exists_chosen_data_with_mesh hβ hmesh
  exact ⟨A,haffine A hA⟩

theorem chosen_finite_numerator_of_affine (hinput : ChosenAffineInput) :
    ChosenFiniteNumeratorInput := by
  intro hβ
  obtain ⟨A,hAffine⟩:=hinput hβ
  obtain ⟨J,hJ,hfinite⟩:=FiniteNumerator.fixed_numerator_of_affine hβ A hAffine
  exact ⟨A,J,hJ,hfinite⟩

theorem common_probe_of_chosen_affine (hinput : ChosenAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_finite_numerator (chosen_finite_numerator_of_affine hinput)

theorem common_probe_of_mesh_affine (hinput : MeshAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_affine (chosen_affine_of_mesh hinput)

theorem beta_le_theta_of_chosen_affine (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤Arithmetic.theta :=
  Cycle25.beta_le_of_common_probe Assembly.theta_gt_half.le Assembly.theta_lt_seven_eighths.le
    (common_probe_of_chosen_affine hinput)

theorem beta_le_rational_of_chosen_affine (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤(437429/500000:ℝ) :=
  beta_le_theta_of_chosen_affine hinput

theorem hecke_nonzero_of_chosen_affine (hinput : ChosenAffineInput)
    (χ : HeckeFamily.Character) (s : ℂ) (hs : Arithmetic.theta<s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : HeckeFamily.LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_theta_of_chosen_affine hinput).trans_lt hs) hpole

theorem dirichlet_nonzero_of_chosen_affine (hinput : ChosenAffineInput)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : Arithmetic.theta<s.re) (hexc : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  Cycle25.dirichlet_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hinput) χ s hs hexc

/-- Mathlib's total zeta convention includes its nonzero value at 1. -/
theorem riemannZeta_nonzero_of_chosen_affine (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) : riemannZeta s≠0 :=
  Cycle25.zeta_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hinput) s hs

/-- The classical zeta region explicitly excludes the pole. -/
theorem zeta_nonzero_off_pole_of_chosen_affine (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) (_hpole : s≠1) : riemannZeta s≠0 :=
  riemannZeta_nonzero_of_chosen_affine hinput s hs
end
end Cycle62.FinalAssembly

#print axioms Cycle62.FinalAssembly.chosen_affine_of_mesh
#print axioms Cycle62.FinalAssembly.chosen_finite_numerator_of_affine
#print axioms Cycle62.FinalAssembly.common_probe_of_chosen_affine
#print axioms Cycle62.FinalAssembly.common_probe_of_mesh_affine
#print axioms Cycle62.FinalAssembly.beta_le_theta_of_chosen_affine
#print axioms Cycle62.FinalAssembly.beta_le_rational_of_chosen_affine
#print axioms Cycle62.FinalAssembly.hecke_nonzero_of_chosen_affine
#print axioms Cycle62.FinalAssembly.dirichlet_nonzero_of_chosen_affine
#print axioms Cycle62.FinalAssembly.riemannZeta_nonzero_of_chosen_affine
#print axioms Cycle62.FinalAssembly.zeta_nonzero_off_pole_of_chosen_affine
