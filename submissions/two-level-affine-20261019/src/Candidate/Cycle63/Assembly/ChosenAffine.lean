import Candidate.Cycle63.Assembly.MeshChoice
import Candidate.Cycle63.Numerator.Finite.Bridge

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open OAI.SevenEighths

/-- The genuine initial affine theorem is needed for one fixed choice of data. -/
def ChosenAffineInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
    ∃A : ChosenData,Numerator.Source.ActualAffineInput A

theorem chosen_finite_numerator_of_affine (hinput : ChosenAffineInput) :
    ChosenFiniteNumeratorInput := by
  intro hβ
  obtain ⟨A,hAffine⟩:=hinput hβ
  obtain ⟨J,hJ,hfinite⟩:=FiniteNumerator.fixed_numerator_of_affine hβ A hAffine
  exact ⟨A,J,hJ,hfinite⟩

theorem common_probe_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : ChosenAffineInput) :
    WeightedQRH.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_finite_numerator hdet (chosen_finite_numerator_of_affine hinput)

theorem beta_le_theta_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤Arithmetic.theta :=
  WeightedQRH.beta_le_of_common_probe Assembly.theta_gt_half.le Assembly.theta_lt_seven_eighths.le
    (common_probe_of_chosen_affine hdet hinput)

theorem hecke_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : ChosenAffineInput)
    (χ : HeckeFamily.Character) (s : ℂ) (hs : Arithmetic.theta<s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : HeckeFamily.LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_theta_of_chosen_affine hdet hinput).trans_lt hs) hpole

theorem dirichlet_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : ChosenAffineInput)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : Arithmetic.theta<s.re) (hexc : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  WeightedQRH.dirichlet_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) χ s hs hexc

/-- Mathlib's total zeta convention includes its nonzero value at 1. -/
theorem riemannZeta_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) : riemannZeta s≠0 :=
  WeightedQRH.zeta_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) s hs

/-- The classical zeta region explicitly excludes the pole. -/
theorem zeta_nonzero_off_pole_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) (_hpole : s≠1) : riemannZeta s≠0 :=
  riemannZeta_nonzero_of_chosen_affine hdet hinput s hs
end
end Cycle63.FinalAssembly
