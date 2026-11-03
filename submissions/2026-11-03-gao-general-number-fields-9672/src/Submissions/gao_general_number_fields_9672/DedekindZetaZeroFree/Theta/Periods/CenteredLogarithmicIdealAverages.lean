/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/CenteredLogarithmicIdealAverages.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.MixedThetaDefinitions
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.RayLatticePeriodization
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Units.RayUnitTorsionFibers

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

theorem mixedThetaCovolume_pos (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    0 < DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaCovolume F I := by
  have hI : 0 < FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (Units.ne_zero I)))
  have hd : 0 < |(NumberField.discr F : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  exact mul_pos (by exact_mod_cast hI) (Real.sqrt_pos.mpr hd)

def centeredLogShape (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (t : ℝ) (h : RayCoset.logHyperplane F) (v : NumberField.InfinitePlace F) : ℝ :=
  (t / DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaCovolume F I) ^
    ((Module.finrank ℚ F : ℝ)⁻¹) * Real.exp (h.val v)

theorem centeredLogShape_pos (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    {t : ℝ} (ht : 0 < t) (h : RayCoset.logHyperplane F)
    (v : NumberField.InfinitePlace F) : 0 < centeredLogShape F I t h v := by
  exact mul_pos (Real.rpow_pos_of_pos (div_pos ht (mixedThetaCovolume_pos F I)) _)
    (Real.exp_pos _)

def centeredLogIdealTheta (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (t : ℝ) (h : RayCoset.logHyperplane F) : ℂ :=
  if ht : 0 < t then
    DedekindZetaZeroFree.AbelianQuotient.Theta.fractionalShapeIdealTheta F I
      (centeredLogShape F I t h)
      (fun v => ne_of_gt (centeredLogShape_pos F I ht h v))
  else 0

def topLogIdealAverage (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) : ℂ :=
  (RayCoset.rayUnitTorsionCard F ⊤ : ℂ)⁻¹ *
    ∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ ht,
      centeredLogIdealTheta F I t h
      ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F

end DedekindZetaZeroFree.Hecke.Theta

end
