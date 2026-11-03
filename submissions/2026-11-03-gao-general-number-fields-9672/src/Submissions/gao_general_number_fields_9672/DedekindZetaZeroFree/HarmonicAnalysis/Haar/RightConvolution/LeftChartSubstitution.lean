/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/RightConvolution/LeftChartSubstitution.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.GaussChartBumps

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.RightConvolution
open MeasureTheory
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

theorem left_chart_substitution
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μL : Measure (L F)) [μL.IsHaarMeasure]
    (q : L F → ℝ) (v : G F ζ hζ → ℂ)
    (b : L F) (c : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)
    (z : X F) :
    (∫ a : L F, (q a : ℂ) * v
      ((KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z *
        (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ b * c.val)) *
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) ∂μL) =
    ∫ y : L F, (q (b⁻¹ * (ell F z)⁻¹ * y) : ℂ) *
      v (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ y * c.val) ∂μL := by
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ

  have hchart : KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (ell F z) := by
    rw [KPLiteralChamber.left_insertion F ζ hζ z]
    rfl

  have hmul (a : L F) :
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (ell F z * b * a) * c.val =
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z *
        (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ b * c.val)) *
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a := by
    have hh : (ell F z * b * a, c) = ((ell F z, 1) * (b, c)) * (a, 1) := by simp
    have hm := congrArg e hh
    change e (ell F z * b * a, c) = e (((ell F z, 1) * (b, c)) * (a, 1)) at hm
    rw [map_mul, map_mul, he, he, he, he] at hm
    simpa only [Subgroup.coe_one, mul_one, hchart] using hm
  let f : L F → ℂ := fun y => (q (b⁻¹ * (ell F z)⁻¹ * y) : ℂ) *
    v (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ y * c.val)
  have hT : b⁻¹ * (ell F z)⁻¹ = (ell F z * b)⁻¹ := (mul_inv_rev _ _).symm
  have hi := integral_mul_left_eq_self (μ := μL) f (ell F z * b)
  change (∫ a, (q a : ℂ) * v
    ((KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z *
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ b * c.val)) *
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) ∂μL) = ∫ y, f y ∂μL
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with a
  dsimp [f]
  rw [hT, inv_mul_cancel_left, ← hmul a]

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.RightConvolution

end
