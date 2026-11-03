/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/LogarithmicAverageClassInvariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.LogarithmicAngularCoordinates
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Haar.LogarithmicLatticeDomainSymmetries
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.PrincipalIdealCenteredShapeCovariance

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

private theorem principal_of_class_top
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hclass : ClassGroup.mk F I = ClassGroup.mk F J) :
    ∃ a : Fˣ, (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F) := by
  have hq := congrArg (ClassGroup.equiv F) hclass
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_monoidHom_refl] at hq
  have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range I =
      QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range J := hq
  rw [QuotientGroup.mk'_eq_mk'] at hq'
  rcases hq' with ⟨a, ⟨b, rfl⟩, ha⟩
  refine ⟨b, ?_⟩
  simpa only [Units.val_mul, coe_toPrincipalIdeal, mul_comm] using
    (congrArg (fun U : (FractionalIdeal (𝓞 F)⁰ F)ˣ => (U : FractionalIdeal (𝓞 F)⁰ F)) ha).symm

theorem topLogIdealAverage_class_invariant
    (htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t)
    (hclass : ClassGroup.mk F I = ClassGroup.mk F J) :
    topLogIdealAverage F htop I t = topLogIdealAverage F htop J t := by
  classical
  obtain ⟨a, ha⟩ := principal_of_class_top F I J hclass
  obtain ⟨d, hd⟩ := DedekindZetaZeroFree.Hecke.principalCenteredShapeCovariance F I J a ha
  have hpoint : ∀ h : RayCoset.logHyperplane F,
      centeredLogIdealTheta F J t h =
        centeredLogIdealTheta F I t (h + (logAngularEquiv F).symm d) := by
    intro h
    rw [centeredLogIdealTheta_eq_mixedRadialTheta F J t ht h,
      centeredLogIdealTheta_eq_mixedRadialTheta F I t ht
        (h + (logAngularEquiv F).symm d),
      hd t ht (logAngularEquiv F h)]
    congr 1
    simp [map_add]
  have hint :
      (∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ htop, centeredLogIdealTheta F J t h
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) =
      ∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ htop, centeredLogIdealTheta F I t h
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F := by
    rw [show (∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ htop, centeredLogIdealTheta F J t h
          ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) =
        ∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ htop,
          centeredLogIdealTheta F I t (h + (logAngularEquiv F).symm d)
          ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F from
      integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    exact topLogDomainIntegral_translation F htop
      (fun h => centeredLogIdealTheta F I t h)
      (fun γ h => centeredLogIdealTheta_rayUnit_periodic F I t ht γ h)
      ((logAngularEquiv F).symm d)
  unfold topLogIdealAverage
  rw [hint]

theorem topLogIdealAverage_reflection
    (htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    (RayCoset.rayUnitTorsionCard F ⊤ : ℂ)⁻¹ *
      (∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ htop,
        centeredLogIdealTheta F I t (-h)
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) =
      topLogIdealAverage F htop I t := by
  unfold topLogIdealAverage
  rw [topLogDomainIntegral_reflection F htop
    (fun h => centeredLogIdealTheta F I t h)
    (fun γ h => centeredLogIdealTheta_rayUnit_periodic F I t ht γ h)]

end DedekindZetaZeroFree.Hecke.Theta

end
