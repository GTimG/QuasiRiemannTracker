/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/LogarithmicLatticeDomainSymmetries.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain

@[expose] public section

noncomputable section

open scoped NumberField Pointwise
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

theorem topLogDomainIntegral_translation (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (f : RayCoset.logHyperplane F → ℂ)
    (hperiodic : ∀ (γ : RayCoset.rayUnitLogLattice F ⊤)
      (h : RayCoset.logHyperplane F), f (h + (γ : RayCoset.logHyperplane F)) = f h) :
    ∀ d : RayCoset.logHyperplane F,
      (∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ ht, f (h + d)
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) =
      ∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ ht, f h
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F := by
  intro d
  letI := RayCoset.isZLattice_rayUnitLogLattice F ⊤ ht
  letI : VAddInvariantMeasure (RayCoset.rayUnitLogLattice F ⊤)
      (RayCoset.logHyperplane F)
      (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) :=
    ⟨fun g s hs => (measurePreserving_add_left
      (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F)
      (g : RayCoset.logHyperplane F)).measure_preimage hs.nullMeasurableSet⟩
  have hf : ∀ (γ : RayCoset.rayUnitLogLattice F ⊤) h, f (γ +ᵥ h) = f h := by
    intro γ h
    change f ((γ : RayCoset.logHyperplane F) + h) = f h
    rw [add_comm]
    exact hperiodic γ h
  have hQ := RayCoset.isAddFundamentalDomain_rayUnitHalfOpenDomain F ⊤ ht
  have hd := hQ.vadd_of_comm d
  have hi := (measurePreserving_add_left
    (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) d).setIntegral_image_emb
    (MeasurableEquiv.addLeft d).measurableEmbedding f (RayCoset.rayUnitHalfOpenDomain F ⊤ ht)
  have hi' : (∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ ht, f (h + d)
      ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) =
      ∫ h in d +ᵥ RayCoset.rayUnitHalfOpenDomain F ⊤ ht, f h
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F := by
    simpa only [← Set.image_vadd, vadd_eq_add, add_comm] using hi.symm
  exact hi'.trans (hd.setIntegral_eq hQ hf)

theorem topLogDomainIntegral_reflection (ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (f : RayCoset.logHyperplane F → ℂ)
    (hperiodic : ∀ (γ : RayCoset.rayUnitLogLattice F ⊤)
      (h : RayCoset.logHyperplane F), f (h + (γ : RayCoset.logHyperplane F)) = f h) :
    (∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ ht, f (-h)
      ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) =
    ∫ h in RayCoset.rayUnitHalfOpenDomain F ⊤ ht, f h
      ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F := by
  letI := RayCoset.isZLattice_rayUnitLogLattice F ⊤ ht
  letI : VAddInvariantMeasure (RayCoset.rayUnitLogLattice F ⊤)
      (RayCoset.logHyperplane F)
      (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) :=
    ⟨fun g s hs => (measurePreserving_add_left
      (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F)
      (g : RayCoset.logHyperplane F)).measure_preimage hs.nullMeasurableSet⟩
  have hf : ∀ (γ : RayCoset.rayUnitLogLattice F ⊤) h, f (γ +ᵥ h) = f h := by
    intro γ h
    change f ((γ : RayCoset.logHyperplane F) + h) = f h
    rw [add_comm]
    exact hperiodic γ h
  let e : RayCoset.logHyperplane F ≃ᵐ RayCoset.logHyperplane F :=
    MeasurableEquiv.neg _
  have he : MeasurePreserving e
      (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F)
      (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) :=
    Measure.measurePreserving_neg _
  have hQ := RayCoset.isAddFundamentalDomain_rayUnitHalfOpenDomain F ⊤ ht
  have hN : IsAddFundamentalDomain (RayCoset.rayUnitLogLattice F ⊤)
      (e '' RayCoset.rayUnitHalfOpenDomain F ⊤ ht)
      (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F) := by
    apply hQ.image_of_equiv e.toEquiv ?_ (Equiv.neg _) ?_
    · exact (Measure.measurePreserving_neg
        (DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F)).quasiMeasurePreserving
    · intro γ h
      change -(-(γ : RayCoset.logHyperplane F) + h) =
        (γ : RayCoset.logHyperplane F) + -h
      simp [add_comm]
  calc
    _ = ∫ h in e '' RayCoset.rayUnitHalfOpenDomain F ⊤ ht, f h
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F :=
      (he.setIntegral_image_emb e.measurableEmbedding f
        (RayCoset.rayUnitHalfOpenDomain F ⊤ ht)).symm
    _ = _ := hN.setIntegral_eq hQ hf

end DedekindZetaZeroFree.Hecke.Theta

end
