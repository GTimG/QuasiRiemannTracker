/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/ZeroDetection/Conductors/Poisson/DenominatorExistence.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RawDenominatorExistence

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem rawDeletionSet_finite (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A) :
    (RawHeckeRows.rawDeletionSet U).Finite := by
  unfold RawHeckeRows.rawDeletionSet
  apply Set.Finite.union R.A.Sf.finite_toSet
  let s : Finset (Ideal (𝓞 F)) :=
    (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).toFinset
  have hinj : Function.Injective
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
  have hsub : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | U.ideal.val ≤ v.asIdeal} ⊆
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.asIdeal) ⁻¹'
        (↑s : Set (Ideal (𝓞 F))) := by
    intro v hv
    simp only [Set.mem_preimage, Finset.mem_coe]
    exact Multiset.mem_toFinset.mpr
      ((Ideal.mem_normalizedFactors_iff U.ideal.property.1).mpr ⟨v.isPrime, hv⟩)
  exact (s.finite_toSet.preimage hinj.injOn).subset hsub

theorem Sf_subset_rawDeletionSet (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A) :
    (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆
      RawHeckeRows.rawDeletionSet U := by
  unfold RawHeckeRows.rawDeletionSet
  exact Set.subset_union_left

theorem raw_denominator_existence (R : PrincipalMellin.ActualRecipe S η) :
    ∃ ω : Frequency R → Detector.PrimitiveFrequencyCharacter F,
      (∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
        U.u = u.val.val → ∀ I : R.A.Exterior,
          AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
            Detector.deletedPrimitiveIdealCoefficient F (ω u)
              (RawHeckeRows.rawDeletionSet U) I.val) ∧
      (∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
        U.u = u.val.val → ∀ ν : Detector.PrimitiveFrequencyCharacter F,
          (∀ I : R.A.Exterior,
            AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
              Detector.deletedPrimitiveIdealCoefficient F ν
                (RawHeckeRows.rawDeletionSet U) I.val) → ν = ω u) ∧
      (∀ u v : Frequency R, Detector.samePrimitiveFrequencyCharacter F (ω u) (ω v) → u = v) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ u : Frequency R,
        (Ideal.absNorm (ω u).conductor : ℝ) ≤ c * frequencyNorm R u) := by
  classical
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    by_contra hout
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six R.A v hout)
  obtain ⟨V, e, he, hnorm⟩ :=
    MinusArithmetic.actual_detector_frequency_representatives R
  obtain ⟨K⟩ := Detector.kummer_frequency_family_exists F R.A.zeta12
    R.A.primitive_zeta12 R.σ (R.A.Sf : Set _) R.A.Sf.finite_toSet hSix V
  obtain ⟨η0, hη0, _, htarget⟩ := MinusArithmetic.target_primitive_inducer R
  obtain ⟨T, hT⟩ :=
    MinusArithmetic.raw_minus_family_identification R V e he K η0 hη0 htarget
  obtain ⟨c, hc, hbound⟩ := Detector.frequency_denominator_conductor_bound F
    R.A.zeta12 R.A.primitive_zeta12 R.σ (R.A.Sf : Set _)
    R.A.Sf.finite_toSet hSix η0 hη0
  refine ⟨fun u => T.denominator (e u), hT, ?_, ?_, c, hc, ?_⟩
  · intro u U hU ν hν
    exact MinusArithmetic.deleted_primitive_inducers_eq R.A
      (RawHeckeRows.rawDeletionSet U) (rawDeletionSet_finite R U)
      (Sf_subset_rawDeletionSet R U)
      ν (T.denominator (e u)) (fun I => (hν I).symm.trans (hT u U hU I))
  · intro u v h
    exact e.injective (Detector.twisted_frequency_character_injective F R.A.zeta12
      R.A.primitive_zeta12 R.σ (R.A.Sf : Set _) R.A.Sf.finite_toSet hSix V K η0 T
      (e u) (e v) h)
  · intro u
    rw [← hnorm u]
    exact hbound V K T (e u)

end

end DedekindZetaZeroFree.Quantitative.RawDenominatorExistence

end Refinement9672
