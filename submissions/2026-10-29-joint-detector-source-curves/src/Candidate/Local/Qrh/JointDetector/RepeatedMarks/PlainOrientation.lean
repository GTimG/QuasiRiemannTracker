/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ParentMarkedPlain
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryProfiles

namespace Qrh.JointDetector.RepeatedMarks.PlainOrientation
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ComplexConjugate
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open HeckeDetectorCoefficientTransfer HeckeInverseAmplification HeckeDetectorProfiles

/-- The actual positive annular detector profile is real, including outside
its positive support. -/
theorem positiveAnnular_conj : (fun x=>conj (positiveAnnular x))=positiveAnnular := by
  funext x
  by_cases hx : 0≤x
  · rw [positiveAnnular_eq x hx]
    simp [DyadicTransfer.annularCutoff,cutoff,QuadraticInitialBound.sieveCutoff_apply]
  · have hz : positiveAnnular x=0 := by
      by_contra hn
      have := (positiveAnnular_support hn).1
      linarith
    simp [hz]

theorem logProfile_positive_conj (n : ℕ) :
    (fun x=>conj (((logProfile^[n]) positiveAnnular) x))=(logProfile^[n]) positiveAnnular := by
  induction n with
  | zero => exact positiveAnnular_conj
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    funext x
    rw [←logProfile_conjugate]
    rw [ih]

theorem oriented_plain_profile (reverse : Bool) (n : ℕ) :
    orientedProfile reverse ((logProfile^[n]) positiveAnnular)=(logProfile^[n]) positiveAnnular := by
  cases reverse
  · rfl
  · exact logProfile_positive_conj n

/-- Conjugating the detector character changes its ordinary frequency only.
The original repeated slot product is kept untouched. -/
theorem pair_norm {Row : Type*} (χ ψ : Row→Character) (reverse : Bool)
    (rows : Finset Row)
    (hcoeff : ∀u∈rows,∀I,idealCoeff (χ u) I=
      if reverse then conj (idealCoeff (ψ u) I) else idealCoeff (ψ u) I)
    (Q : Row→ℂ) (j k : ℕ) (X σ freq : ℝ) (hX : 0<X)
    (u : Row) (hu : u∈rows) :
    ‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) X σ freq*
      polynomial (χ u) false ((logProfile^[k]) positiveAnnular) X σ freq*Q u‖^2 =
    ‖polynomial (ψ u) false ((logProfile^[j]) positiveAnnular) X σ (orientedFrequency reverse freq)*
      polynomial (ψ u) false ((logProfile^[k]) positiveAnnular) X σ (orientedFrequency reverse freq)*Q u‖^2 := by
  simp only [norm_mul]
  rw [norm_of_oriented_coefficients (χ u) (ψ u) reverse (hcoeff u hu) false _ X σ freq hX,
    norm_of_oriented_coefficients (χ u) (ψ u) reverse (hcoeff u hu) false _ X σ freq hX,
    oriented_plain_profile,oriented_plain_profile]

/-- Uniform actual plain raw fields transport to either detector orientation
without changing the original response or its amplitude class. -/
theorem raw_moment {Row : Type*} (χ ψ : Row→Character) (reverse : Bool)
    (rows : Finset Row)
    (hcoeff : ∀u∈rows,∀I,idealCoeff (χ u) I=
      if reverse then conj (idealCoeff (ψ u) I) else idealCoeff (ψ u) I)
    (Q : Row→ℂ) (X height bound : ℝ) (hX : 0<X)
    (hraw : ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      ∑u∈rows,‖polynomial (ψ u) false ((logProfile^[j]) positiveAnnular) X σ freq*
        polynomial (ψ u) false ((logProfile^[k]) positiveAnnular) X σ freq*Q u‖^2≤bound) :
    ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      ∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) X σ freq*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) X σ freq*Q u‖^2≤bound := by
  intro j k hjk σ hσ freq hfreq
  have hf : orientedFrequency reverse freq ∈ Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact abs_le.mpr hfreq
  have he : (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) X σ freq*
      polynomial (χ u) false ((logProfile^[k]) positiveAnnular) X σ freq*Q u‖^2)=
      ∑u∈rows,‖polynomial (ψ u) false ((logProfile^[j]) positiveAnnular) X σ (orientedFrequency reverse freq)*
      polynomial (ψ u) false ((logProfile^[k]) positiveAnnular) X σ (orientedFrequency reverse freq)*Q u‖^2 :=
    Finset.sum_congr rfl (fun u hu=>pair_norm χ ψ reverse rows hcoeff Q j k X σ freq hX u hu)
  rw [he]
  exact hraw j k hjk σ hσ _ hf

end
end Qrh.JointDetector.RepeatedMarks.PlainOrientation
#print axioms Qrh.JointDetector.RepeatedMarks.PlainOrientation.raw_moment
