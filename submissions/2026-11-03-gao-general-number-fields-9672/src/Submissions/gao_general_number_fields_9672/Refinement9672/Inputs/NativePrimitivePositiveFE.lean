/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Noncircular successor input module, 2026-11-03, Zhongpai Gao with AI assistance.
Apache-2.0. Original theorem/dependency attribution below is retained.
Input module paths are relocated only; declaration namespaces stay original.
The old Hecke endpoint is supplied from the disjoint frozen original proof DAG.
Full native-import checking and successor endpoint verification remain pending.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.Inputs.NativePrimitiveLine97
public import Submissions.gao_general_number_fields_9672.Refinement9672.Inputs.NativeGammaPositiveReflection
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterConjugation

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrimitivePositiveFE

noncomputable section
open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem reciprocal_eq_inv_completion (m : Ideal (𝓞 F)) (s : ℂ) :
    heckeReciprocalCompletionFactor F m s = (heckeCompletionFactor F m s)⁻¹ := by
  have hc : (heckeConductorScale F m : ℂ) =
      (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) := by
    unfold heckeConductorScale
    rw [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]
  unfold heckeReciprocalCompletionFactor heckeCompletionFactor
  rw [← hc]
  simp only [mul_inv, inv_pow]
  congr 1
  rw [show -s / 2 = -(s / 2) by ring, Complex.cpow_neg]

def dualEntire {m : Ideal (𝓞 F)} {η : RayClassCharacter F m}
    (D : NonprincipalRayHeckeData F m η) (s : ℂ) : ℂ :=
  heckeReciprocalCompletionFactor F m s * D.Λdual s

theorem dualEntire_differentiable {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    {η : RayClassCharacter F m} (D : NonprincipalRayHeckeData F m η) :
    Differentiable ℂ (dualEntire D) :=
  (heckeReciprocalCompletionFactor_differentiable F m hm).mul D.Λdual_entire

theorem dualEntire_series {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    {η : RayClassCharacter F m} (D : NonprincipalRayHeckeData F m η)
    (s : ℂ) (hs : 1 < s.re) :
    dualEntire D s = Detector.idealLSeries F (Hecke.conjugateRayCharacter η) s := by
  have hn := heckeCompletionFactor_ne_zero F m hm s (by linarith)
  have hprod : heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m s = 1 := by
    rw [reciprocal_eq_inv_completion, inv_mul_cancel₀ hn]
  have H := (D.dual_series s hs).mul_left (heckeReciprocalCompletionFactor F m s)
  have H' : HasSum (fun I : Ideal (𝓞 F) =>
      (starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s)) (dualEntire D s) := by
    simpa only [dualEntire, ← mul_assoc, hprod, one_mul] using H
  rw [← H'.tsum_eq]
  unfold Detector.idealLSeries
  refine tsum_congr fun I => ?_
  by_cases hI : I = ⊥
  · subst I
    simp [Hecke.rayClassCharacter_apply_bot]
  · simp [hI]

def conjugatePrimitive (ν : Detector.PrimitiveFrequencyCharacter F) :
    Detector.PrimitiveFrequencyCharacter F where
  conductor := ν.conductor
  conductor_ne_zero := ν.conductor_ne_zero
  character := Hecke.conjugateRayCharacter ν.character
  primitive := (Hecke.conjugateRayCharacter_isPrimitive_iff _).2 ν.primitive

theorem conjugatePrimitive_nonprincipal (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) : ¬ (conjugatePrimitive ν).character.IsPrincipal := by
  simpa only [conjugatePrimitive, Hecke.conjugateRayCharacter_isPrincipal_iff] using hν

theorem continuation_series (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) {η : RayClassCharacter F m}
    (D : NonprincipalRayHeckeData F m η) (s : ℂ) (hs : 1 < s.re) :
    nonprincipalHeckeEntireContinuation F m η D s = Detector.idealLSeries F η s := by
  rw [nonprincipalHeckeEntireContinuation_eq F hF m hm η D s (by linarith),
    ← (D.series s hs).tsum_eq]
  unfold Detector.idealLSeries
  refine tsum_congr fun I => ?_
  by_cases hI : I = ⊥
  · subst I
    simp [Hecke.rayClassCharacter_apply_bot]
  · simp [hI]

theorem primitive_reflection (hF : NumberField.IsTotallyComplex F)
    (ν : Detector.PrimitiveFrequencyCharacter F)
    (D : NonprincipalRayHeckeData F ν.conductor ν.character)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hgs : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s)
    (s : ℂ) (hs : s.re < 1) :
    g s = D.W * (heckeReciprocalCompletionFactor F ν.conductor s *
      heckeCompletionFactor F ν.conductor (1 - s)) * dualEntire D (1 - s) := by
  have heq : g = nonprincipalHeckeEntireContinuation F ν.conductor ν.character D :=
    RowHeckeBridge.entire_eq_of_eq_right hg
      (nonprincipalHeckeEntireContinuation_differentiable F hF ν.conductor
        ν.conductor_ne_zero ν.character D)
      (fun z hz => (hgs z hz).trans (continuation_series hF ν.conductor_ne_zero D z hz).symm)
  have ht : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hn := heckeCompletionFactor_ne_zero F ν.conductor ν.conductor_ne_zero (1 - s) ht
  have hdual : D.Λdual (1 - s) =
      heckeCompletionFactor F ν.conductor (1 - s) * dualEntire D (1 - s) := by
    unfold dualEntire
    rw [reciprocal_eq_inv_completion, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [heq, nonprincipalHeckeEntireContinuation, D.reflection, hdual]
  ring

theorem completion_ratio_norm {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (σ : ℝ) (s : ℂ) (hs : s.re = σ) :
    ‖heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1 - s)‖ =
      heckeConductorScale F m ^ ((1 : ℝ) / 2 - σ) *
      ‖Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹‖ ^
        NumberField.InfinitePlace.nrComplexPlaces F := by
  have hQ : 0 < heckeConductorScale F m :=
    lt_of_lt_of_le zero_lt_one (one_le_heckeConductorScale F m hm)
  have hc : (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) =
      (heckeConductorScale F m : ℂ) := by
    unfold heckeConductorScale
    rw [Complex.ofReal_mul]
    norm_cast
  unfold heckeReciprocalCompletionFactor heckeCompletionFactor
  rw [hc]
  simp only [norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  rw [show (-s / 2).re = -σ / 2 by simp [hs],
    show ((1 - s) / 2).re = (1 - σ) / 2 by simp [hs]]
  rw [show (1 : ℝ) / 2 - σ = -σ / 2 + (1 - σ) / 2 by ring,
    Real.rpow_add hQ, mul_pow]
  ring

theorem completion_ratio_line_03 :
    ∃ B : ℝ, 0 < B ∧ ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (s : ℂ),
      s.re = (3 / 100 : ℝ) →
      ‖heckeReciprocalCompletionFactor F ν.conductor s *
          heckeCompletionFactor F ν.conductor (1 - s)‖ ≤
        B * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((47 : ℝ) / 100) *
          (2 + |s.im|) ^ NumberField.InfinitePlace.nrComplexPlaces F := by
  obtain ⟨K, hK, HK⟩ := gammaC_reflected_ratio_line_03
  let r := NumberField.InfinitePlace.nrComplexPlaces F
  let d : ℝ := ((|NumberField.discr F| : ℤ) : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero F)
  refine ⟨d ^ ((47 : ℝ) / 100) * K ^ r, by positivity, fun ν s hs => ?_⟩
  rw [completion_ratio_norm ν.conductor_ne_zero (3 / 100) s hs]
  norm_num only [show (1 : ℝ) / 2 - 3 / 100 = 47 / 100 by norm_num]
  have hN : (Ideal.absNorm ν.conductor : ℝ) ^ ((47 : ℝ) / 100) ≤
      (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((47 : ℝ) / 100) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by norm_num)
  have hgam := pow_le_pow_left₀ (norm_nonneg _) (HK s hs) r
  rw [heckeConductorScale, Real.mul_rpow hd.le (Nat.cast_nonneg _)]
  calc _ ≤ (d ^ ((47 : ℝ) / 100) *
        (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((47 : ℝ) / 100)) *
        (K * (2 + |s.im|)) ^ r := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by positivity)) hgam
            (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The functional equation and its gamma factors transfer a uniform .97 bound
to .03. The only analytic hypothesis is the stated .97 estimate; the functional
equation is supplied by the actual native Hecke data, not an assumed norm bound. -/
theorem primitive_line_03_of_97 (hF : NumberField.IsTotallyComplex F)
    (data : ∀ (ν : Detector.PrimitiveFrequencyCharacter F), ¬ ν.character.IsPrincipal →
      NonprincipalRayHeckeData F ν.conductor ν.character)
    (H97 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (g : ℂ → ℂ), Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ t : ℝ,
          ‖g (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ε * (2 + |t|)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (g : ℂ → ℂ), Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ t : ℝ,
          ‖g (((3 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((47 : ℝ) / 100 + ε) *
              (2 + |t|) ^ A := by
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces F
  refine ⟨(r : ℝ) + 1, by positivity, fun ε hε => ?_⟩
  obtain ⟨B, hB, HB⟩ := completion_ratio_line_03 (F := F)
  obtain ⟨C, hC, HC⟩ := H97 ε hε
  refine ⟨B * C, mul_pos hB hC, fun ν hν g hg hgs t => ?_⟩
  let D := data ν hν
  let s : ℂ := ((3 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hs : s.re = (3 / 100 : ℝ) := by simp [s]
  have him : s.im = t := by simp [s]
  have hdual := HC (conjugatePrimitive ν) (conjugatePrimitive_nonprincipal ν hν)
    (dualEntire D) (dualEntire_differentiable ν.conductor_ne_zero D)
    (dualEntire_series ν.conductor_ne_zero D) (-t)
  have hpoint : 1 - s = ((97 / 100 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    dsimp [s]
    push_cast
    ring
  rw [← hpoint] at hdual
  simp only [conjugatePrimitive, abs_neg] at hdual
  have hrefl := primitive_reflection hF ν D g hg hgs s (by rw [hs]; norm_num)
  change ‖g s‖ ≤ _
  rw [hrefl, norm_mul, norm_mul, D.root_norm, one_mul]
  have hratio := HB ν s hs
  rw [him] at hratio
  have hQ : 0 < 1 + (Ideal.absNorm ν.conductor : ℝ) := by positivity
  have hT : 0 < 2 + |t| := by positivity
  calc _ ≤ (B * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((47 : ℝ) / 100) *
        (2 + |t|) ^ r) *
        (C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ε * (2 + |t|)) :=
      mul_le_mul hratio hdual (norm_nonneg _) (by positivity)
    _ = (B * C) * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((47 : ℝ) / 100 + ε) *
        (2 + |t|) ^ ((r : ℝ) + 1) := by
      rw [Real.rpow_add hQ, Real.rpow_add hT, Real.rpow_one, Real.rpow_natCast]
      ring

#print axioms primitive_reflection
#print axioms completion_ratio_line_03
#print axioms primitive_line_03_of_97

end
end DedekindZetaZeroFree.Quantitative.PrimitivePositiveFE
