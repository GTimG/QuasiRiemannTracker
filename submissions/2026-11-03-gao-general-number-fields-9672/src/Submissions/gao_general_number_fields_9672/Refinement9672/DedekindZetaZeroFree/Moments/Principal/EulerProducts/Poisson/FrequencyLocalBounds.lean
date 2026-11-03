/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Principal/EulerProducts/Poisson/FrequencyLocalBounds.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.FrequencyNormalConvergence

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RawEulerLocal31

noncomputable section

open _root_.DedekindZetaZeroFree _root_.DedekindZetaZeroFree.Quantitative.EulerDomain
open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain
open _root_.DedekindZetaZeroFree.AllRowEuler.InitialSeparation
open DedekindZetaZeroFree.AllRowEuler.InitialSeparation

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem localCorrection_good_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (U.j pr).val = 0 → ∀ p ∈ OmegaStarMargin δ',
          ‖localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-1 - δ) :=
  RawEulerGood31.localCorrection_good_sub_one_le D δ' hδ'

theorem localCorrection_bad_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (U.j pr).val ≠ 0 → ∀ p ∈ OmegaStarMargin δ',
          ‖localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-δ) :=
  RawEulerBad31.localCorrection_bad_sub_one_le D δ' hδ'

theorem localCorrection_bad_sub_one_le_paddedBoxes :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (U.j pr).val ≠ 0 → ∀ p ∈ paddedBoxes,
          ‖localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-(1 / 20000 : ℝ)) :=
  RawEulerBad31.localCorrection_bad_sub_one_le_paddedBoxes D

theorem localCorrection_eq_of_ne_zero (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val ≠ 0) (ξ w z : ℂ) :
    localCorrection D.context U pr ξ w z =
      (1 - CorrectionFactors.V pr z) *
        LocalFiniteSums.f D.context pr (U.j pr) (U.theta D.context pr) ξ w z := by
  rw [localCorrection, if_neg hj, CorrectionFactors.badFactor]

theorem localSeries_hasSumLocallyUniformlyOn (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val ≠ 0) :
    HasSumLocallyUniformlyOn
      (fun (i : Fin 2 × ℕ × ℕ × ℕ) (p : Coordinates) =>
        LocalFiniteSums.seriesTerm D.context pr (U.j pr) (U.theta D.context pr)
          i.1 i.2.1 i.2.2.1 i.2.2.2 p.1 p.2.1 p.2.2)
      (fun p : Coordinates =>
        LocalFiniteSums.f D.context pr (U.j pr) (U.theta D.context pr) p.1 p.2.1 p.2.2)
      OmegaStar :=
  RawEulerBad31.localSeries_hasSumLocallyUniformlyOn D U pr hj

theorem localCorrection_differentiableOn (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val ≠ 0) :
    DifferentiableOn ℂ
      (fun p : Coordinates => localCorrection D.context U pr p.1 p.2.1 p.2.2) OmegaStar :=
  RawEulerProduct31.localCorrection_differentiableOn D U pr

def rawQ (U : RawFrequency D.recipe.A) : ℝ := D.recipe.A.exteriorNorm U.ideal

theorem correctionProduct_subpower (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ OmegaStarMargin δ,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖correctionProduct D.context U p.1 p.2.1 p.2.2‖ ≤ C * rawQ D U ^ ε := by
  obtain ⟨C, hC, h⟩ := RawEulerProduct31.correctionProduct_subpower D δ hδ ε hε
  exact ⟨C, hC, fun U p hp => h U p hp⟩

theorem correctionProduct_subpower_of_subset (T : Set Coordinates) (δ : ℝ) (hδ : 0 < δ)
    (hT : T ⊆ OmegaStarMargin δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ T,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖correctionProduct D.context U p.1 p.2.1 p.2.2‖ ≤ C * rawQ D U ^ ε := by
  obtain ⟨C, hC, h⟩ := correctionProduct_subpower D δ hδ ε hε
  exact ⟨C, hC, fun U p hp => h U p (hT hp)⟩

theorem correctionProduct_subpower_paddedBoxes (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ paddedBoxes,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖correctionProduct D.context U p.1 p.2.1 p.2.2‖ ≤ C * rawQ D U ^ ε := by
  obtain ⟨δ, hδ, hsub⟩ := paddedBoxes_subset_OmegaStarMargin
  exact correctionProduct_subpower_of_subset D paddedBoxes δ hδ hsub ε hε

theorem correctionProduct_subpower_boxes (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ boxes,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖correctionProduct D.context U p.1 p.2.1 p.2.2‖ ≤ C * rawQ D U ^ ε := by
  obtain ⟨C, hC, h⟩ := correctionProduct_subpower_paddedBoxes D ε hε
  exact ⟨C, hC, fun U p hp => h U p (boxes_subset_paddedBoxes hp)⟩

end

end DedekindZetaZeroFree.Quantitative.RawEulerLocal31

end Refinement9672
