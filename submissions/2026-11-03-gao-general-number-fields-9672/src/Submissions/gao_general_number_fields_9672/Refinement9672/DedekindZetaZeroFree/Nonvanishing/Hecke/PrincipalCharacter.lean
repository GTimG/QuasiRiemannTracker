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
Original path: DedekindZetaZeroFree/Nonvanishing/Hecke/PrincipalCharacter.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.RayCharacterGaloisRealization
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Hecke.EulerProducts.RayCharacterFiniteCorrection
public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Main

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.HeckeCorollary

open scoped NumberField
open AbelianQuotient IsDedekindDomain

theorem principalRayCharacter_ne_zero
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : RayClassCharacter K m) (hχ : χ.IsPrincipal) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s : ℂ, 1209 / 1250 < s.re → s ≠ 1 → f s ≠ 0 := by
  let S := (narrowIdealModulus K m hm).finitePart.support
  let χ₀ := trivialRayCharacter K
  obtain ⟨Z, hZdiff, hZseries, hZzero⟩ := dedekindZeta_ne_zero K
  have hzero : ∀ p ∈ S, χ p.asIdeal = 0 :=
    rayCharacter_eq_zero_of_mem_modulus_support K m hm χ
  have hagree : ∀ p ∉ S, χ p.asIdeal = χ₀ p.asIdeal := by
    intro p hp
    have hcoprime : p.asIdeal ⊔ m = ⊤ := by
      by_contra hne
      have hnone := rayIdealClass_eq_none K m hm p.asIdeal (Or.inr hne)
      rw [rayIdealClass_of_finitePrime K m hm p hp] at hnone
      contradiction
    rw [hχ p.asIdeal p.ne_bot hcoprime]
    simp [χ₀, trivialRayCharacter_apply, p.ne_bot]
  have htrivial (s : ℂ) (hs : 1 < s.re) :
      (∑' I : Ideal (𝓞 K), χ₀ I * (Ideal.absNorm I : ℂ) ^ (-s)) =
        NumberField.dedekindZeta K s := by
    apply HasSum.tsum_eq
    apply (Odlyzko.hasSum_idealInverseNormPower K hs).congr_fun
    intro I
    by_cases hI : I = ⊥
    · simp [χ₀, trivialRayCharacter_apply, hI, Odlyzko.idealInverseNormPower]
    · simp [χ₀, trivialRayCharacter_apply, hI, Odlyzko.idealInverseNormPower_of_ne_zero K s hI]
  refine ⟨fun s => Z s * finiteEulerCorrection K χ₀ S s,
    hZdiff.mul (finiteEulerCorrection_differentiable K χ₀ S).differentiableOn, ?_, ?_⟩
  · intro s hs
    have hsum := (weightedIdealSummability K χ χ.map_mul' χ.map_top'
      ((χ.eq_zero_iff' ⊥).mpr (Or.inl rfl)) (rayCharacter_norm_le_one K m hm χ) s hs).of_norm
    have heq := rayCharacter_eulerCorrection K m ⊤ hm top_ne_bot χ χ₀ S hzero hagree s hs
    rw [htrivial s hs, ← hZseries s hs] at heq
    change HasSum _ (Z s * finiteEulerCorrection K χ₀ S s)
    rw [← heq]
    exact hsum.hasSum
  · intro s hs hs1
    exact mul_ne_zero (hZzero s hs hs1)
      (finiteEulerCorrection_ne_zero K χ₀
        (rayCharacter_norm_le_one K ⊤ top_ne_bot χ₀) S s (by linarith))

end DedekindZetaZeroFree.HeckeCorollary

end Refinement9672
