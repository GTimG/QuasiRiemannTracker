/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Weil/CubicCorrection/CharacterExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.CubicCorrection.ExtensionData
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.FiniteGammaNormalization
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.QuadraticGaussCorrection
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.ResidueSymbols.HilbertFactorAndSexticConjugation

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem correctedPhaseGluing (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
    (H : A.V → A.V → Fˣ) (B : Subgroup A.V)
    (hB : A.IsSUnitIsotropicComplement H B)
    (h : A.WeilSStructuralLaws H σ A.complexWeilPhase
      (fun v => A.finiteWeilPhase v.val)) :
    ∃ (φ : B →* ℂˣ) (D : A.ClassCharacterExtension B φ),
      (∀ b : B, φ b ^ 6 = 1) ∧
      (∀ (y : A.G) (hy : QuotientGroup.mk' A.sixthPowers y ∈ B),
        (A.ideleSInverseProduct D.ideleCharacter y : ℂ) =
          (σ (((A.H_S (A.diagonal CubicWeilCorrection.fourS) y : Fˣ) : F)))⁻¹ *
            A.weilSCorrection A.complexWeilPhase (fun v => A.finiteWeilPhase v.val) y) := by
  obtain ⟨φ, D, h6, hrecipe⟩ :=
    CubicWeilCorrection.phaseClassExtension A hCl σ H B hB
      A.complexWeilPhase (fun v => A.finiteWeilPhase v.val) h
  refine ⟨φ, D, h6, ?_⟩
  intro y hy
  rw [hrecipe y hy, CubicWeilCorrection.cubicS_coe]

theorem correctedWeilExtension (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (hS : A.ContainsTraceBadPlaces)
    (σ : F →+* ℂ) (H : A.V → A.V → Fˣ) (B : Subgroup A.V)
    (hActual : ∀ x y : A.G, H (QuotientGroup.mk' A.sixthPowers x)
      (QuotientGroup.mk' A.sixthPowers y) = (A.H_S x y : Fˣ))
    (hB : A.IsSUnitIsotropicComplement H B) :
    Nonempty (CorrectedWeilExtension A H B σ hS) := by
  obtain ⟨φ, D, _h6, hrecipe⟩ := correctedPhaseGluing A hCl σ H B hB
    (actualWeilSStructuralLaws A σ H hActual)
  refine ⟨{
    G := D.ideleCharacter
    continuous := D.continuous
    finiteOrder := D.finiteOrder
    unramified := D.unramified
    infinity := classCharacterExtension_infinity A B φ D
    stabilized := finiteQuadraticStabilizes_free A
    normalizer_ne_zero := finiteGamma_one_ne_zero_free A
    structural := actualWeilSStructuralLaws A σ H hActual
    local_recipe := fun y hy => hrecipe y hy
    prime := ?_ }⟩
  intro I v hIv p hp a ha hap x hx
  have hideal := (localArithmeticLaws A D.ideleCharacter D.continuous D.unramified).1
    I x a p hx hp hap
  calc
    (D.ideleCharacter (QuotientGroup.mk x) : ℂ) =
        (A.ideleSInverseProduct D.ideleCharacter (A.diagonal a) : ℂ) :=
      congrArg (fun z : Circle => (z : ℂ)) hideal
    _ = (σ (((A.H_S (A.diagonal CubicWeilCorrection.fourS)
          (A.diagonal a) : Fˣ) : F)))⁻¹ *
        A.weilSCorrection A.complexWeilPhase (fun w => A.finiteWeilPhase w.val)
          (A.diagonal a) := hrecipe (A.diagonal a) ha
    _ = star (σ (A.sexticResidue I (4 : A.R))) * A.idealGauss σ hS I p hp 3 := by
      rw [CorrectedWeilSource.inverse_four_hilbert_eq_star_residue A σ I p hp a hap,
        CorrectedWeilSource.weilSCorrection_diagonal_prime A σ hS B I v hIv p hp a hap ha]

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
