/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Profiles/OrbitSheetMassBounds.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Profiles.AbsoluteSheetBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def gammaEquiv : ThetaReflectionData.rationalGamma R.A ≃* R.A.Gamma1 :=
  MulEquiv.ofBijective
    ({ toFun := fun γ => ⟨⟨R.A.diagonal γ.val, R.A.Gamma_le_G1
          (Subgroup.mem_map.mpr ⟨γ.val, γ.property, rfl⟩)⟩,
          Subgroup.mem_map.mpr ⟨γ.val, γ.property, rfl⟩⟩
       map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
       map_mul' := by intro x y; apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _ } :
      ThetaReflectionData.rationalGamma R.A →* R.A.Gamma1)
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        apply Units.ext
        let w : InfinitePlace F := Classical.choice inferInstance
        have hw := congrArg (fun γ : R.A.Gamma1 => (γ.val.val.1 w : w.Completion)) h
        exact (algebraMap F w.Completion).injective hw
      · intro γ
        obtain ⟨a, ha, he⟩ := Subgroup.mem_map.mp γ.property
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he)

@[simp] lemma gammaEquiv_val (γ : ThetaReflectionData.rationalGamma R.A) :
    (gammaEquiv R γ).val.val = R.A.diagonal γ.val := rfl

end DedekindZetaZeroFree.OrbitFrequencies

end
