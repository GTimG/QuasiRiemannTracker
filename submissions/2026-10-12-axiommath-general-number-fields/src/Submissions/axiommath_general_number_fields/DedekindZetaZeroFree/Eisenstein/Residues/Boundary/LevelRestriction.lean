/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/Boundary/LevelRestriction.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CoherentLevelsAndNormInvariance
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalFlatFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryRelevel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
def meetLevel (U J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
  ⟨U.toOpenSubgroup ⊓ J.toOpenSubgroup, U.isCompact.inter_right J.toOpenSubgroup.isClosed⟩
def restrictStage (U V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U) :
    KPContActualSphericalFlatStage.Stage F ζ hζ V :=
  ⟨v.val, by
    refine ⟨?_, v.property.2⟩
    intro g u
    exact v.property.1 g ⟨u.val, Subgroup.map_mono h u.property⟩⟩
@[simp] theorem restrictStage_val (U V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U) :
    (restrictStage F ζ hζ U V h v).val = v.val := rfl
theorem level_idempotent (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPShift81CoherentLevel.level F ζ hζ (KPShift81CoherentLevel.level F ζ hζ U) =
      KPShift81CoherentLevel.level F ζ hζ U := by
  unfold KPShift81CoherentLevel.level
  simp only [inf_assoc, inf_idem]
end DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryRelevel

end
