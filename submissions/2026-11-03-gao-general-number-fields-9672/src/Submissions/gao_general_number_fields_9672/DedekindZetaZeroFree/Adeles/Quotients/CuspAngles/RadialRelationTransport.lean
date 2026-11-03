/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/CuspAngles/RadialRelationTransport.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.TransitionsAndCoordinateDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal
namespace DedekindZetaZeroFree.KPMsActualAngularFixedRadiusRelationSource
open KPMsActualAngularSource KPMsActualAngularDomainSource KPMsActualAngularDescentSource
open KPMsActualCuspSource
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem radial_s_commute
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (r : KPMsFixedHaarDisintegration.Radius) (y : Fˣ) :
    Commute (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r)
      (KPGlobalTorusFunctionData.s F ζ hζ y).val := by
  obtain ⟨z,hz⟩ := radialSection_mem_center F ζ hζ B r
  have hc := ((Subgroup.mem_center_iff.mp z.property (KPGlobalTorusFunctionData.s F ζ hζ y))).symm
  have h := congrArg (fun t : KPGlobalTorusFunctionData.E F ζ hζ => t.val) hc
  change _ * _ = _ * _ at h
  change _ * _ = _ * _
  simpa only [hz] using h

theorem quotientMap_left_rational
    (γ : KPCuspArithmetic.PGL2 F) (g : KPMsActualAngularSource.G F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (rationalLift F ζ hζ γ * g) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have hmem : rationalLift F ζ hζ γ ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
    unfold rationalLift
    exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F _, rfl⟩
  convert (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem hmem using 1 <;> group

theorem quotientMap_left_s
    (y : Fˣ) (g : KPMsActualAngularSource.G F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      ((KPGlobalTorusFunctionData.s F ζ hζ y).val * g) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g := by
  have he : (KPGlobalTorusFunctionData.s F ζ hζ y).val =
      rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d F y 1)) := by
    rw [rationalLift_mk]
    rfl
  rw [he, quotientMap_left_rational]

end DedekindZetaZeroFree.KPMsActualAngularFixedRadiusRelationSource

end
