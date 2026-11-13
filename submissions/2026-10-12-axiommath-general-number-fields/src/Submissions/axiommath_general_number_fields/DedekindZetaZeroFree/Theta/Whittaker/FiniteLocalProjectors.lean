/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/FiniteLocalProjectors.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.Jacquet.FiniteWhittakerProjectors
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Whittaker.LocalFunctionalsFromGlobalPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
open _root_.DedekindZetaZeroFree.SArithmeticData renaming localTraceCharacter_exists_ne_one → localTraceCharacter_exists_ne_one
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def actualFiniteRoot (q : KPFinitePlace F) :
    Multiplicative (q.adicCompletion F) →*
      KPPGLLocalCover.CubicPGL2 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) where
  toFun t := KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t.toAdd
  map_one' := by simp [KPPGLLocalCover.N, KPStandardLocalRootLifts.N_zero]
  map_mul' t u := KPPGLLocalCover.N_add F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) _ _

def actualFiniteCharacter (q : KPFinitePlace F) : ContinuousAddChar (q.adicCompletion F) where
  toAddChar := {
    toFun t := (ResidueTrace.localTraceCharacter q t : ℂ)
    map_zero_eq_one' := by simp
    map_add_eq_mul' t u := by rw [AddChar.map_add_eq_mul, Circle.coe_mul] }
  continuous_toFun := continuous_subtype_val.comp (ResidueTrace.continuous_localTraceCharacter q)
  unitary t := Circle.norm_coe _

theorem character_nontrivial (q : KPFinitePlace F) :
    ∃ t, (actualFiniteCharacter (F := F) q).toAddChar t ≠ 1 := by
  obtain ⟨t, ht⟩ := localTraceCharacter_exists_ne_one (F := F) q
  exact ⟨t, fun h => ht (Circle.coe_injective (by simpa [actualFiniteCharacter] using h))⟩

variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

abbrev actualFiniteAction (D : SourceFactorization R Q T) (q : KPFinitePlace F) :=
  KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
    (D.finiteData q).haar (D.finiteData q).haar_integer

theorem stabilizer_open (D : SourceFactorization R Q T)
    (q : KPFinitePlace F) (b : actualLocal R D.finiteData (Sum.inr q)) :
    IsOpen {g | actualFiniteAction R D q g b = b} := by
  obtain ⟨J, hJ⟩ := KPRankOneShellRepair.actualCanonicalImage_smooth F R.A.zeta12
    R.A.primitive_zeta12 q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
    (D.finiteData q).haar (D.finiteData q).haar_integer b
  apply isOpen_iff_mem_nhds.mpr
  intro g hg
  have hgn : ∀ᶠ h in nhds g, g⁻¹ * h ∈ J :=
    (J.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hgn] with h hh
  have he := hJ (g⁻¹ * h) hh
  have hk := congrArg (actualFiniteAction R D q g) he
  have hk' : actualFiniteAction R D q h b = actualFiniteAction R D q g b := by
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using hk
  exact hk'.trans hg

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
