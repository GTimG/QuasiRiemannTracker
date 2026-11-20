/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/ConstantTerms/ComplexWeylIntegralWeight.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.ConstantTerms.BruhatCellExpansion
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Periods.WeylIntegralWeights

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem selected_outgoing_weyl_weight (C : JointForwardIdentitySources R N)
    (v : R.A.UnitQuotient) (s : ℂ) (hs : (1 / 3 : ℝ) < s.re)
    (w : InfinitePlace F) (z : w.Completionˣ) (g : Group R)
    (hi : Integrable (fun x : KPAdeles F => incoming C v s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g))
      (KPAdditiveHaar.adelicMeasure F))
    (hia : Integrable (fun x : KPAdeles F => incoming C v s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * (archDiagonal w z * g)))
      (KPAdditiveHaar.adelicMeasure F)) :
    outgoing C v s (archDiagonal w z * g) = weylWeight w z s * outgoing C v s g := by
  exact DedekindZetaZeroFree.CompactPeriodAnalyticity.WeylIntegral.completion_weyl_integral_weight
    F R.A.zeta12 R.A.primitive_zeta12 C.sources.K (C.sources.flat v) s w z g hi hia

end DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods

end
