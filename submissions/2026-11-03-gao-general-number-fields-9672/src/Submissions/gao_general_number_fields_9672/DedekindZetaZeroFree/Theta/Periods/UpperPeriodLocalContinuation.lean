/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/UpperPeriodLocalContinuation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.CompactPeriodLaurentGerms
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberAnalyticity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity
open MomentSources
open ThetaExpansion.ChamberPeriods
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem selected_chamber_period_integrable (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    Integrable (fun q => KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
      C.sources.K (C.sources.flat v) s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) C.sources.dq :=
  Chamber.upper_integrable F R.A.zeta12 R.A.primitive_zeta12 C.sources.K C.sources.iwasawa
    (C.sources.flat v) C.sources.dq C.sources.quotientHaar s hs g

end DedekindZetaZeroFree.CompactPeriodAnalyticity

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity
open MomentSources
open ThetaExpansion.ChamberPeriods
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem selected_chamber_period_analytic (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (g : Group R) : AnalyticOnNhd ℂ (fun s => chamberPeriod C v s g)
      {s : ℂ | (1 / 3 : ℝ) < s.re} :=
  Chamber.upper_analyticOnNhd C.sources v g

theorem selected_cleared_period_analytic (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (g : Group R) : AnalyticOnNhd ℂ (fun s => clearedPeriod C v s g)
      (Metric.ball (0 : ℂ) C.realization.radius) :=
  CompactPeriod.upper_cleared_analyticOnNhd C.realization v g

end DedekindZetaZeroFree.CompactPeriodAnalyticity

end
end
