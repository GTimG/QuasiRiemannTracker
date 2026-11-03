/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Profiles/RadialJetsAndLocalNorms.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Profiles.RadialJetRegularity
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.Integration.DominatedSecondDifferentiation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Haar.PowerEnvelopes.Definitions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def radialSheetIntegrand (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (v : R.A.UnitQuotient) (κ : R.A.V) (u : ℝ) (y : R.A.G1) : ℂ :=
  C.realization.sheetIntegrand C.packet v κ
    (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u))

theorem radial_sheet_integrand_regular (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    (∀ v κ y, ContDiff ℝ 2 (fun u => radialSheetIntegrand R C v κ u y)) ∧
    (∀ v κ (j : ℕ), j ≤ 2 → ∀ u : ℝ,
      letI : MeasurableSpace R.A.G1 := borel _;
      AEStronglyMeasurable (fun y : R.A.G1 =>
        iteratedDeriv j (fun t => radialSheetIntegrand R C v κ t y) u)
        R.probe.domain.measure) := by
  constructor
  · intro v κ y
    exact (SheetRescaling.sheet_radial_contDiff R C.realization C.packet v κ y).of_le (by simp)
  · intro v κ j hj u
    exact SheetRescaling.sheet_radial_jets_aestronglyMeasurable R C.realization C.packet v κ j hj u

def normalizedLocalWeylValue (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient)
    (p : KPHilbert.Place F) (z : (KPHilbert.Completion F p)ˣ) : ℂ :=
  fourier R C.sources.dq (C.realization.theta v)
    (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F p z) *
      KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 p
          (KPRationalAdelicSplitting.WCoordinates F R.A.zeta12 R.A.primitive_zeta12 p))) /
    fourier R C.sources.dq (C.realization.theta v) 1

theorem first_root_forward_period_ne_zero (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient) :
    fourier R C.sources.dq (C.realization.theta v) 1 ≠ 0 := by
  have hd : diagonal R 1 = 1 := by
    have ha : KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 1 = 1 := by
      apply RestrictedProduct.ext
      intro p
      simp [KPRationalAdelicSplitting.ATuple, KPRationalAdelicSplitting.ACoordinates]
    simp [diagonal, localIdele, KPRationalAdelicSplitting.localIdele,
      KPRationalAdelicSplitting.pglA, KPRationalAdelicSplitting.A, ha]
  have hf := C.forward v 1
  rw [hd] at hf
  rw [hf]
  exact C.packet.forwardProfile_one_ne_zero v

def localWeylArchJet (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient)
    (w : InfinitePlace F) (j : ℕ) (z : w.Completionˣ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => normalizedLocalWeylValue R C v (Sum.inl w)
    (z * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) 0

def sheetProductPowerMajorant (R : PrincipalMellin.ActualRecipe S η)
    (M A : ℝ) (y : R.A.G) : ℝ :=
  (∏ p : R.A.Sf,
    ThetaRawSheetEnvelope.WeightedWhittakerSheets.finitePowerMajorant M
      ‖(y.2 p : p.val.adicCompletion F)‖) *
    ∏ w : InfinitePlace F,
      ThetaRawSheetEnvelope.WeightedWhittakerSheets.archPowerMajorant A
        (‖(y.1 w : w.Completion)‖ ^ 2)

end DedekindZetaZeroFree.ThetaExpansion

end
