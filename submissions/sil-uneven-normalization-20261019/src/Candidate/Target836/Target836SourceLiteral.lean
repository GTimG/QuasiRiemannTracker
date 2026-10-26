/- Fresh source-budget to actual initial moment transport. Apache-2.0;
adapted from Hailey Collet and accepted PR60. -/
import Candidate.Target836.Source836.GeometryAffineAssembly
import Candidate.Target836.Num836.Fourth.Input

set_option autoImplicit false
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate ContDiff
open Filter HeckeFamily Cycle63InitialMass CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentLogDyadic
open Cycle25WeightedNumeratorPhysical CenteredMomentDetectorDictionary ProbePhysical

/-- Chosen reflected numerator source: all original masks and fixed exclusions
are retained, while the pending estimate remains a literal live budget. -/
def SourceLiteralAffineGeometryBudget {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh εmass τ ξ : ℝ) : Prop :=
  let W:=fun x=>conj (F.W x)
  let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
  let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
  let η:=fixedSourcePrincipal F.S F.exclusions.prime
  LiteralAffineGeometryBudget (α:=Fin D.N) F.modulus ⊤ le_top W hW hs
    η η (weighted_sourceFixedIdeal F) bΦ mesh εmass τ ξ

/-- The exact public fourth-moment input follows from the genuine full
geometry budget. Constants precede every live row, profile and height. -/
theorem weighted_source_affine_from_geometry {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε τ ξ : ℝ)(hbΦ : 0< bΦ)(hmesh : 0< mesh)(hε : 0< ε)
    (hτ : 0< τ)(hξ : 0< ξ)
    (hmeshComparison : mesh≤ Cycle63FirstActual.comparisonMesh 1 1 (ε/2))
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ))
    (hbudget : SourceLiteralAffineGeometryBudget F bΦ mesh (ε/4) τ ξ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠ U : ℝ in atTop,
      Target836.Numerator.Fourth.AffineAt F bΦ mesh ε U degree S C := by
  let W:=fun x=>conj (F.W x)
  have hW : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  have hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
  let η:=fixedSourcePrincipal F.S F.exclusions.prime
  exact literal_geometry_initial_affine (α:=Fin D.N) F.modulus ⊤ le_top W hW hs
    η η (weighted_sourceFixedIdeal F) bΦ mesh ε τ ξ hbΦ hmesh hε hτ hξ
    hmeshComparison hbeta hκbeta (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 logAnnulus_compact logAnnulus_smooth hbudget

end
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.weighted_source_affine_from_geometry
