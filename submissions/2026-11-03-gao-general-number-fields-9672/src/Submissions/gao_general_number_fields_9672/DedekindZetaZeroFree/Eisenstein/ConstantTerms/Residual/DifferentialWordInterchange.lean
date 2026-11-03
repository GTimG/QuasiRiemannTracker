/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/ConstantTerms/Residual/DifferentialWordInterchange.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.Cuspidality.DifferentialWords

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualUpperWordInterchange
open KPMsGreenFlux KPMsGreenFlux.IntrinsicAveraging KPSmoothActualFlowData
open KPContActualSphericalRightFieldIdentification KPMsClearedTruncationL2.NativeWordBridge
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
set_option backward.isDefEq.respectTransparency false

theorem actualRight_eq (b : Fin (groupDimension F)) (f : Cover F ζ hζ → ℂ) :
    actualRight F ζ hζ b f = rightDerivative F ζ hζ
      (wordIndexEquiv F b).1 (wordIndexEquiv F b).2 f := by
  funext g
  unfold actualRight rightDerivative
  simp only [matrixExp_eq_flow]
  rfl

theorem constantTerm_word
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : ∀w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (w : List (Fin (groupDimension F))) :
    actualRightWord F ζ hζ w (constantTerm A dn j (IntrinsicAveraging.pullback f)) =
      constantTerm A dn j (IntrinsicAveraging.pullback (wordDerivative F ζ hζ (w.map (wordIndexEquiv F)) f)) := by
  induction w with
  | nil => rfl
  | cons b w hw =>
    rw [actualRightWord,hw,actualRight_eq]
    exact ResidualIntrinsicJets.rightDerivative_constantTerm_word A dn j f hf _ _ _

theorem word_left (w : List (Fin (groupDimension F)))
    (f : Cover F ζ hζ → ℂ) (a : Cover F ζ hζ) :
    actualRightWord F ζ hζ w (fun g => f (a*g)) =
      fun g => actualRightWord F ζ hζ w f (a*g) := by
  induction w with
  | nil => rfl
  | cons b w hw =>
    funext g
    simp only [actualRightWord,actualRight,hw]
    congr 1
    funext t
    simp only [mul_assoc]

def upper (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∫q, IntrinsicAveraging.pullback f (KPGlobalTorusFunctionData.N F ζ hζ
    (KPCompactFourier.representative F q)*g) ∂dn

theorem upper_word
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : ∀w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (w : List (Fin (groupDimension F))) :
    actualRightWord F ζ hζ w (upper dn f) =
      upper dn (wordDerivative F ζ hζ (w.map (wordIndexEquiv F)) f) := by
  have he (h : KPSmoothActualFlowData.X F ζ hζ → ℂ) : upper dn h =
      fun g => constantTerm A dn j (IntrinsicAveraging.pullback h) (cuspRepresentative A j*g) := by
    funext g
    rw [ResidualAllWordCusp.constantTerm_eq_upper]
    simp only [inv_mul_cancel_left,upper]
  rw [he f,word_left,constantTerm_word A dn j f hf]
  exact (he _).symm
end DedekindZetaZeroFree.FourierContinuation.ResidualUpperWordInterchange

end
