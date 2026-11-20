/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original reflected numerator, primitive presentations, masks, retained
annuli and discarded tails are those of the credited imported source library.
The Q positive source supplies the physical moment; it is not a premise here. -/
import Candidate.C092.transport.DirectPhysicalOriginal
import Candidate.C092.transport.DirectPhysicalSource
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator
namespace QRH.Cycle092.DirectEnergy

/-- Actual Q-source fourth moment of the original physical numerator.
One mesh precedes D/F; constants precede every row, original coefficient scale,
primitive presentation and independent external height. The empty selected
family remains valid through ordinary length U². -/
theorem q_original_numerator_fourth
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (hAffineError : 0 < affineError) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : Cycle25.Weighted.MomentData)
      (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
      (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
      (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ)
      (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ),
      0 < loss → 0 < xi → 0 < b → 0 < Cslot →
      ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (data : ∀ i : rows, PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : rows → ℝ) (Y m : ℝ),
      0 < Y → (∀ i, 0 < N i ∧ N i ≤ b*Y) → 0 ≤ m → m+xi ≤ 2 →
      (∀ i, (data i).combinedConductor ≤ (fixedConductorConstant F.S : ℝ)*U^m*(Y/N i)) →
      ∀ (T : Finset (Fin D.N)) (width : T → ℝ) (z : T → ℂ) (height : ℝ),
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ mesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀ i, (z i).re=17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      (((∑ i, width i) ≤ QRH.Cycle090.physicalCap ∧
        2*(m+xi)+(2+10*QRH.Cycle090.sourceCost)*(∑ i,width i) ≤ 1-QRH.Cycle090.sourceCost) ∨
        (2*(m+xi)+6*κ*(∑ i,width i) ≤ 1 ∨ T=∅)) →
      (∀ i : rows, ‖∏ s, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ Cslot*U^q) →
      (∑ i : rows, ‖polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0‖^4*
        ‖∏ s, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  obtain ⟨mesh,hm,hsrc⟩ := q_physical_affine_source hβ affineError hAffineError
  refine ⟨mesh,hm,?_⟩
  intro D F κ hκlo hκhi hκβ G loss xi q b Cslot hloss hxi hb hCslot
  obtain ⟨bPhi,_hbPhi,hsPhi,di,control,Ci,hCi,hinput⟩ := hsrc D F
  exact affine_original_numerator_fourth F κ hκlo hκhi hβ hκβ
    bPhi mesh affineError hAffineError hsPhi di control Ci hCi hinput G loss xi q b Cslot
    hloss hxi hb hCslot
end QRH.Cycle092.DirectEnergy
#print axioms QRH.Cycle092.DirectEnergy.q_original_numerator_fourth
