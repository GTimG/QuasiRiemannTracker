/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The original physical polynomial, with complete primitive restoration and
discarded tails, at the variable physical face. Adapted from PR137 Original
(Sil and predecessor authors, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveFixedProfile
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Original

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator.PhysicalTail
open Cycle25.Weighted.Numerator CenteredMomentRetainedWeightedSource
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- Fourth moment of the actual physical polynomial, including its entire
discarded tail and each row's true primitive presentation. -/
theorem original_fourth_with_cost (A : ChosenData) {s : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1/1000000000) (κ : ℝ)
    (hk0 : (7/10:ℝ) ≤ κ) (hk1 : κ ≤ (3/4:ℝ))
    (hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hkb : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bPhi error : ℝ) (herror : 0 < error)
    (hsPhi : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop,
      affineAtFace (PositiveSource.physicalFace s) A bPhi error U di control Ci)
    (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ)
    (hloss : 0 < loss) (hxi : 0 < xi) (hbpos : 0 < b) (hCslot : 0 < Cslot) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (data : ∀ i : rows, PhysicalReflectionData A.F.S A.F.exclusions.prime i.val)
        (N : rows → ℝ) (Y m : ℝ),
      0 < Y → (∀ i, 0 < N i ∧ N i ≤ b*Y) → 0 ≤ m → m+xi ≤ 2 →
      (∀ i, (data i).combinedConductor ≤ (fixedConductorConstant A.F.S : ℝ)*U^m*(Y/N i)) →
      ∀ T : Finset (Fin A.D.N), ∀ width : T → ℝ, ∀ z : T → ℂ, ∀ height : ℝ,
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ A.sourceMesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (A.D.t/4)) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      ((2*(m+xi)+(2+10*s)*(∑ i, width i) ≤ 1-s ∧ (∑ i, width i) ≤ 3/40) ∨
        (2*(m+xi)+6*κ*(∑ i, width i) ≤ 1 ∨ T = ∅)) →
      (∀ i : rows, ‖∏ j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W
        2 (U^(width j)) (z j)‖ ≤ Cslot*U^q) →
      (∑ i : rows, ‖HeckeDyadic.polynomial (rowCharacter A.F.S A.F.exclusions.prime i.val)
        false G (Y/N i) 0 0‖^4 *
        ‖∏ j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W
          2 (U^(width j)) (z j)‖^2) ≤ C*(1+height)^degree*U^(1+A.D.t+error+loss) := by
  let Ccond : ℝ := fixedConductorConstant A.F.S
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos A.F.S A.F.exclusions.prime
  obtain ⟨degree,Cr,hCr,hret⟩ := retained_fixed_profile_with_cost A hs hsmax κ hk0 hk1 hb hkb
    bPhi error herror hsPhi di control Ci hCi hinput G loss Ccond Ccond xi
    hloss hCcond hCcond hxi
  obtain ⟨Ct,hCt,htail⟩ := subtype_discarded_fourth_negligible (xi/2) 0 q b Ccond Cslot
    (by positivity) hbpos hCcond hCslot G
  refine ⟨degree,8*(Cr+Ct),by positivity,?_⟩
  filter_upwards [hret] with U hret
  have hU := hret.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N Y m hY hN hm hmmax hcombined T width z height
    hw hwmesh hwmax hz hheight hzim hcap hQ
  let τ (i : rows) := (data i).presentation
  let ψ (i : rows) := (data i).primitive
  let R (i : rows) := retainedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let tail (i : rows) := discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let Q (i : rows) := ∏ j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
    A.F.W 2 (U^(width j)) (z j)
  let P (i : rows) := HeckeDyadic.polynomial (rowCharacter A.F.S A.F.exclusions.prime i.val)
    false G (Y/N i) 0 0
  have hc (i : rows) : (data i).combinedConductor ≤ Ccond*U :=
    (data i).combined_le_row.trans (mul_le_mul_of_nonneg_left (hrows i.val i.property).2 hCcond.le)
  have hred (i : rows) : (Ideal.absNorm (∏ p ∈ sourcePrimes (τ i) (ψ i), p) : ℝ) ≤ Ccond*U :=
    (data i).redundant_le_combined.trans (hc i)
  have hr := hret.2 rows hrows τ ψ (fun i => Y/N i) m (fun i => (data i).element_eq)
    (fun i => div_pos hY (hN i).1) hm hmmax hred hcombined T width z height
    hw hwmesh hwmax hz hheight hzim hcap
  have ht := htail rows τ ψ N Q Y U hY hU.le hN (fun u hu => (hrows u hu).2) hc hQ
  simp only [show (xi/2)/2 = xi/4 by ring,neg_zero,Real.rpow_zero,mul_one] at ht
  have hsplit (i : rows) : P i = (data i).phase*(R i+tail i) :=
    (data i).split G (Y/N i) (U^(xi/4)) (div_pos hY (hN i).1)
  have hh := original_split_weighted_fourth Finset.univ P R tail (fun i => (data i).phase) Q
    (fun _ => 1) (Cr*(1+height)^degree*U^(1+A.D.t+error+loss)) Ct
    (fun _ _ => le_rfl) (fun i _ => (data i).phase_norm) (fun i _ => hsplit i)
    (by simpa only [Complex.ofReal_one,div_one] using hr) ht
  simp only [Complex.ofReal_one,div_one] at hh
  have hH : 1 ≤ (1+height)^degree := one_le_pow₀ (by linarith)
  have hpow : 1 ≤ U^(1+A.D.t+error+loss) :=
    Real.one_le_rpow hU.le (by linarith [A.D.t_pos])
  have hcost : 1 ≤ (1+height)^degree*U^(1+A.D.t+error+loss) := one_le_mul_of_one_le_of_one_le hH hpow
  have hCt' := mul_le_mul_of_nonneg_left hcost hCt.le
  exact hh.trans (by nlinarith)

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.original_fourth_with_cost
