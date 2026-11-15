/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Variable-face fourth moment for the complete retained primitive restoration.
Adapted from PR137 Retained (Sil and predecessor authors, Apache-2.0).
The row-dependent primitive presentations and full retained sums are unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveHybrid
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Retained

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths Cycle25WeightedNumeratorReflection Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceLowWindow CenteredMomentNaturalPrimitive
local notation "O" => HeckeFamily.O
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- The full retained fourth moment, with the variable physical face and all
native/empty alternatives. Presentation, scale and primitive character may
vary with the row; their combined conductor and profile costs remain explicit. -/
theorem retained_fourth_with_cost (A : ChosenData) {s : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1/1000000000) (κ : ℝ)
    (hk0 : (7/10:ℝ) ≤ κ) (hk1 : κ ≤ (3/4:ℝ))
    (hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hkb : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bPhi error : ℝ) (herror : 0 < error)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant : ℝ → ℂ)
      ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop,
      affineAtFace (PositiveSource.physicalFace s) A bPhi error U di control Ci)
    (epsilon Cscale xi : ℝ) (hepsilon : 0 < epsilon) (hCscale : 0 < Cscale) (hxi : 0 < xi) :
    ∃ degree : ℕ, ∃ H : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (τ ψ : rows → Character) (G : rows → 𝓢(ℝ,ℂ)) (X : rows → ℝ) (m B Rcap : ℝ),
      (∀ i, ∀ n : O, elementCoeff (rowCharacter A.F.S A.F.exclusions.prime i.val) n =
        elementCoeff (τ i) n) →
      (∀ i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 → 0 < B →
      (∀ i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ B) →
      1 ≤ Rcap → (∀ i, (Ideal.absNorm (∏ P ∈ sourcePrimes (τ i) (ψ i), P) : ℝ) ≤ Rcap) →
      (∀ i, ((ψ i).modulus.absNorm : ℝ)*(Ideal.absNorm (∏ P ∈ sourcePrimes (τ i) (ψ i), P) : ℝ)
        ≤ Cscale*U^m*X i) →
      ∀ T : Finset (Fin A.D.N), ∀ width : T → ℝ, ∀ z : T → ℂ, ∀ height : ℝ,
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ A.sourceMesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (A.D.t/4)) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      ((2*(m+xi)+(2+10*s)*(∑ i, width i) ≤ 1-s ∧ (∑ i, width i) ≤ 3/40) ∨
        (2*(m+xi)+6*κ*(∑ i, width i) ≤ 1 ∨ T = ∅)) →
      (∑ i : rows, ‖retainedSchwartz (τ i) (ψ i) (G i) (X i) (U^(xi/4))‖^4 *
        ‖∏ j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W
          2 (U^(width j)) (z j)‖^2) ≤
      C*Rcap^epsilon*B^4*(1+2*((m+xi)*Real.log U))^2*
        (1+height)^degree*U^(1+A.D.t+error) := by
  obtain ⟨degree,Jp,Cp,hCp,hpositive⟩ := hybrid_fourier_with_cost A hs hsmax κ hk0 hk1 hb hkb
    bPhi error herror hsPhi di control Ci hCi hinput
  obtain ⟨H,Cr,hCr,hretained⟩ := actual_retained_uniform_fourth epsilon hepsilon 2 Jp (by norm_num)
  refine ⟨degree,H,Cr*Cp,by positivity,?_⟩
  filter_upwards [hpositive,eventually_retained_log_interval Cscale xi hCscale hxi] with U hp hg
  have hU := hp.1
  have hUpos := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ G X m B Rcap he hX hm hmmax hB hG hRcap hR hcombined
    T width z height hw hwmesh hwmax hreal hheight hzim hcapacity
  let n := m+xi
  have hn : 0 ≤ n := by dsimp [n]; linarith
  let P (i : rows) := ∏ j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
    A.F.W 2 (U^(width j)) (z j)
  let E := Cp*(1+height)^degree*U^(1+A.D.t+error)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinterval : 0 ≤ n*Real.log U := mul_nonneg hn (Real.log_pos hU).le
  have hgeom (i : rows) (a : CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes (τ i) (ψ i)))
      (hY : 0 < dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
      (ha : a.2 ∈ CenteredMomentReflectedTruncation.retainedAnnuli (U^(xi/4))
        (dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2) hY) :
      Real.log (dyadicScale a.2*dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
        ∈ Set.Icc 0 (n*Real.log U) := hg.2 (τ i) (ψ i) (X i) m (hX i) (hcombined i) a hY ha
  have hpoly (i : rows) (W : ℝ → ℂ) (x freq : ℝ) :
      polynomial (τ i).inverse false W x 0 freq =
        polynomial (rowCharacter A.F.S A.F.exclusions.prime i.val).inverse false W x 0 freq :=
    (Cycle25.Weighted.RowConductor.polynomial_eq_of_elementCoeff_eq _ _
      (Cycle25.Weighted.RowConductor.inverse_elementCoeff_eq _ _ (he i)) false W x 0 freq).symm
  have hmoment (v w : ℝ) (j k : Fin 2) (x : ℝ) (hx : x ∈ Set.Icc 0 (n*Real.log U))
      (y : ℝ) (hy : y ∈ Set.Icc 0 (n*Real.log U)) :
      (∑ i : rows, ‖polynomial (τ i).inverse false (scaleTest (fun z : ℝ => (annulus z : ℂ)) j)
        (Real.exp x) 0 (2*Real.pi*v) *
        polynomial (τ i).inverse false (scaleTest (fun z : ℝ => (annulus z : ℂ)) k)
        (Real.exp y) 0 (2*Real.pi*w) * P i‖^2) ≤ E*((1+‖v‖)^Jp)^2*((1+‖w‖)^Jp)^2 := by
    have hxlen := reflection_window_length U n x hU hn hx
    have hylen := reflection_window_length U n y hU hn hy
    simp_rw [hpoly]
    have hh := hp.2 rows hrows T width z height n hw hwmesh hwmax hreal hheight hzim
      hn hmmax hcapacity (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
      hxlen.2 hylen.2 hxlen.1 hylen.1 j k v w
    rw [←Finset.sum_coe_sort rows] at hh
    simpa only [P,E] using hh
  have hh := hretained G τ ψ P X (fun _ => U^(xi/4)) 0 (n*Real.log U) B E Rcap
    hX hinterval hgeom hB hE hG hRcap hR hmoment
  convert hh using 1 <;> dsimp [E,n] <;> ring

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.retained_fourth_with_cost
