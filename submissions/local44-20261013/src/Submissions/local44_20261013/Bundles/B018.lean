/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B014
import Submissions.local44_20261013.Bundles.B015
import Submissions.local44_20261013.Bundles.B016
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralSelected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorIntegral

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceDeletionClipped ; sha256 64b2763eddd095b0e5a6d8da7e25a5596f0ac3813e28e0b7e3e1b3bb9664e8ad -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceDeletionClipped.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionClipped
open HeckeFamily Cycle25CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget

local notation "O" => HeckeFamily.O

lemma deleted_long_le_width (Z M X₁ X₂ ell kappa : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 7/10 ≤ kappa)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I) :
    Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) ≤ M := by
  have hg := balanced_reference_geometry Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap
  have hn := product_norm_ge_one D hD
  have hp : 0 < ((∏ I ∈ D, I).absNorm:ℝ) := zero_lt_one.trans_le hn
  have hy := (comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂).2
  rw [Real.logb_div hy.ne' hp.ne']
  have hlog := Real.logb_nonneg hZ hn
  linarith [hg.2.2.2.2]

lemma clipped_reflected_bound (Z M X₁ X₂ ell kappa xi reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 7/10 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (href : reflected ≤ max 0 (M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi)) :
    reflected ≤ M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi := by
  have hlong := deleted_long_le_width Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap D hD
  rwa [max_eq_right (by linarith)] at href

end SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionClipped

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceDeletionClipped -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.FullWAggregate ; sha256 0b17703036a379b28233be37d8a4972c0e2c62ea8a4d830b0be26abb783ef0b1 -/
section



/-! The actual weighted physical finite sum with the full numerator integral. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def fullWWeightedRow {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : HeightSpace→ℂ :=
  (fullWSlab H).indicator
    (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1/2) (17/50))

theorem fullWWeightedRow_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (fullWWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H) heightMeasure := by
  have hi := continued_kernel_strip_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (1/2) (17/50) le_rfl (by linarith) le_rfl (by linarith)
  let E := fullWSlab H
  have hE : MeasurableSet E := fullWSlab_measurable H
  apply (integrable_indicator_iff hE).mpr
  have heq : weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1/2) (17/50)=
      fun t=>(∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1/2) (17/50) t := by
    funext t
    exact weightedRowOnLines_eq ..
  rw [heq]
  exact (hi.mono_set (fun t ht=> ht.1.1)).const_mul _

lemma fullWWeightedRow_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,fullWWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H t ∂heightMeasure)=
      (∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1/2) := by
  have hE : MeasurableSet (fullWSlab H) := fullWSlab_measurable H
  unfold fullWWeightedRow
  rw [integral_indicator hE]
  simp_rw [weightedRowOnLines_eq]
  rw [integral_const_mul]
  unfold centralFullWIntegral
  ring

theorem finiteCentralFullWRows_eq_integral {K : ℕ}
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2< B u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
      detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)< a u+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    let F := fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      fullWWeightedRow S hS hmax (fun i=>(P i).val) (fun i=> hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z (a u) e (H u) t
    Integrable F heightMeasure ∧
      finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  let f (u : FreeRow) (P : ∀i,T i) := fullWWeightedRow S hS hmax
    (fun i=>(P i).val) (fun i=> hT i _ (P i).property) η u W Yp W0 W1 X Y Z (a u) e (H u)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    rcases hbin u hu with ⟨ha,ha',hB,hH,hzero⟩
    exact fullWWeightedRow_integrable e (a u) (B u) (H u) (idx u) he he' ha ha' hB hH
      S hS hmax hfirst _ _ η u (hR u hu) (ψ u) hzero W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P _=> hi u hu P)
  refine ⟨integrable_finsetSum _ hiu,?_⟩
  change finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu,Finset.mul_sum]
  unfold finiteCentralFullWRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=> hi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact (fullWWeightedRow_integral S hS hmax _ _ η u W Yp W0 W1 X Y Z (a u) e (H u)).symm


end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.FullWAggregate -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorUnramifiedMass ; sha256 7229e79198284a6f8a31ab47113bfc32e1ab41acb691847e5fa17bca8afdc03f -/
section



/-! Coefficient masses for the original unramified correction and error. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler ProbeLocal

structure CubicCoefficients where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
def CubicCoefficients.eval (c : CubicCoefficients) (T : ℂ) : ℂ :=
  cubic c.a c.b c.c c.d T
def CubicCoefficients.mass (c : CubicCoefficients) (r : ℝ) : ℝ :=
  cubicMass c.a c.b c.c c.d r

def unramifiedE₀ (Q : ℝ) (A eta v x z : ℂ) : ℂ :=
  markedDefectConstant (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹ (coordD Q eta v x)
def unramifiedE₁ (Q : ℝ) (A eta v x z : ℂ) : ℂ :=
  markedDefectLinear (coordR Q A x z) (coordV Q z) v
    (eta * (Q - 1) * (Q : ℂ) ^ (-x))

theorem coordK_split (Q : ℝ) (eta x w : ℂ) (hQ : 0 < Q) :
    coordK Q eta x w = (eta * (Q - 1) * (Q : ℂ) ^ (-x)) * (Q : ℂ) ^ (-w) := by
  unfold coordK
  rw [show -x - w = -x + -w by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  ring

theorem unramified_marked_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0) :
    unramifiedMarked Q A eta v x w z =
      affine (unramifiedE₀ Q A eta v x z) (unramifiedE₁ Q A eta v x z)
        ((Q : ℂ) ^ (-w)) - coordD Q eta v x := by
  have hh := marked_defect_affine (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordD Q eta v x) v (eta * (Q - 1) * (Q : ℂ) ^ (-x))
    ((Q : ℂ) ^ (-w)) hR hV
  unfold unramifiedMarked
  rw [coordK_split Q eta x w hQ]
  change markedFactor _ _ _ _ (-coordD Q eta v x + v * (Q : ℂ) ^ (-w) * _) 1 = _
  exact eq_sub_of_add_eq hh

def unramifiedDefectCoefficients (Q : ℝ) (A eta v x z : ℂ) : QuadraticCoefficients :=
  let V := coordV Q z
  let D := coordD Q eta v x
  let E₀ := unramifiedE₀ Q A eta v x z
  let E₁ := unramifiedE₁ Q A eta v x z
  ⟨correctionDefectConstant V D E₀, correctionDefectLinear V D v E₀ E₁,
    correctionDefectQuadratic V D v E₁⟩

theorem unramified_defect_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0)
    (hD : 1 - coordD Q eta v x ≠ 0) :
    unramifiedClosed Q A eta v x w z - 1 =
      (unramifiedDefectCoefficients Q A eta v x z).eval ((Q : ℂ) ^ (-w)) := by
  change continuedCorrection (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) - 1 = _
  rw [unramified_marked_expansion Q A eta v x w z hQ hR hV]
  exact correction_defect_quadratic _ _ _ _ _ _ hD

def unramifiedErrorCoefficients (Q : ℝ) (A eta v x z : ℂ) : CubicCoefficients :=
  let V := coordV Q z
  let D := coordD Q eta v x
  let B := star eta * (Q : ℂ) ^ x
  let nu := star v
  let E₀ := unramifiedE₀ Q A eta v x z
  let E₁ := unramifiedE₁ Q A eta v x z
  let c := (1 - V) / (1 - D)
  let a := errorBracketConstant V D B nu E₀
  let b := errorBracketLinear V D B nu E₀ E₁
  let d := errorBracketQuadratic E₁
  ⟨c * a, c * (b - v * a), c * (d - v * b), -c * v * d⟩

theorem unramified_error_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0)
    (hD : 1 - coordD Q eta v x ≠ 0) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1) :
    unramifiedSelected Q A eta v x w z + unramifiedClosed Q A eta v x w z * star v =
      (unramifiedErrorCoefficients Q A eta v x z).eval ((Q : ℂ) ^ (-w)) := by
  have hi := selected_phase_identities Q eta v x w hQ heta hv
  change compensatedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta * (Q : ℂ) ^ x) ((Q : ℂ) ^ (-w)) +
    continuedCorrection (coordV Q z) (coordW Q v w) (coordD Q eta v x)
      (unramifiedMarked Q A eta v x w z) * star v = _
  rw [unramified_marked_expansion Q A eta v x w z hQ hR hV]
  exact compensated_error_cubic _ _ _ _ _ _ _ _ hV hD hi.1
    (PrincipalSlotEstimate.unit_phase_inverse v hv)

theorem unramified_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    1 - coordR Q A x z ≠ 0 ∧ 1 - coordV Q z ≠ 0 ∧ 1 - coordD Q eta v x ≠ 0 := by
  refine ⟨one_sub_ne_zero_of_norm_le_half _
    ((coordR_norm_le Q (by linarith) A x z hA).trans
      (rpow_le_half Q _ hQ (by linarith))),
    one_sub_ne_zero_of_norm_le_half _ (first_region_V_half Q hQ z hz), ?_⟩
  apply one_sub_ne_zero_of_norm_le_half
  exact (coordD_norm_le Q (by linarith) eta v x heta hv).trans
    (rpow_le_half Q _ hQ (by linarith))

/-- Summable unramified correction defect coefficient mass. -/
theorem unramified_defect_coefficient_mass (Q sigma eps : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (heps : 0 < eps) (hx : (51 / 100 : ℝ) ≤ x.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hxw : 1 + eps ≤ x.re + sigma) :
    (unramifiedDefectCoefficients Q A eta v x z).mass (Q ^ (-sigma)) ≤
      720 * Q ^ (-1 - min eps (1 / 50 : ℝ)) := by
  obtain ⟨hR,hV,hD⟩ := unramified_denominators Q A eta v x z hQ hA heta hv hx hz
  let c := unramifiedDefectCoefficients Q A eta v x z
  have hb := quadraticMass_le_of_vertical_bound Q sigma sigma
    (240 * Q ^ (-1 - min eps (1 / 50 : ℝ))) c.a c.b c.c (by linarith) le_rfl (by
      intro w hw
      have hh := unramifiedClosed_first_region_bound Q A eta v x w z eps
        hQ hA heta hv heps hx hz (by rw [hw]; exact hsigma) (by rw [hw]; exact hxw)
      rw [unramified_defect_expansion Q A eta v x w z (by linarith) hR hV hD] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  nlinarith

/-- Actual unramified error coefficient mass, valid on both new reconstruction
lines.  Its prime exponent is strictly below −1/2. -/
theorem unramified_error_coefficient_mass (Q alpha eps sigma : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hsigma : 1 - alpha - 6 * eps ≤ sigma) :
    (unramifiedErrorCoefficients Q A eta v x z).mass (Q ^ (-sigma)) ≤
      2880 * Q ^ (-(51 / 100 : ℝ)) := by
  obtain ⟨hR,hV,hD⟩ := unramified_denominators Q A eta v x z hQ hA heta.le hv.le
    (by rw [hx]; linarith) (by rw [hz])
  let c := unramifiedErrorCoefficients Q A eta v x z
  have hb := cubicMass_le_of_vertical_bound Q (1 - alpha - 6 * eps) sigma
    (720 * Q ^ (-(51 / 100 : ℝ))) c.a c.b c.c c.d (by linarith) hsigma (by
      intro w hw
      have hh := unramifiedSelected_central_error Q alpha eps A eta v x w z
        hQ halpha halpha1 heps heps1 hA heta hv hx hw hz
      rw [unramified_error_expansion Q A eta v x w z (by linarith) hR hV hD heta hv] at hh
      exact hh)
  change cubicMass c.a c.b c.c c.d _ ≤ _
  nlinarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorUnramifiedMass -/

/- BEGIN ORIGINAL MODULE LocalMoment.UniformDensity ; sha256 5c5d6f1a0826b8015cbfeaaed96b9240a80afee5441e18e314cdf49b0a9ee7b7 -/
section


/-! Extend an eventual free-row estimate to every window at least one.
The bounded-window constant is uniform in the row predicate, so it does
not introduce dependence on a selected label, zero bin, or frequency.
The substantive eventual density hypothesis is retained explicitly. -/

namespace OAI
noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ConcretePrimeRowBridge

theorem uniform_free_density_varying_of_eventually {α : Type*}
    (P : α → FreeRow → Prop) (C : ℝ) (ρ : α → ℝ) (hρ : ∀ p, 0 ≤ ρ p)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C * Y ^ ρ p) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C' * Y ^ ρ p := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hevent
  let B : ℝ := max 1 Y₀
  let C' : ℝ := max C (128 * B)
  have hB : 1 ≤ B := le_max_left _ _
  have hC' : 0 < C' := lt_of_lt_of_le (by dsimp [B]; positivity) (le_max_right _ _)
  refine ⟨C', hC', le_max_left _ _, ?_⟩
  intro Y hY p F hF
  by_cases hlarge : Y₀ ≤ Y
  · exact (hY₀ Y hlarge p F hF).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
  · have hc : (F.card : ℝ) ≤ 128 * B :=
      freeRow_count F B hB (fun u hu => (hF u hu).1.trans
        ((le_of_not_ge hlarge).trans (le_max_right _ _)))
    have hp : 1 ≤ Y ^ ρ p := Real.one_le_rpow hY (hρ p)
    calc
      (F.card : ℝ) ≤ 128 * B := hc
      _ ≤ C' := le_max_right _ _
      _ ≤ C' * Y ^ ρ p := by nlinarith

theorem uniform_free_density_of_eventually {α : Type*}
    (P : α → FreeRow → Prop) (C ρ : ℝ) (hρ : 0 ≤ ρ)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C * Y ^ ρ) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C' * Y ^ ρ :=
  uniform_free_density_varying_of_eventually P C (fun _ => ρ) (fun _ => hρ) hevent

/-- A single convolution constant works for every exponent above a fixed
summability threshold, for every finite fixed character list and every bin. -/
theorem raw_density_uniform_exponent (ρ₀ : ℝ) (hρ₀ : 1 / 6 < ρ₀) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ι : Type*} [Fintype ι] (data : ι → RowData)
      (a b T C ρ : ℝ), 0 ≤ C → ρ₀ ≤ ρ →
      (∀ Y : ℝ, 1 ≤ Y → ∀ F : Finset FreeRow,
        (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin data a b T ⟨u.val, u.property.1⟩) →
          (F.card : ℝ) ≤ C * Y ^ ρ) →
      ∀ H : ℝ, 0 < H → ∀ R : Finset ProbePhysical.NonzeroFrequency,
        (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ rawZeroBin data a b T h) →
          (R.card : ℝ) ≤ C * D * H ^ ρ := by
  let w := fun B : HeckeInverseAmplification.NonzeroIdeal =>
    (B.val.absNorm : ℝ) ^ (-6 * ρ₀)
  have hw := ideal_sixth_power_summable ρ₀ hρ₀
  have hw0 : ∀ B, 0 ≤ w B := fun B => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D := (∑' B : HeckeInverseAmplification.NonzeroIdeal, w B) + 1
  have hsum : 0 ≤ ∑' B : HeckeInverseAmplification.NonzeroIdeal, w B := tsum_nonneg hw0
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro ι _ data a b T C ρ hC hρ hfree H hH R hR
  have hc := raw_sixth_convolution data a b T H C ρ hH hC R hR hfree
  have hn (B : HeckeInverseAmplification.NonzeroIdeal) : 1 ≤ (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  simp_rw [sixth_window_power H _ ρ hH (lt_of_lt_of_le zero_lt_one (hn _))] at hc
  calc
    (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd,
        C * (H ^ ρ * (B.val.absNorm : ℝ) ^ (-6 * ρ)) := hc
    _ ≤ ∑ B ∈ (sixthPairs R).image Prod.snd, C * (H ^ ρ * w B) := by
      apply Finset.sum_le_sum
      intro B _
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hH.le _)
      exact Real.rpow_le_rpow_of_exponent_le (hn B) (by linarith)
    _ = (C * H ^ ρ) * ∑ B ∈ (sixthPairs R).image Prod.snd, w B := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ ≤ (C * H ^ ρ) * ∑' B : HeckeInverseAmplification.NonzeroIdeal, w B :=
      mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ (fun B _ => hw0 B)) (by positivity)
    _ ≤ C * D * H ^ ρ := by
      have ht : (∑' B : HeckeInverseAmplification.NonzeroIdeal, w B) ≤ D := by
        dsimp [D]; linarith
      calc
        _ ≤ (C * H ^ ρ) * D := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by ring

/-- The all-integer-row conclusion needs only an eventual free-row density
estimate. No density assumption is required in the bounded residual windows
of the sixth-power convolution. -/
theorem raw_density_from_eventual_free {ι : Type*} [Fintype ι]
    (data : ι → RowData) (a b T C ρ : ℝ) (hρ : 1 / 6 < ρ)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin data a b T ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ C * Y ^ ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 0 < H → ∀ R : Finset ProbePhysical.NonzeroFrequency,
      (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ rawZeroBin data a b T h) →
        (R.card : ℝ) ≤ K * H ^ ρ := by
  let P : Unit → FreeRow → Prop :=
    fun _ u => rawZeroBin data a b T ⟨u.val, u.property.1⟩
  have hevent' : ∀ᶠ Y : ℝ in atTop, ∀ p : Unit, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C * Y ^ ρ := by
    filter_upwards [hevent] with Y hY
    exact fun _ => hY
  obtain ⟨C', hC', _, hfree⟩ := uniform_free_density_of_eventually P C ρ
    (by linarith) hevent'
  obtain ⟨D, hD, hraw⟩ := raw_density_from_free data a b T C' ρ hC'.le hρ
    (fun Y hY => hfree Y hY ())
  exact ⟨C' * D, mul_pos hC' hD, hraw⟩

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.UniformDensity -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyIntegral ; sha256 171b9c78de833f76c7a82b31acacbda7c662bc16ee0b624475e7f507a0c69897 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) (counts : CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤13/16+ζ → d-v≤μ →
      51/100< a → a≤1 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving) := by
  obtain ⟨C,hC,harith⟩ :=
    actual_nonfloor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal counts
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro η
  filter_upwards [harith η,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z harith hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro hmom
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let A : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))
  have hA : 0≤ A := by dsimp [A];positivity
  have hp := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha.le ha' hT
    (by gcongr;omega) S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1)
    T (nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hnext W Y
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp A hA
    (fun t ht=> harith d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
      t ht (hmom t ht))
  apply hp.trans_eq
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZp]
  dsimp only [A]
  calc
    _ = (D*C)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
        (Z^((25/48)*a-181/300+(105/8)*e)*Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))) := by ring
    _ = _ := by rw [←Real.rpow_add hZp];congr 2;ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyIntegral -/

/- BEGIN ORIGINAL MODULE Analytic.ActualJointRow ; sha256 11ba19972ae587c12f2873a64d5c89b21361dbef20ce55ede694d7513d0daba5 -/
section


/-! The first common-support character and the actual second frequency combine
into one integer row. All remaining reciprocity characters lie in a finite
dictionary fixed before the common-support ideals. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open CenteredMomentFirstColumns HeckeFamily

local notation "O" => ActualEisensteinCubic.O

def leftCanceledMask (C D : Ideal O) (n : O) : ℂ :=
  ∏ i : ActiveIndex C D, if activeExponent C D i = 5 then
    if IsCoprime n (activePrimary C D i) then (1 : ℂ) else 0 else 1

def rightCanceledMask (C D : Ideal O) (n : O) : ℂ :=
  ∏ i : ActiveIndex C D, if activeExponent C D i = 1 then
    if IsCoprime n (activePrimary C D i) then (1 : ℂ) else 0 else 1

/-- Both actual first-column signs, followed by any genuine second frequency,
use one integer row and a fixed-dictionary character. The canceled-prime
masks remain literal factors on all supported primary arguments. -/
theorem actual_joint_row_dictionary (C D : Ideal O) (hC : Supported C) :
    ∃ u : Oˣ, ∃ ηL ∈ fixedPhaseDictionary, ∃ ηR ∈ fixedPhaseDictionary,
      activeConductor C D = (u : O) * ∏ i, activePrimary C D i ∧
      ∀ e j n : O, Supported (Ideal.span {n}) → goodLambda ^ 2 ∣ n-1 →
      (leftCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          idealRowHom j (Ideal.span {n}) =
        elementCoeff ηL n *
          idealRowHom (e * (u : O) * leftEffectiveFactor C D * j) (Ideal.span {n}) *
          leftCanceledMask C D n) ∧
      (rightCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          idealRowHom j (Ideal.span {n}) =
        elementCoeff ηR n *
          idealRowHom (e * (u : O) * rightEffectiveFactor C D * j) (Ideal.span {n}) *
          rightCanceledMask C D n) := by
  obtain ⟨u, hu, hcolumns⟩ := actual_first_columns_reconstruct C D hC
  obtain ⟨ηL, hηL, _, hL⟩ := reciprocity_product_in_fixed_dictionary
    (activePrimary C D) (activePrimary_supported C D hC) (activeExponent C D)
  obtain ⟨ηR, hηR, _, hR⟩ := reciprocity_product_in_fixed_dictionary
    (activePrimary C D) (activePrimary_supported C D hC) (fun i => 6-activeExponent C D i)
  refine ⟨u, ηL, hηL, ηR, hηR, hu, ?_⟩
  intro e j n hn hnp
  obtain ⟨hl, hr⟩ := hcolumns e n hn hnp
  constructor
  · rw [hl, hL n hn hnp]
    simp only [idealRowHom_argument_mul]
    unfold leftCanceledMask
    ring
  · rw [hr, hR n hn hnp]
    simp only [idealRowHom_argument_mul]
    unfold rightCanceledMask
    ring

#print axioms actual_joint_row_dictionary

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualJointRow -/
