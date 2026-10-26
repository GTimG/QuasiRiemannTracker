/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual initial affine face discharges the complete padded pool cap. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularResidualGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularResidualGeometry
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEnergyBands
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
local notation "O"=>ActualEisensteinCubic.O

/-- The clipped global affine face bounds the actual positive plain product. -/
theorem global_face_product_cap (B lam cap Z X₁ X₂ width : ℝ)
    (hZ : 1<Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hB : B≤1) (hlam : 0≤lam) (hw : 0≤width)
    (hadm : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) width 1) :
    X₁*X₂≤Z := by
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hx (X : ℝ) : X≤Z^(length Z X) := by
    rw [length,Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hbudget : length Z X₁+length Z X₂+lam*width≤B := by
    simpa only [globalFace,mul_one] using hadm.2.2.2.2.2.2
  have hsum : length Z X₁+length Z X₂≤1:=by linarith [mul_nonneg hlam hw]
  calc
    _≤Z^(length Z X₁)*Z^(length Z X₂) :=
      mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂) := (Real.rpow_add hz _ _).symm
    _≤Z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le hsum

section Initial
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable (p : Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

/-- The genuine long initial supplier needs only its literal face and
reference inequalities. All stored pools, including padded zeros, have cap Z². -/
theorem initial_full_pool_cap_of_global_face (B lam cap : ℝ)
    (hZlarge : 9/4≤Z) (hB : B≤1) (hlam : 0≤lam) (hcap : cap≤1)
    (hw : ∀i,0≤w i)
    (hadm : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hy₂ : 1≤Y₂) (hl₁ : Y₂≤X₁) (hl₂ : Y₂≤X₂) :
    ∀j I,I∈(s).pools j→(I.absNorm:ℝ)≤Z^(2:ℝ) := by
  have hZ1 : 1<Z:=by linarith
  have hs : 0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hp : X₁*X₂≤Z:=global_face_product_cap B lam cap Z X₁ X₂ (∑i,w i)
    hZ1 hX₁ hX₂ hB hlam hs hadm
  have hx₁ : X₁≤Z:=(le_mul_of_one_le_right hX₁.le (hy₂.trans hl₂)).trans hp
  have hx₂ : X₂≤Z:=(le_mul_of_one_le_left hX₂.le (hy₂.trans hl₁)).trans hp
  have hy₁ : Y₁≤Z:=by
    apply (le_mul_of_one_le_right hY₁.le hy₂).trans
    rw [hprod]
    exact hp
  have hslot : ∑i,w i≤cap:=by simpa only [globalFace,mul_one] using hadm.2.2.2.2.2.1
  have hwi : ∀i,w i≤1:=fun i=>(Finset.single_le_sum (fun j _=>hw j) (Finset.mem_univ i)).trans
    (hslot.trans hcap)
  exact initial_full_pool_cap rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hZlarge hwi hx₁ hx₂ hy₁ (hl₂.trans hx₂)
end Initial
end
end QRH.Record1252270103Source.RegularResidualGeometry
#print axioms QRH.Record1252270103Source.RegularResidualGeometry.global_face_product_cap
#print axioms QRH.Record1252270103Source.RegularResidualGeometry.initial_full_pool_cap_of_global_face
