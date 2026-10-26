/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete padded projector pool is bounded through the original stored
factor pools. No nonzero coefficient or encoded-row divisibility is assumed. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondPhysicalWindows
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondData
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialInput
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondProjectorShell

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularResidualGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentPrimeSlot
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open Cycle61InitialMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.GlobalPhysical
local notation "O"=>ActualEisensteinCubic.O

/-- Changing the literal coefficient does not change the complete residual
pool. The cap uses every stored factor, including zero-profile entries. -/
theorem modified_second_residual_cap {α Label : Type*} [Fintype α] [DecidableEq α]
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ)
    (r : SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l)))
    (N : ℕ) (Z U : ℝ) (hN : Fintype.card (d r.1).slots≤N)
    (hZ : 1≤Z) (hU : 0≤U)
    (hpool : ∀j I,I∈(d r.1).input.pools j→(I.absNorm:ℝ)≤Z^U)
    (L : Ideal O)
    (hL : L∈secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r) :
    L≠0 ∧ (L.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
  apply second_datum_projector_cap (d r.1) N Z U hN hZ hU hpool L
  exact ((mem_second_residual_ideals _ r L).mp hL).1

/-- Both actual common extractions preserve a full factor-pool cap, with
no requirement that the frozen or surviving coefficient be nonzero. -/
theorem two_child_full_pool_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ)
    (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ Y : ℝ)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Y) :
    ∀j I,I∈(child (child s C₁ R₁ B₁ τ₁ t₁) C₂ R₂ B₂ τ₂ t₂).pools j→
      (I.absNorm:ℝ)≤Y :=
  actual_child_pool_cap _ C₂ R₂ B₂ τ₂ t₂ Y
    (actual_child_pool_cap s C₁ R₁ B₁ τ₁ t₁ Y hpool)

/-- A long reference corner has four bounded positive scales. This also
supplies the lower bounds needed to compare each factor to the product. -/
theorem long_corner_caps (Z X₁ X₂ r : ℝ) (hZ : 1≤Z)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hr : 0≤r)
    (hl₁ : Z^r≤X₁) (hl₂ : Z^r≤X₂) (hprod : X₁*X₂≤Z) :
    1≤X₁ ∧ 1≤X₂ ∧ 1≤Z^r ∧ X₁≤Z ∧ X₂≤Z ∧
      X₁*X₂/Z^r≤Z ∧ Z^r≤Z := by
  have hy : 1≤Z^r:=Real.one_le_rpow hZ hr
  have hx₁ : 1≤X₁:=hy.trans hl₁
  have hx₂ : 1≤X₂:=hy.trans hl₂
  have hc₁ : X₁≤Z:= (le_mul_of_one_le_right hX₁.le hx₂).trans hprod
  have hc₂ : X₂≤Z:= (le_mul_of_one_le_left hX₂.le hx₁).trans hprod
  exact ⟨hx₁,hx₂,hy,hc₁,hc₂,(div_le_self (mul_pos hX₁ hX₂).le hy).trans hprod,
    hl₁.trans hc₁⟩

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

/-- The literal canonical initial pools have cap Z² once the four raw
scales are at most Z. The threshold only absorbs the fixed support 9/4. -/
theorem initial_full_pool_cap (hZlarge : 9/4≤Z) (hw : ∀i,w i≤1)
    (hx₁ : X₁≤Z) (hx₂ : X₂≤Z) (hy₁ : Y₁≤Z) (hy₂ : Y₂≤Z) :
    ∀j I,I∈(s).pools j→(I.absNorm:ℝ)≤Z^(2:ℝ) := by
  classical
  have hz₁ : 1≤Z:=by linarith
  have hpay (X : ℝ) (hx : X≤Z) : (9/4)*X≤Z^(2:ℝ) := by
    calc
      _≤(9/4)*Z := mul_le_mul_of_nonneg_left hx (by norm_num)
      _≤Z*Z := mul_le_mul_of_nonneg_right hZlarge hZ.le
      _=Z^(2:ℝ) := by norm_num [pow_two]
  apply actual_completed_pool_cap (s) (Z^(2:ℝ))
  · intro i I hI
    change I∈primePool rayM H 2 (Z^(w i)) at hI
    have hn := (Nat.cast_le.mpr (mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1).2).trans
      (Nat.floor_le (by positivity : 0≤max 1 (2:ℝ)*Z^(w i)))
    have hwZ : Z^(w i)≤Z := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz₁ (hw i)
    calc
      (I.absNorm:ℝ)≤2*Z^(w i) := by simpa only [max_eq_right (by norm_num : (1:ℝ)≤2)] using hn
      _≤Z*Z := mul_le_mul (by linarith) hwZ (Real.rpow_nonneg hZ.le _) hZ.le
      _=Z^(2:ℝ) := by norm_num [pow_two]
  · rfl
  · rfl
  · exact hpay X₁ hx₁
  · exact hpay Y₁ hy₁
  · exact hpay X₂ hx₂
  · exact hpay Y₂ hy₂
end Initial

end
end QRH.Record1252270103Source.RegularResidualGeometry
#print axioms QRH.Record1252270103Source.RegularResidualGeometry.modified_second_residual_cap
#print axioms QRH.Record1252270103Source.RegularResidualGeometry.two_child_full_pool_cap
#print axioms QRH.Record1252270103Source.RegularResidualGeometry.long_corner_caps
#print axioms QRH.Record1252270103Source.RegularResidualGeometry.initial_full_pool_cap
