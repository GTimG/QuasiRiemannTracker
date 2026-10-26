/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual affine initial geometry and the literal second projector pool use
one cardinality-independent polynomial exponent. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialPhysicalPoolBounds
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondData
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondPhysicalWindows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialPhysical
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentEnergyBands CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open Cycle61InitialMass QRH.Record1252270103Source.High.GlobalPhysical
local notation "O"=>ActualEisensteinCubic.O

/-- The genuine full-pool cap propagates to the complete second residual
projector pool; the modified coefficient does not change these finite sets. -/
theorem modified_second_residual_full_cap {α Label : Type*} [Fintype α] [DecidableEq α]
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ)
    (r : SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l))) (Y : ℝ)
    (hpool : ∀I∈finiteColumns (Fintype.piFinset (d r.1).input.pools),(I.absNorm:ℝ)≤Y)
    (L : Ideal O)
    (hL : L∈secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r) :
    L≠0 ∧ (L.absNorm:ℝ)≤Y := by
  apply second_block_projector_norm (modifiedDatumBlock (d r.1) (modifier r.1)) Y _ L
    ((mem_second_residual_ideals _ r L).mp hL).1
  intro I hI
  apply hpool I
  dsimp only [modifiedDatumBlock,SecondInputDatum.block,originalSecondBlock] at hI
  obtain ⟨v,hv,he⟩:=Finset.mem_image.mp hI
  exact Finset.mem_image.mpr ⟨v,by simpa only [Fintype.mem_piFinset] using hv,he⟩

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

/-- All raw and marked-product cap premises are discharged from the
literal global face and long-reference conditions. The original N appears
only in the fixed multiplicative constant. -/
theorem initial_full_column_cap_of_global_face (N : ℕ) (hN : Fintype.card ι≤N)
    (B lam cap : ℝ) (hZ1 : 1<Z) (hB : B≤1) (hlam : 0≤lam) (hcap : cap≤1)
    (hw : ∀i,0≤w i)
    (hadm : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hy₂ : 1≤Y₂) (hl₁ : Y₂≤X₁) (hl₂ : Y₂≤X₂) :
    ∀I∈finiteColumns (Fintype.piFinset (s).pools),
      (I.absNorm:ℝ)≤(2:ℝ)^N*(9/4)^2*Z^(3:ℝ) := by
  have hs : 0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hp : X₁*X₂≤Z:=RegularResidualGeometry.global_face_product_cap B lam cap Z X₁ X₂ (∑i,w i)
    hZ1 hX₁ hX₂ hB hlam hs hadm
  have hx₁ : X₁≤Z:=(le_mul_of_one_le_right hX₁.le (hy₂.trans hl₂)).trans hp
  have hx₂ : X₂≤Z:=(le_mul_of_one_le_left hX₂.le (hy₂.trans hl₁)).trans hp
  have hy₁ : Y₁≤Z:=by
    apply (le_mul_of_one_le_right hY₁.le hy₂).trans
    rw [hprod]
    exact hp
  have hslot : ∑i,w i≤cap:=by simpa only [globalFace,mul_one] using hadm.2.2.2.2.2.1
  exact initial_full_column_cap rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod N hN hZ1.le hx₁ hx₂ hy₁ (hl₂.trans hx₂)
    (hslot.trans hcap)
end Initial
end
end QRH.Record1252270103Source.InitialPhysical
#print axioms QRH.Record1252270103Source.InitialPhysical.modified_second_residual_full_cap
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_full_column_cap_of_global_face
