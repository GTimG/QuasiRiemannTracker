/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedFrameRowWitnessLabel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
import Candidate.C092.transport.ColoredGaussFrameProviderOriginalFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentChildRows CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentFirstPhysicalSource CenteredMomentFirstSourceConductorCaps
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
namespace QRH.Cycle092.FixedFrameConductorCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

/-- The raised native cutoff bounds the actual prepacked H15 row. -/
theorem supported_row_cap {η : Character} (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (hf : Fits η rs x) (hH : commonH rs ≤ 19/10) (z : O)
    (hz : ((Ideal.span {z}).absNorm:ℝ) ≤ 2*dyadicScale (x.n 1)) :
    ((Ideal.span {x.twist*z}).absNorm:ℝ) ≤ 2*Z^(19/10:ℝ) := by
  have hN := absNorm_span_pos x.twist hf.twist_ne
  have hmul : 0 < ((Ideal.span {x.twist}).absNorm:ℝ)*dyadicScale (x.n 1) :=
    mul_pos hN (dyadicScale_pos _)
  have hc : ((Ideal.span {x.twist}).absNorm:ℝ)*dyadicScale (x.n 1) ≤ Z^(cutoffLog rs) :=
    (Real.logb_le_iff_le_rpow rs.hZ hmul).mp hf.dual
  have hV : (1:ℝ) ≤ (Ideal.span {rs.V₀}).absNorm := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr rs.hV₀)))
  have ht : 0 ≤ rs.twistLog := Real.logb_nonneg rs.hZ hV
  have hh : cutoffLog rs ≤ 19/10 := by unfold commonH at hH; linarith
  rw [absNorm_span_mul]
  calc
    _ ≤ ((Ideal.span {x.twist}).absNorm:ℝ)*(2*dyadicScale (x.n 1)) :=
      mul_le_mul_of_nonneg_left hz hN.le
    _ = 2*(((Ideal.span {x.twist}).absNorm:ℝ)*dyadicScale (x.n 1)) := by ring
    _ ≤ 2*Z^(cutoffLog rs) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le rs.hZ.le hh) (by norm_num)

lemma native_mask_norm {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) :
    ((Ideal.span {FixedCubeGauss.nativeSourceMask s}).absNorm:ℝ) =
      ((Ideal.span {fixedBadMask}).absNorm:ℝ)*(s.R.absNorm:ℝ) := by
  rw [FixedCubeGauss.nativeSourceMask,←Ideal.span_singleton_mul_span_singleton,
    map_mul,ConcretePrimeRowBridge.span_idealGenerator,Nat.cast_mul]

/-- Two true ray children cost two fixed ray moduli, independently of labels. -/
lemma second_child_modulus (ρ : Character) (ξ χ : RayFourExpansion.RayCharacter) :
    ((childCharacter (childCharacter ρ ξ) χ).modulus.absNorm:ℝ) ≤
      (ρ.modulus.absNorm:ℝ)*((Ideal.span {(12:O)}).absNorm:ℝ)^2 := by
  have h := (child_modulus_bound (childCharacter ρ ξ) χ).trans
    (Nat.mul_le_mul_right _ (child_modulus_bound ρ ξ))
  have hh : ((childCharacter (childCharacter ρ ξ) χ).modulus.absNorm:ℝ) ≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast h
  convert hh using 1 <;> ring

/-- Exact original conductor expression, with the real completion mask. -/
lemma row_conductor_eq {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b)
    (ρ : Character) (A z : O) :
    (HeckeRowClosure.rowConductorBound ρ (FixedCubeGauss.nativeSourceMask s) 1 (A*z):ℝ) =
      (ρ.modulus.absNorm:ℝ)*((Ideal.span {fixedBadMask}).absNorm:ℝ)*s.R.absNorm*
        (Ideal.span {(72:O)}).absNorm*(Ideal.span {A*z}).absNorm := by
  simp only [HeckeRowClosure.rowConductorBound,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow,one_mul,
    Nat.cast_mul,native_mask_norm]
  ring

#print axioms supported_row_cap
#print axioms native_mask_norm
#print axioms second_child_modulus
#print axioms row_conductor_eq
end QRH.Cycle092.FixedFrameConductorCaps
