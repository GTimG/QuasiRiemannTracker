/- Copyright (c) 2026 Sil. Apache-2.0.
Homogeneous native raw cost with all fixed Fourier moments in its constant.
Monotonicity allows finite family uniformity before moving slot subtypes.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallRawBudget
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedActualNonexceptionalBound

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedSmallCostControl
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondWindowBudget
open CenteredMomentFirstAmplificationChoice
open QuadraticInitialBound
open MixedPrincipalPair MixedInnerExceptionalBlock MixedFirstProfileEnvelope
open MixedActualNonexceptionalBound RepairedSmallRawBudget
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def simpleCost (s : Source ι a b) (C : ℝ) (J : ℕ) (control : Finset (ℕ×ℕ))
    (t₀ V tp Z exponent : ℝ) (η : Character) (seed : Id) : ℝ :=
  C*slotCost s*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^J*heightEnvelope tp^(2*J)*Z^exponent*
    (η.modulus.absNorm:ℝ)*(sourceVolume s/pairNorm s.d)^2/(seed.absNorm:ℝ)

theorem height_envelope_one (tp : ℝ) : 1≤heightEnvelope tp := by
  unfold heightEnvelope
  apply one_le_mul_of_one_le_of_one_le
  · linarith [norm_nonneg tp,Real.pi_pos]
  · linarith [Real.pi_pos]

theorem simple_cost_mono (s : Source ι a b) (C C' : ℝ) (j J : ℕ)
    (U U' : Finset (ℕ×ℕ)) (t₀ V tp Z exponent : ℝ) (η : Character) (seed : Id)
    (hC : 0≤C) (hCC : C≤C') (hj : j≤J) (hU : U⊆U') (hV : 0≤V) (hZ : 0≤Z) :
    simpleCost s C j U t₀ V tp Z exponent η seed≤
      simpleCost s C' J U' t₀ V tp Z exponent η seed := by
  have hC' := hC.trans hCC
  have hcontrols : sourceControl U s.W₁*sourceControl U s.W₂≤
      sourceControl U' s.W₁*sourceControl U' s.W₂ :=
    mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hU) s.W₁)
      (Seminorm.le_def.mp (Finset.sup_mono hU) s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprod := pow_le_pow_left₀
    (mul_nonneg (sourceControl_nonneg U s.W₁) (sourceControl_nonneg U s.W₂)) hcontrols 2
  have hheight : 1≤height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hh := pow_le_pow_right₀ hheight hj
  have ht := pow_le_pow_right₀ (height_envelope_one tp) (Nat.mul_le_mul_left 2 hj)
  have hc : C*slotCost s≤C'*slotCost s :=
    mul_le_mul_of_nonneg_right hCC (slot_cost_nonneg s)
  have hcp := mul_le_mul hc hprod (sq_nonneg _) (mul_nonneg hC' (slot_cost_nonneg s))
  have hcph := mul_le_mul hcp hh (pow_nonneg (zero_le_one.trans hheight) _)
    (mul_nonneg (mul_nonneg hC' (slot_cost_nonneg s)) (sq_nonneg _))
  have hcoef := mul_le_mul hcph ht (pow_nonneg (heightEnvelope_pos tp).le _)
    (mul_nonneg (mul_nonneg (mul_nonneg hC' (slot_cost_nonneg s)) (sq_nonneg _))
      (pow_nonneg (zero_le_one.trans hheight) _))
  have hrest : 0≤Z^exponent*(η.modulus.absNorm:ℝ)*
      (sourceVolume s/pairNorm s.d)^2/(seed.absNorm:ℝ) := by
    have hp := Real.rpow_nonneg hZ exponent
    positivity
  have he := mul_le_mul_of_nonneg_right hcoef hrest
  convert he using 1 <;> unfold simpleCost <;> ring

def fixedNativeCost (slots degree : ℕ) (Cs Cp Cg b : ℝ) : ℝ :=
  4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*Cp*Cg*Cs*
    diagonalControl ballProfile*b^2*(2:ℝ)^slots*profileMoment degree^2

theorem fixed_native_cost_nonneg (slots degree : ℕ) (Cs Cp Cg b : ℝ)
    (hCs : 0≤Cs) (hCp : 0≤Cp) (hCg : 0≤Cg) :
    0≤fixedNativeCost slots degree Cs Cp Cg b := by
  have hd := diagonalControl_nonneg ballProfile
  unfold fixedNativeCost
  positivity

theorem closed_budget_eq_simple (s : Source ι a b) (degree : ℕ)
    (control : Finset (ℕ×ℕ)) (Cs Cp Cg Z exponent t₀ V tp : ℝ)
    (η : Character) (seed : Id) :
    closedBudget (Fintype.card ι) degree Cp Cg Z exponent
      (Cs*slotCost s*diagonalControl ballProfile*
        (sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^degree) b (sourceVolume s) tp 1 η seed s.d=
      simpleCost s (fixedNativeCost (Fintype.card ι) degree Cs Cp Cg b)
        degree control t₀ V tp Z exponent η seed := by
  unfold closedBudget simpleCost fixedNativeCost
  rw [div_pow]
  ring

end
end Candidate.FourthPower.RepairedSmallCostControl
