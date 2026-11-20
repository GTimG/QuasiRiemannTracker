/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   One threshold, before all authentic fixed labels and supported rows. -/
import Candidate.C092.transport.FixedFrameConductorCapsCore
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentFirstPhysicalSource CenteredMomentFirstSourceConductorCaps
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
namespace QRH.Cycle092.FixedFrameConductorCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

def conductorConstant (η : Character) : ℝ :=
  2*fixedPresentationCost*(η.modulus.absNorm:ℝ)*((Ideal.span {(12:O)}).absNorm:ℝ)^2*
    (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

/-- Original left and right first families give the same uniform cap on the
pre-family child character used by the H15 completion. -/
lemma first_base_modulus (η : Character) (C E : Id) (hC : Supported C)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C E)) (ξ₁ ξ₂ : RayFourExpansion.RayCharacter)
    (F : FixedPair η C E hC U ξ₁ ξ₂) (ρ : Character) (hρ : ρ=F.left ∨ ρ=F.right)
    (hZ : 1<Z) (hcap : (C.absNorm:ℝ)≤Z^(8:ℝ)) :
    (ρ.modulus.absNorm:ℝ) ≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*Z^(16:ℝ) := by
  have hm := fixed_pair_caps η C E hC U ξ₁ ξ₂ F
  have hh : (ρ.modulus.absNorm:ℝ) ≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    rcases hρ with rfl|rfl
    · exact hm.1
    · exact hm.2
  apply hh.trans
  have hfp := fixedPresentationCost_pos.le
  have hn := Nat.cast_nonneg (α:=ℝ) η.modulus.absNorm
  calc
    _ ≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*(Z^(8:ℝ))^2 := by
      gcongr
    _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hZ).le]; norm_num

/-- This is the literal original conductor, including the source puncture
and two genuine ray children. The ball supplies the same row z. -/
theorem conductor_from_native_caps (η ρ : Character) (ξ χ : RayFourExpansion.RayCharacter)
    (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (hf : Fits η rs x) (hH : commonH rs≤19/10)
    (hρ : (ρ.modulus.absNorm:ℝ) ≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*Z^(16:ℝ))
    (hR : (s.R.absNorm:ℝ) ≤ Z^(8:ℝ)) (z : O)
    (hz : ((Ideal.span {z}).absNorm:ℝ) ≤ 2*dyadicScale (x.n 1)) :
    (HeckeRowClosure.rowConductorBound (childCharacter (childCharacter ρ ξ) χ)
      (FixedCubeGauss.nativeSourceMask s) 1 (x.twist*z):ℝ) ≤
      conductorConstant η * Z^(259/10:ℝ) := by
  have hm := (second_child_modulus ρ ξ χ).trans
    (mul_le_mul_of_nonneg_right hρ (sq_nonneg _))
  have hr := supported_row_cap rs x hf hH z hz
  have hfp := fixedPresentationCost_pos.le
  have hη := Nat.cast_nonneg (α:=ℝ) η.modulus.absNorm
  have h8 := Real.rpow_nonneg (zero_lt_one.trans rs.hZ).le (8:ℝ)
  have h16 := Real.rpow_nonneg (zero_lt_one.trans rs.hZ).le (16:ℝ)
  rw [row_conductor_eq]
  calc
    _ ≤ (fixedPresentationCost*(η.modulus.absNorm:ℝ)*Z^(16:ℝ)*
      ((Ideal.span {(12:O)}).absNorm:ℝ)^2)*(Ideal.span {fixedBadMask}).absNorm*Z^(8:ℝ)*
        (Ideal.span {(72:O)}).absNorm*(2*Z^(19/10:ℝ)) := by
      gcongr <;> positivity
    _ = conductorConstant η * Z^(259/10:ℝ) := by
      rw [show (259/10:ℝ)=16+8+19/10 by norm_num,
        Real.rpow_add (zero_lt_one.trans rs.hZ),Real.rpow_add (zero_lt_one.trans rs.hZ)]
      unfold conductorConstant
      ring

/-- The threshold depends only on the original base, and precedes every
first family, second family, label, allocation and row. -/
theorem eventually_actual_conductor (η : Character) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      ∀ (C E : Id) (hC : Supported C) (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C E))
      (ξ₁ ξ₂ : RayFourExpansion.RayCharacter) (F : FixedPair η C E hC U ξ₁ ξ₂)
      (ρ : Character), (ρ=F.left ∨ ρ=F.right) → (C.absNorm:ℝ)≤Z^(8:ℝ) →
      ∀ {L mesh : ℝ} {θ : GData L} (s : Source (Fin θ.N) θ.a θ.b)
      (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z), Fits η rs x → commonH rs≤19/10 →
      (s.R.absNorm:ℝ)≤Z^(8:ℝ) → ∀ (ξ χ : RayFourExpansion.RayCharacter) (z : O),
      ((Ideal.span {z}).absNorm:ℝ)≤2*dyadicScale (x.n 1) →
      (HeckeRowClosure.rowConductorBound (childCharacter (childCharacter ρ ξ) χ)
        (FixedCubeGauss.nativeSourceMask s) 1 (x.twist*z):ℝ) ≤ Z^(27:ℝ) := by
  filter_upwards [eventually_ge_atTop (conductorConstant η),eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro C E hC U ξ₁ ξ₂ F ρ hρ hcap L mesh θ s rs x hf hH hR ξ χ z hz
  have hb := conductor_from_native_caps η ρ ξ χ s rs x hf hH
    (first_base_modulus η C E hC U ξ₁ ξ₂ F ρ hρ hZ hcap) hR z hz
  apply hb.trans
  calc
    _ ≤ Z*Z^(259/10:ℝ) := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _ = Z^(269/10:ℝ) := by rw [show (269/10:ℝ)=1+259/10 by norm_num,
      Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)

#print axioms first_base_modulus
#print axioms conductor_from_native_caps
#print axioms eventually_actual_conductor
end QRH.Cycle092.FixedFrameConductorCaps
