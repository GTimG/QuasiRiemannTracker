/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace QRH.Record12518109Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

theorem length_rpow_base (Z X M : ℝ) (hZ : 0<Z) :
    length (Z^M) X=length Z X/M := by
  unfold length Real.logb
  rw [Real.log_rpow hZ]
  ring

theorem SourceFace.admissible_div {f : SourceFace} {m₁ m₂ s M : ℝ}
    (hM : 0<M) (h : f.Admissible m₁ m₂ s M) :
    f.Admissible (m₁/M) (m₂/M) (s/M) 1 := by
  rcases h with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [mul_one]; exact (le_div_iff₀ hM).mpr h₁
  · simp only [mul_one]; exact (div_le_iff₀ hM).mpr h₂
  · simp only [mul_one]; exact (le_div_iff₀ hM).mpr h₃
  · simp only [mul_one]; exact (div_le_iff₀ hM).mpr h₄
  · simp only [mul_one]; exact (le_div_iff₀ hM).mpr h₅
  · simp only [mul_one]; exact (div_le_iff₀ hM).mpr h₆
  · have he : m₁/M+m₂/M+f.lam*(s/M)=(m₁+m₂+f.lam*s)/M := by ring
    rw [he,mul_one]
    exact (div_le_iff₀ hM).mpr h₇

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- Changing the common base preserves the actual prime pools, annular slots,
initialKeep and whole-product normalization exactly. -/
theorem initialAffineAt_rescale (face : SourceFace) (W : ℝ→ℂ)
    (bslot a b bΦ mesh unitMesh σlo σhi M ε unitε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (hZ : 1<Z) (hM : 0<M) (hC : 0≤C) (hmesh : mesh≤unitMesh*M)
    (hε : M*unitε≤ε)
    (hsource : InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ unitMesh
      σlo σhi 1 1 unitε (Z^M) η η₀ Q degree S C) :
    InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ mesh
      σlo σhi M M ε Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M' hMlo hMhi
    Φ hΦ hpΦ p X₁ X₂ hX₁ hX₂ hadm
  have heM : M'=M := le_antisymm hMhi hMlo
  subst M'
  have hnorm : ∀u : ℝ,(Z^M)^(u/M)=Z^u := by
    intro u
    rw [←Real.rpow_mul (by linarith : 0≤Z)]
    congr 1
    field_simp
  have hadm' : face.Admissible (length (Z^M) X₁) (length (Z^M) X₂)
      (∑i,w i/M) 1 := by
    rw [length_rpow_base Z X₁ M (by linarith),
      length_rpow_base Z X₂ M (by linarith),←Finset.sum_div]
    exact SourceFace.admissible_div hM hadm
  have he := hsource T θ (fun i=>w i/M) σ v t height
    (fun i=>div_nonneg (hw i) hM.le)
    (fun i=>(div_le_iff₀ hM).mpr ((hwm i).trans hmesh))
    hσlo hσhi hh hv 1 le_rfl le_rfl Φ hΦ hpΦ p X₁ X₂ hX₁ hX₂ hadm'
  simp only [hnorm,Real.rpow_one] at he
  apply he.trans
  have hpower : (Z^M)^(1+unitε)≤Z^(M+ε) := by
    rw [←Real.rpow_mul (by linarith : 0≤Z)]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith only [hε]
  have hfactor : 0≤C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
      (1+|t|+height)^degree := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity
  exact mul_le_mul_of_nonneg_left hpower hfactor

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.initialAffineAt_rescale
