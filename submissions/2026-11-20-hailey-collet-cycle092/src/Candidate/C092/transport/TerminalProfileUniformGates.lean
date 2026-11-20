/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One original-profile payment for the plain and every opened short row. -/
import Candidate.C092.transport.TerminalProfileUniformRatio
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap ContDiff
open Set OAI OAI.SevenEighths CenteredMomentFiniteProfileExceptional HeckeDetectorDyadicProfiles

/-- The source orders are fixed by the unit-bound supplier BEFORE this bank.
The extra controls are the long-source controls already chosen upstream. -/
theorem actual_unit_profile_bank (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (a b : ℝ) (ha : 0 < a) (lo hi : ℝ) (orders : Finset ℕ)
    (extra : Finset (ℕ×ℕ)) :
    ∃ S : Finset (ℕ×ℕ), (0,0) ∈ S ∧ extra ⊆ S ∧
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ W : 𝓢(ℝ,ℂ), Function.support (W:ℝ→ℂ) ⊆ Icc a b →
      Function.support (unitProfile S C W:ℝ→ℂ) ⊆ Icc a b ∧
      (C*sourceControl S W) • unitProfile S C W = W ∧
      sourceControl extra (unitProfile S C W) ≤ 1 ∧
      ∀ j ∈ orders, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (unitProfile S C W) ((σ:ℂ)+t*Complex.I)‖ ≤ 1 ∧
      ∀ R ∈ Icc (0:ℝ) 4,
      (1+|t|)^j*‖mellin (ratioProfile V (unitProfile S C W) R)
        ((σ:ℂ)+t*Complex.I)‖ ≤ 1 := by
  obtain ⟨T,hT,D,hD,hd⟩ := finite_mellin_controls a b ha lo hi orders
  obtain ⟨S₀,hS₀,hTS₀,E,hE,he⟩ := ratio_controls V hV a b T
  let S := S₀ ∪ extra
  let C := 1+D*(E+1)
  have hC1 : 1 ≤ C := by dsimp [C]; nlinarith
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hDC : D ≤ C := by dsimp [C]; nlinarith
  have hDEC : D*E ≤ C := by dsimp [C]; nlinarith
  have hmono (A : Finset (ℕ×ℕ)) (hA : A ⊆ S) (W : 𝓢(ℝ,ℂ)) :
      sourceControl A W ≤ sourceControl S W := Seminorm.le_def.mp (Finset.sup_mono hA) W
  have hSS : S₀ ⊆ S := Finset.subset_union_left
  refine ⟨S,hSS hS₀,Finset.subset_union_right,C,hC1,?_⟩
  intro W hs
  let Wu := unitProfile S C W
  have hsu : Function.support (Wu:ℝ→ℂ) ⊆ Icc a b := (unitProfile_support S C W).trans hs
  have hctl : sourceControl S Wu ≤ C⁻¹ := unitProfile_control S hC W
  have hCinv : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
  refine ⟨hsu,unitProfile_reconstruct S (hSS hS₀) hC W,
    (hmono extra Finset.subset_union_right Wu).trans (hctl.trans hCinv),?_⟩
  intro j hj σ hσ t
  constructor
  · exact (hd Wu hsu j hj σ hσ t).trans ((mul_le_mul_of_nonneg_left
      ((hmono T (hTS₀.trans hSS) Wu).trans hctl) hD.le).trans
      ((mul_le_mul_of_nonneg_right hDC (inv_nonneg.mpr hC.le)).trans_eq (mul_inv_cancel₀ hC.ne')))
  · intro R hR
    have hratio := he Wu hsu R hR
    have hsratio := (ratioProfile_support V Wu R).trans hsu
    have hb := hd (ratioSchwartz V hV Wu a b hsu R) hsratio j hj σ hσ t
    apply hb.trans
    calc
      D*sourceControl T (ratioSchwartz V hV Wu a b hsu R) ≤
          D*(E*sourceControl S₀ Wu) := mul_le_mul_of_nonneg_left hratio hD.le
      _ ≤ D*(E*C⁻¹) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((hmono S₀ hSS Wu).trans hctl) hE.le) hD.le
      _ = (D*E)*C⁻¹ := by ring
      _ ≤ C*C⁻¹ := mul_le_mul_of_nonneg_right hDEC (inv_nonneg.mpr hC.le)
      _ = 1 := mul_inv_cancel₀ hC.ne'

#print axioms actual_unit_profile_bank
end
end QRH.Cycle092.TerminalProfileUniform
