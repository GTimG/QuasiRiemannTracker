/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed unit-ideal test separates the reflected long column from an arbitrary
short witness. Its polynomial at scale one is exactly one for any character. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformRetainedEnergy
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic CenteredMomentScaleSupremum Set
namespace QRH.Cycle092.MixedScale
noncomputable section
set_option autoImplicit false

def unitWindow (x : ℝ) : ℂ := CompletedHeight.positiveCutoff 1 1 zero_lt_one x

theorem unitWindow_smooth : ContDiff ℝ ∞ unitWindow :=
  Complex.ofRealCLM.contDiff.comp (CompletedHeight.positiveCutoff 1 1 zero_lt_one).contDiff

theorem unitWindow_support : Function.support unitWindow ⊆ Icc (1/2:ℝ) (3/2) := by
  intro x hx
  have hmem : x ∈ Function.support (CompletedHeight.positiveCutoff 1 1 zero_lt_one) := by
    intro he; exact hx (by change ((_ : ℝ):ℂ)=0; rw [he,Complex.ofReal_zero])
  rw [(CompletedHeight.positiveCutoff 1 1 zero_lt_one).support_eq] at hmem
  change dist x ((1+max (1:ℝ) 1)/2)<(max (1:ℝ) 1-1)/2+1/2 at hmem
  rw [Real.dist_eq,abs_lt] at hmem
  norm_num at hmem
  exact ⟨by linarith only [hmem.1],by linarith only [hmem.2]⟩

theorem one_ideal_only (χ : Character) (W : ℝ→ℂ) (hs : Function.support W ⊆ Icc (1/2:ℝ) (3/2)) :
    polynomial χ false W 1 0 0 = W 1 := by
  let u : HeckeDyadic.NonzeroIdeal := ⟨1,one_ne_zero⟩
  unfold polynomial
  rw [tsum_eq_single u]
  · simp [summand,u,HeckeDyadic.norm,coefficient,HeckeDyadic.shift,←Ideal.one_eq_top]
  · intro I hI
    have hI1 : I.val ≠ 1 := fun h => hI (Subtype.ext h)
    have hnorm : 2 ≤ I.val.absNorm := by
      have hp := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
      have hne : I.val.absNorm ≠ 1 := fun h => hI1 ((Ideal.absNorm_eq_one_iff.mp h).trans Ideal.one_eq_top.symm)
      omega
    have hW : W (norm I) = 0 := by
      by_contra h
      have hh := (hs h).2
      have h2 : (2:ℝ) ≤ norm I := by unfold HeckeDyadic.norm; exact_mod_cast hnorm
      linarith
    simp only [summand,div_one,hW,mul_zero,zero_mul]

theorem unitWindow_polynomial (χ : Character) : polynomial χ false unitWindow 1 0 0 = 1 := by
  rw [one_ideal_only χ _ unitWindow_support]
  change ((CompletedHeight.positiveCutoff 1 1 zero_lt_one 1:ℝ):ℂ)=1
  rw [CompletedHeight.positiveCutoff_one 1 1 zero_lt_one 1 ⟨le_rfl,le_rfl⟩,Complex.ofReal_one]

#print axioms unitWindow_polynomial
end
end QRH.Cycle092.MixedScale
