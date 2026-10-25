/- Copyright (c) 2026 Sil. Apache-2.0.
Concrete source scale caps for the arbitrary-saving discarded tail.
The original prefix denominator is retained before the uniform threshold.
-/
import Candidate.Feedback.FourthPower.MixedOriginalTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedOriginalTailCaps
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedOriginalTail MixedOriginalNormCap MixedCommonCoefficient
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Explicit constants, with the full original prefix norm still in
the denominator. No bound on a coefficient or energy is a premise. -/
theorem source_caps_with_prefix (s : Source ι a b) (N : ℕ) (Z L Pexp : ℝ)
    (hZ : 0<Z) (hcard : Fintype.card ι≤N)
    (hX₁ : s.X₁≤Z^L) (hX₂ : s.X₂≤Z^L)
    (hY₁ : s.Y₁≤Z^L) (hY₂ : s.Y₂≤Z^L) (hP : (∏i,s.P i)≤Z^Pexp) :
    poolCap s≤(4*(128*b)^2*(256:ℝ)^N)*Z^(2*L+Pexp)/pairNorm s.d ∧
    sourceNormCap s.P b s.T s.d≤(b^2*(2:ℝ)^N)*Z^(2*L+Pexp)/pairNorm s.d := by
  have hx₁ : 0≤s.X₁ := (s.hL.trans_le s.hX₁).le
  have hx₂ : 0≤s.X₂ := (s.hL.trans_le s.hX₂).le
  have hy₁ : 0≤s.Y₁ := (s.hL.trans_le s.hY₁).le
  have hy₂ : 0≤s.Y₂ := (s.hL.trans_le s.hY₂).le
  have hp : 0≤∏i,s.P i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))
  have hden : 0<pairNorm s.d := pairNorm_pos s.hd.1 s.hd.2
  have h256 : (256:ℝ)^Fintype.card ι≤256^N := pow_le_pow_right₀ (by norm_num) hcard
  have h2 : (2:ℝ)^Fintype.card ι≤2^N := pow_le_pow_right₀ (by norm_num) hcard
  have hprod256 : (∏i,256*s.P i)≤(256:ℝ)^N*Z^Pexp := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    exact mul_le_mul h256 hP hp (by positivity)
  have hprod2 : (∏i,2*s.P i)≤(2:ℝ)^N*Z^Pexp := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    exact mul_le_mul h2 hP hp (by positivity)
  have hpool : (s.X₁+s.Y₁)*(s.X₂+s.Y₂)≤4*(Z^L)^2 := by
    calc
      _ ≤ (2*Z^L)*(2*Z^L) := mul_le_mul (by linarith) (by linarith)
        (add_nonneg hx₂ hy₂) (by positivity)
      _ = _ := by ring
  have hT : s.T≤(Z^L)^2 := by
    rw [←s.hpX,pow_two]
    exact mul_le_mul hX₁ hX₂ hx₂ (Real.rpow_nonneg hZ.le _)
  have hpower : (Z^L)^2*Z^Pexp=Z^(2*L+Pexp) := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  constructor
  · unfold poolCap
    calc
      _ = ((128*b)^2*((s.X₁+s.Y₁)*(s.X₂+s.Y₂))*(∏i,256*s.P i))/pairNorm s.d := by ring
      _ ≤ ((128*b)^2*(4*(Z^L)^2)*((256:ℝ)^N*Z^Pexp))/pairNorm s.d := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpool (sq_nonneg _)) hprod256
          (Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i))))
          (by positivity)
      _ = (4*(128*b)^2*(256:ℝ)^N)*((Z^L)^2*Z^Pexp)/pairNorm s.d := by ring
      _ = _ := by rw [hpower]
  · unfold sourceNormCap
    calc
      _ = (b^2*s.T*(∏i,2*s.P i))/pairNorm s.d := by ring
      _ ≤ (b^2*(Z^L)^2*((2:ℝ)^N*Z^Pexp))/pairNorm s.d := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hT (sq_nonneg _)) hprod2
          (Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i))))
          (by positivity)
      _ = (b^2*(2:ℝ)^N)*((Z^L)^2*Z^Pexp)/pairNorm s.d := by ring
      _ = _ := by rw [hpower]

/-- The same threshold works for every original type, profile, prefix,
height and source whose ordinary lengths and marked product obey the
displayed scale caps. Only fixed b and N enter the absorbed constants. -/
theorem eventually_source_caps (N : ℕ) (b L Pexp ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      (∏i,s.P i)≤Z^Pexp→
      poolCap s≤Z^(2*L+Pexp+ε) ∧ sourceNormCap s.P b s.T s.d≤Z^(2*L+Pexp+ε) := by
  let Cpool : ℝ := 4*(128*b)^2*(256:ℝ)^N
  let Cnorm : ℝ := b^2*(2:ℝ)^N
  have hc : ∀ᶠZ : ℝ in atTop,max Cpool Cnorm≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (max Cpool Cnorm)
  filter_upwards [hc,Filter.eventually_gt_atTop (1:ℝ)] with Z hconstant hZ
  refine ⟨hZ,?_⟩
  intro ι instι a s hcard hX₁ hX₂ hY₁ hY₂ hP
  have hz : 0<Z := zero_lt_one.trans hZ
  have hcaps := source_caps_with_prefix s N Z L Pexp hz hcard hX₁ hX₂ hY₁ hY₂ hP
  have hden : (1:ℝ)≤pairNorm s.d := by
    have hn : (1:ℝ)≤((s.d.1*s.d.2).absNorm:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero s.hd.1 s.hd.2))
    simpa only [pairNorm,map_mul,Nat.cast_mul] using hn
  have hcp : Cpool≤Z^ε := (le_max_left _ _).trans hconstant
  have hcn : Cnorm≤Z^ε := (le_max_right _ _).trans hconstant
  have hp : 0≤Z^(2*L+Pexp) := Real.rpow_nonneg hz.le _
  have hpower : Z^ε*Z^(2*L+Pexp)=Z^(2*L+Pexp+ε) := by
    rw [←Real.rpow_add hz]
    congr 1
    ring
  constructor
  · calc
      poolCap s ≤ Cpool*Z^(2*L+Pexp)/pairNorm s.d := hcaps.1
      _ ≤ Cpool*Z^(2*L+Pexp) := div_le_self (by dsimp only [Cpool];positivity) hden
      _ ≤ Z^ε*Z^(2*L+Pexp) := mul_le_mul_of_nonneg_right hcp hp
      _ = _ := hpower
  · calc
      sourceNormCap s.P b s.T s.d ≤ Cnorm*Z^(2*L+Pexp)/pairNorm s.d := hcaps.2
      _ ≤ Cnorm*Z^(2*L+Pexp) := div_le_self (by dsimp only [Cnorm];positivity) hden
      _ ≤ Z^ε*Z^(2*L+Pexp) := mul_le_mul_of_nonneg_right hcn hp
      _ = _ := hpower

end
end Candidate.Feedback.FourthPower.MixedOriginalTailCaps
