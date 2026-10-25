/- Copyright (c) 2026 Sil. Apache-2.0.
Arbitrary polynomial saving for the actual original discarded source.
Only explicit numerical scale caps are added to MixedOriginalTail.
-/
import Candidate.SilPrior.FourthPower.MixedOriginalTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedOriginalTailPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentFirstLocalization
open CenteredMomentSectorLocalization CenteredMomentNaturalRadialCutoff
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceInputTailUniform (kernel_inverse_cap eventually_tail_threshold)
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalTail MixedOriginalNormCap
open MixedPoissonLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The order is chosen from fixed numeric budgets, before all actual
coefficients and scales. The 16 in K4 and the division by W are retained.
The exponent 12B is 2B+5B+2B+2B+B. -/
theorem choose_fourth_tail_order (B ξ saving : ℝ) (hB : 0≤B) (hξ : 0<ξ) :
    ∃Adec : ℕ,∀(Z V K W X Tsec : ℝ),1≤Z→0≤V→0<K→0<W→0<X→0<Tsec→
      V≤Z^B→K≤Z^B→W≤Z^B→X≤Z^B→Tsec≤Z^B→W⁻¹≤Z^B→
      V^2*(16*K*W^4)*X^2*((min 1 (kernelReference Tsec 0))^2)⁻¹*
        ((1+Z^(ξ/4))^Adec)⁻¹/W≤64*Z^(-saving) := by
  obtain ⟨Adec,hAdec⟩ := exists_nat_ge ((12*B+saving)/(ξ/4))
  have horder : 12*B-(ξ/4)*(Adec:ℝ)≤-saving := by
    have hh : 12*B+saving≤(Adec:ℝ)*(ξ/4) :=
      (div_le_iff₀ (by linarith : 0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro Z V K W X Tsec hZ hV hK hW hX hT hVc hKc hWc hXc hTc hWic
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hU : 0<Z^B := Real.rpow_pos_of_pos hz _
  have hk : ((min 1 (kernelReference Tsec 0))^2)⁻¹≤4*(Z^B)^2 := by
    convert kernel_inverse_cap 0 Z B Tsec hZ hB hT hTc using 1 <;> norm_num
  have hd := reciprocal_cutoff_bound Z (ξ/4) Adec hz
  have hp : (Z^B)^12=Z^(12*B) := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  calc
    _ = V^2*(16*K*W^4)*X^2*((min 1 (kernelReference Tsec 0))^2)⁻¹*
        ((1+Z^(ξ/4))^Adec)⁻¹*W⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (Z^B)^2*(16*Z^B*(Z^B)^4)*(Z^B)^2*(4*(Z^B)^2)*
        Z^(-(ξ/4)*(Adec:ℝ))*Z^B := by
      gcongr
      all_goals first | exact hVc | exact hKc | exact hWc | exact hXc | exact hk | exact hd | exact hWic | positivity
    _ = 64*(Z^B)^12*Z^(-(ξ/4)*(Adec:ℝ)) := by ring
    _ = 64*Z^(12*B-(ξ/4)*(Adec:ℝ)) := by
      rw [hp,mul_assoc,←Real.rpow_add hz]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (by norm_num)

/-- Arbitrary saving for the literal discarded Fourier density.
The only source-dependent prefactor is homogeneous profileCap squared;
poolCap and sourceNormCap are explicit numerical functions of original
lengths, marked scales and prefix norms, not assumed analytic estimates. -/
theorem original_tail_arbitrary_saving (B ξ saving : ℝ) (hB : 0≤B) (hξ : 0<ξ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,∀ha : 0<a,0≤b→
      ∀(seed : Id)(η : Character)(t K W X Tsec : ℝ),0<K→0<W→0<X→
      poolCap s≤Z^B→sourceNormCap s.P b s.T s.d≤X→
      X≤Z^B→K≤Z^B→W≤Z^B→W⁻¹≤Z^B→Tsec≤Z^B→X^2/(16*K*W^4)≤Tsec→
      ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha seed I*heightCoeff η t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖≤
      C*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving) := by
  obtain ⟨Adec,hdecay⟩ := choose_fourth_tail_order B ξ saving hB hξ
  obtain ⟨control,Ctail,hCtail,htail⟩ := original_discarded_bound Adec
  refine ⟨control,64*Ctail,mul_pos (by norm_num) hCtail,?_⟩
  filter_upwards [eventually_tail_threshold 0 ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι a b s ha hb seed η t K W X Tsec hK hW hX
    hmass hcap hXc hKc hWc hWic hTc hscale
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) (by positivity : 0<16*K*W^4)).trans_le hscale
  have ht := htail ι a b s ha hb seed η t K W X 0 Tsec Z 1 ξ
    hK hW hX hZ.1 le_rfl (by simpa using hcap) hscale (by simpa using hZ.2)
  have hbnd := hdecay Z (poolCap s) K W X Tsec hZ.1.le (poolCap_nonneg s)
    hK hW hX hT hmass hKc hWc hXc hTc hWic
  have hp : 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile := apply_nonneg _ _
  have hfactor : 0≤Ctail*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile :=
    mul_nonneg (mul_nonneg hCtail.le (sq_nonneg _)) hp
  apply ht.trans
  calc
    _ = (Ctail*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
        ((poolCap s)^2*(16*K*W^4)*X^2*((min 1 (kernelReference Tsec 0))^2)⁻¹*
          ((1+Z^(ξ/4))^Adec)⁻¹/W) := by
      simp only [Real.exp_zero,one_mul,massCap,div_eq_mul_inv,mul_inv_rev,mul_pow]
      ring
    _ ≤ (Ctail*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
        (64*Z^(-saving)) := mul_le_mul_of_nonneg_left hbnd hfactor
    _ = _ := by ring

end
end Candidate.SilPrior.FourthPower.MixedOriginalTailPower
