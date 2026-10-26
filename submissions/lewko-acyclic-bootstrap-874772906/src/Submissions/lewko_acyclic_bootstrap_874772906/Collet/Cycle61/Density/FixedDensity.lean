import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.UniformFree
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily

theorem incumbent_beta_upper : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

/-- Actual D+ antecedent: the fixed dictionary, common constant, height
degree and scale threshold are chosen before both live parameters. -/
theorem fixed_dictionary_eventual_free_density {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℝ in atTop,
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ Y ∧ rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩) →
        (rows.card : ℝ) ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hevent⟩ := actual_uniform_free_density_normalized D loss hloss incumbent_beta_upper
  obtain ⟨K, hK, hmod⟩ := D.natural_conductor_bound
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hscale : Tendsto (fun Y : ℝ => K*Y) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hKp).2 tendsto_id
  refine ⟨J, C*K^(1+loss), by positivity, ?_⟩
  filter_upwards [hscale.eventually hevent, eventually_gt_atTop (1 : ℝ)] with Y hY hY1
  intro a T ha ha' hT rows hrows
  have hUp : 0 < K*Y := zero_lt_one.trans hY.1
  have hYp : 0 < Y := zero_lt_one.trans hY1
  have hnorm : ∀ u ∈ rows, rowNorm u ≤ K*Y := by
    intro u hu
    exact (hrows u hu).1.trans (by nlinarith)
  have hcond : ∀ u ∈ rows, ∀ j, ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤ K*Y := by
    intro u hu j
    exact (hmod u j).trans (mul_le_mul_of_nonneg_left (hrows u hu).1 hKp.le)
  have hb := hY.2 a T ha ha' hT rows (fun u hu => ⟨hnorm u hu, (hrows u hu).2⟩) hcond
  have hρ : unmarkedDensity (2*a-1)+loss ≤ 1+loss := by
    linarith [unmarkedDensity_le_one (δ := 2*a-1) (by linarith) (by linarith)]
  apply hb.trans
  rw [Real.mul_rpow hKp.le hYp.le]
  have hp := Real.rpow_le_rpow_of_exponent_le hK hρ
  calc
    _ ≤ C*(1+T)^J*(K^(1+loss)*Y^(unmarkedDensity (2*a-1)+loss)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hYp.le _)) (by positivity)
    _ = _ := by ring

abbrev DensityParameter := {p : ℝ × ℝ | 33/40 ≤ p.1 ∧ p.1 ≤ 7/8 ∧ 0 ≤ p.2}

/-- The raw sixth-power lift of actual D+. Natural Euler holes and the
literal fixed dictionary are preserved by the imported exact convolution. -/
theorem fixed_dictionary_raw_density {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset ProbePhysical.NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ rawZeroBin D.data a (7/8) T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hfree⟩ := fixed_dictionary_eventual_free_density D loss hloss
  let exponent : DensityParameter → ℝ := fun p => unmarkedDensity (2*p.val.1-1)+loss
  let weight : DensityParameter → ℝ := fun p => (1+p.val.2)^J
  have hρ (p : DensityParameter) : 2/7 ≤ exponent p := by
    dsimp [exponent]
    linarith [unmarkedDensity_ge_two_sevenths (show 2*p.val.1-1 ≤ 3/4 by linarith [p.property.2.1])]
  have hw (p : DensityParameter) : 1 ≤ weight p := one_le_pow₀ (by linarith [p.property.2.2])
  have hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : DensityParameter, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧
        rawZeroBin D.data p.val.1 (7/8) p.val.2 ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ C*weight p*Y^exponent p := by
    filter_upwards [hfree] with Y hY
    intro p
    exact hY p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨C', hC', hraw⟩ := raw_density_weighted_from_eventual_free
    (fun _ : DensityParameter => D.data) (fun p => p.val.1) (fun _ => 7/8)
    (fun p => p.val.2) weight exponent C (2/7) (by norm_num) hρ hw hevent
  refine ⟨J, C', hC', ?_⟩
  intro a T ha ha' hT H hH rows hrows
  exact hraw ⟨(a,T), ha, ha', hT⟩ H hH rows hrows

#print axioms incumbent_beta_upper
#print axioms fixed_dictionary_eventual_free_density
#print axioms fixed_dictionary_raw_density
end SevenEighths.LocalMoment
end
end OAI
