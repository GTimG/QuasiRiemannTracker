import Candidate.Cycle63.Density.FixedDensity
import Candidate.Target830.Marked.Density.UniformFree
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace OAI.SevenEighths.Target830MarkedDensity
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalRowSource HeckeFiniteDeletion

theorem fixed_dictionary_eventual_free_density {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℝ in atTop,
      ∀ a T : ℝ, 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
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

abbrev DensityParameter := {p : ℝ × ℝ | 81/100 ≤ p.1 ∧ p.1 ≤ 7/8 ∧ 0 ≤ p.2}


end OAI.SevenEighths.Target830MarkedDensity
#print axioms OAI.SevenEighths.Target830MarkedDensity.fixed_dictionary_eventual_free_density
