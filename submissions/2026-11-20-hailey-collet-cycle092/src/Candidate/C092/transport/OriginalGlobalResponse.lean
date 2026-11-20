/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
At the established global zero-free boundary every retained regular row has
squared prime response at most 3/4, including all zero-width descriptors. -/
import Candidate.C092.transport.LowActualSource
import Candidate.C092.transport.SmallCoreMonotone
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeGlobal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

namespace QRH.Cycle092.GlobalResponse
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily ConcretePrimeRowBridge ConcreteTraceCRT
open OAI.SevenEighths.Cycle61Moment.LowBranch
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_OriginalGlobalResponse_b71c9005c9fd4794_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem global_low_gate (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    {e : ℝ} (he : 0 < e) (T : ℝ) (z : O)
    (hΦ : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0) :
    ActualLow M H hH s η₀ hQM hQη (7/8) e T z := by
  have hb := HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))
  refine ⟨hΦ,?_⟩; intro hz θ
  exact lt_of_le_of_lt ((CenteredMomentPrimeGlobal.zeroMaximum_le_beta _ _ T hβ).trans hb)
    (by linarith only [he])

theorem all_regular_low {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (buf bΦ : ℝ) (hb : 0 < buf) (hφ : 0 ≤ bΦ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ s : NaturalState U 0 bΦ, s.width ≤ 2 →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
      (θ : Slot → RayQuotient.Characters M H) (w σ v : Slot → ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) → (∀ j, w j ≤ 1) → (∀ j, σ j = 33/50) →
      (∀ j, |v j| ≤ height) → |t|+height ≤ U^(1/2:ℝ) →
      ∀ z : O, s.radial.keep z → s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
        LowRows Finset.univ s.character s.mask 1 t U (3/4) (C*U^buf) w
          (originalPools M H 2 U w) (originalCoefficients M H hH η₀ θ W U w σ v)
          (fun j => U^(w j)) z := by
  let ε := buf/6
  let e := min (1/2000) (ε/32)
  have hε : 0 < ε := div_pos hb (by norm_num)
  have he : 0 < e := lt_min (by norm_num) (div_pos hε (by norm_num))
  have hsmall : e < 1/1000 := (min_le_left _ _).trans_lt (by norm_num)
  have hbudget : 8*e*1+ε/2 ≤ ε := by nlinarith only [min_le_right (1/2000:ℝ) (ε/32),hε]
  obtain ⟨C,hC,hslots⟩ := actual_low_response (Slot:=Slot) M H hH (3/4) (by norm_num) (by norm_num)
    W 1 2 (by norm_num) hWs hW 1 3 (1/2) ε e (ε/2) 1 (33/50) (33/50) bΦ 2 0 (1/2) 3
    (by norm_num) (by norm_num) (by norm_num) hε he hsmall (by positivity) (by norm_num)
    hbudget hφ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩; intro η₀
  filter_upwards [hslots η₀,eventually_ge_atTop (5:ℝ)] with U hU h5
  refine ⟨hU.1,?_⟩; intro s hs hQM hQη θ w σ v t height hw hw' hσ hv ht z hz hΦ
  have hp := Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) (1/2:ℝ)
  have hu := Real.rpow_le_rpow_of_exponent_le hU.1.le (by norm_num : (1/2:ℝ) ≤ 1)
  rw [Real.rpow_one] at hu
  have hfreq (j : Slot) : |t+v j|+U^(1/2:ℝ)/2 ≤ (3*0+2 : ℕ)*U^(1/2:ℝ) := by
    push_cast; linarith only [abs_add_le t (v j),hv j,ht,hp]
  have hheavy : (3+(3*0+2 : ℕ)*U^(1/2:ℝ))^2 ≤ (U^(3:ℝ))^(1:ℝ) := by
    norm_num
    have hroot : (U^(1/2:ℝ))^2 = U := by rw [← Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hU.1.le)]; norm_num
    nlinarith only [hroot, h5, hp, hu, mul_nonneg (show 0 ≤ U-5 by linarith) (show 0 ≤ U^2+5*U+25 by positivity)]
  have hl := (hU.2 s hs hQM hQη (7/8) 0 (by norm_num) (by norm_num) θ w σ v t hw
    (fun j => by linarith only [hw' j]) (fun j => (hσ j).ge) (fun j => (hσ j).le) hfreq hheavy z hz
    (global_low_gate hβ M H hH s η₀ hQM hQη he _ z hΦ)).1
  simpa only [show 2*ε*3=buf by dsimp [ε]; ring] using hl

#print axioms all_regular_low
end
end QRH.Cycle092.GlobalResponse
