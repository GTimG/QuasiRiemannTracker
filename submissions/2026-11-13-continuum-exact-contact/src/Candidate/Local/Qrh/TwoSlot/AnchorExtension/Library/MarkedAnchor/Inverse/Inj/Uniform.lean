/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/{Descent/Canonical,
Inversion/InitialClippedColumns, Inversion/InitialEnergyCallerClipping, Descent/ClippedFourier,
Descent/ClippedEnergy, Descent/ClippedUniform, Inversion/InitialEnergyCallerUniform}.lean`
(Apache-2.0). Modified by Sil (2026-11-12): the mark `primeMark` is replaced by the injective mark
`primeMarkInj` (`finiteCanonicalMarkedRowInj`, `normalizedColumnEnergyInj`). Every row identity
used is linear in the mark and is proved column by column exactly as in the baseline (the
pointwise Fourier facts `clipped_test_fourier`, `fourier_phase_integrable`, `child_test_clipping`
are reused from the baseline). Proofs otherwise unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Inj.Oracle
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUniform

/-!
# Inverse.Inj.Uniform — `initial_raw_uniform` for the injective column energy

* `rowInj_actual_columns`, `rowInj_clipping(_norm)`, `rowInj_zero_of_freshColumns_empty`,
  `rowInj_clipped_mode_integrable`, `rowInj_clipped_fourier`: the row identities;
* `normalized_energy_clipping_inj`, `normalized_energy_vector_inj`;
* `canonical_clipped_energy_inj`, `canonical_clipped_uniform_inj`, **`initial_raw_uniform_inj`**.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory
open OAI OAI.SevenEighths OAI.SevenEighths.InverseMoment
open FourierBridge JointLogSeparation SecondPassIntegration
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseInitialClippedColumns InverseInitialOverlapFourier InverseInitialProfile
open Qrh.MarkedAnchor.Inverse
local notation "Eis" => ActualEisensteinCubic.O

section Rows
variable {ι σ : Type} [DecidableEq ι]
variable (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
variable (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem rowInj_actual_columns
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k)
          (Ideal.span {∏ i ∈ U, p i}) *
        (primeMarkInj slots lists a U * W (primeProductNorm p U / X)) := by
  unfold finiteCanonicalMarkedRowInj fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  have he := CanonicalRowCompletion.columnWeight_finset p hp hcop hg hpr U Ψ m f k
    (fun U => primeMarkInj slots lists a U * W (primeProductNorm p U / X))
  symm
  convert he using 1 ; simp only [secondChildColumn, canonicalSourceCoefficient] ; ring

theorem rowInj_zero_of_freshColumns_empty
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ) (he : freshColumns p pool w X = ∅) :
    finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X = 0 := by
  unfold finiteCanonicalMarkedRowInj fixedChildRow
  apply Finset.sum_eq_zero
  intro U hU
  have hw : w (primeProductNorm p U/X) = 0 := by
    by_contra hw
    have hu : U ∈ freshColumns p pool w X := Finset.mem_filter.mpr ⟨hU,hw⟩
    rw [he] at hu
    exact Finset.notMem_empty U hu
  simp only [secondChildColumn,childLogTest,hw,zero_mul,mul_zero]

theorem rowInj_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N) =
      logPhase h (Real.log (Z^(max 0 N-N))) *
        finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a
          (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold finiteCanonicalMarkedRowInj fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  rw [child_test_clipping w hZ (primeProductNorm_pos p hp U) N h]
  ring

theorem rowInj_clipping_norm
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    ‖finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N)‖ =
    ‖finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N))‖ := by
  rw [rowInj_clipping p hp hcop hg pool Ψ m f k slots lists a w hZ N h,
    norm_mul,logPhase_norm,one_mul]

theorem normalized_energy_clipping_inj
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (d : Ideal Eis → ℝ) (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h F : ℝ) :
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows d
      (childLogTest w h) (Z^N) Z F =
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows d
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z F := by
  unfold normalizedColumnEnergyInj
  simp_rw [norm_mul, rowInj_clipping_norm p hp hcop hg pool Ψ m _ _
    slots lists a w hZ N h]

theorem normalized_energy_vector_inj
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (hD : ∀ f ∈ labels, 0 ≤ D f) (W : ℝ → ℂ) (X Z F : ℝ) :
    (∑ v : labels × rows, ‖(Real.sqrt (D v.1) : ℂ) * ((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2
        slots lists a W X‖^2) =
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F := by
  unfold normalizedColumnEnergyInj
  rw [Fintype.sum_prod_type,←Finset.sum_coe_sort labels]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←Finset.sum_coe_sort rows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_assoc,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hD f f.property)]

theorem rowInj_clipped_mode_integrable
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (g : 𝓢(ℝ,ℂ)) (wFresh : ℝ → ℂ) (c θ X : ℝ) :
    Integrable (fun t : ℝ => density g (Real.log c) t *
      finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a
        (childLogTest wFresh (θ+t)) X) := by
  simp_rw [rowInj_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro U hU
  convert fourier_phase_integrable g (Real.log c+Real.log (primeProductNorm p U/X))
    (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
      primeMarkInj slots lists a U*wFresh (primeProductNorm p U/X)*
        logPhase θ (Real.log (primeProductNorm p U/X))) using 1
  funext t
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem rowInj_clipped_fourier
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (wFresh : ℝ → ℂ) (c θ X : ℝ) (hc : 0 < c) (hX : 0 < X)
    (hwFresh : ∀ y, 0 < y → wFresh y * W (c*y) = W (c*y)) :
    finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a (clippedTest W c θ) X =
      ∫ t : ℝ, density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a
          (childLogTest wFresh (θ+t)) X := by
  simp_rw [rowInj_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  have hints (U : Finset ι) : Integrable (fun t : ℝ =>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t*
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        (primeMarkInj slots lists a U*childLogTest wFresh (θ+t) (primeProductNorm p U/X)))) := by
    convert fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log (primeProductNorm p U/X))
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        primeMarkInj slots lists a U*wFresh (primeProductNorm p U/X)*
          logPhase θ (Real.log (primeProductNorm p U/X))) using 1
    funext t
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun U _ => hints U)]
  apply Finset.sum_congr rfl
  intro U hU
  rw [clipped_test_fourier W lo hi hlo hs hW wFresh c θ _ hc
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX)
    (hwFresh _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX))]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem canonical_clipped_energy_inj
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (hD : ∀ f ∈ labels, 0 ≤ D f)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hs : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W)
    (wFresh : ℝ → ℂ) (c θ X Z F E : ℝ) (J : ℕ) (hc : 0 < c) (hX : 0 < X) (hE : 0 ≤ E)
    (hw : ∀ y, 0 < y → wFresh y * W (c*y) = W (c*y))
    (he : ∀ s, normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest wFresh s) X Z F ≤ E*(1+‖s‖)^(2*J)) :
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest W c θ) X Z F ≤
      E*(1+‖θ‖)^(2*J)*(∫ t : ℝ, (1+‖t‖)^J*
        ‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2 := by
  let g := CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let b := density g (Real.log c)
  let phi : labels × rows → ℝ → ℂ := fun v t => (Real.sqrt (D v.1) : ℂ)*((Z^(-F/2) : ℝ) : ℂ)*
    finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
      (childLogTest wFresh (θ+t)) X
  have hint (v : labels × rows) : Integrable (fun t : ℝ => b t * phi v t) := by
    convert (rowInj_clipped_mode_integrable p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a g wFresh c θ X).const_mul ((Real.sqrt (D v.1) : ℂ)*((Z^(-F/2) : ℝ) : ℂ))
      using 1
    funext t
    dsimp [b,phi]
    ring
  have hbound (t : ℝ) : (∑ v : labels × rows, ‖phi v t‖^2) ≤
      (E*(1+‖θ‖)^(2*J))*((1+‖t‖)^J)^2 := by
    dsimp only [phi]
    rw [normalized_energy_vector_inj p hp hcop hg pool Ψ m slots lists a labels rows D hD]
    apply (he (θ+t)).trans
    have hb : 1+‖θ+t‖ ≤ (1+‖θ‖)*(1+‖t‖) := by
      have hh := norm_add_le θ t
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg t)]
    calc
      _ ≤ E*((1+‖θ‖)*(1+‖t‖))^(2*J) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hE
      _ = _ := by rw [mul_pow,pow_mul];ring
  have hden : Integrable (fun t : ℝ => (1+‖t‖)^J*‖b t‖) := by
    simpa only [b,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh := CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy b phi
    (fun t : ℝ => (1+‖t‖)^J) (by intro t;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq (v : labels × rows) : (∫ t : ℝ, b t * phi v t) =
      (Real.sqrt (D v.1) : ℂ)*((Z^(-F/2) : ℝ) : ℂ)*
      finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
        (clippedTest W c θ) X := by
    rw [rowInj_clipped_fourier p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a W lo hi hlo hs hW wFresh c θ X hc hX hw,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [b,phi,g]
    ring
  simp_rw [heq] at hh
  rw [normalized_energy_vector_inj p hp hcop hg pool Ψ m slots lists a labels rows D hD] at hh
  simpa only [b,density_norm,g] using hh

end Rows

theorem canonical_clipped_uniform_inj
    (W : ℝ → ℂ) (lo hi b : ℝ) (hlo : 0 < lo) (hb : 1 ≤ b)
    (hs : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (wFresh : 𝓢(ℝ,ℂ)) (af bf : ℝ), 0 < af ∧ af ≤ bf ∧ HasCompactSupport (wFresh : ℝ → ℂ) ∧
      tsupport (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf ∧
      ∀ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
      (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ) (lists : σ → Finset ι)
      (a : σ → ι → ℂ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
      (_hD : ∀ f ∈ labels, 0 ≤ D f)
      (c θ X Z F E : ℝ), 1 ≤ c → c ≤ b → 0 < X → 0 ≤ E →
      (∀ s, normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) X Z F ≤ E*(1+‖s‖)^(2*J)) →
      normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W c θ) X Z F ≤ C*E*(1+‖θ‖)^(2*J) := by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,hagree⟩ := clipped_fixed_window W lo hi b hlo hb hs
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  let M := (∫ t : ℝ, (1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2
  refine ⟨M+1,by dsimp [M];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD c θ X Z F E hc1 hcb
    hX hE he
  have hh := canonical_clipped_energy_inj p hp hcop hg hpr pool Ψ m slots lists a labels rows D
    hD W lo hi hlo hs hW wFresh c θ X Z F E J (zero_lt_one.trans_le hc1) hX hE
    (hagree c hc1 hcb) he
  apply hh.trans
  change E*(1+‖θ‖)^(2*J)*M ≤ (M+1)*E*(1+‖θ‖)^(2*J)
  have hn : 0 ≤ E*(1+‖θ‖)^(2*J) := by positivity
  nlinarith

/-- **`initial_raw_uniform` for the injective column energy.** -/
theorem initial_raw_uniform_inj
    (W : ℝ → ℂ) (lo b : ℝ) (hlo : 0 < lo) (hb : 1 ≤ b)
    (hs : Function.support W ⊆ Set.Icc lo b) (hW : ContDiff ℝ ∞ W) :
    ∃ (wFresh : 𝓢(ℝ,ℂ)) (af bf : ℝ), 0 < af ∧ af ≤ bf ∧ HasCompactSupport (wFresh : ℝ → ℂ) ∧
      tsupport (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf ∧
      ∀ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
      (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ) (lists : σ → Finset ι)
      (a : σ → ι → ℂ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
      (_hD : ∀ f ∈ labels, 0 ≤ D f)
      (Z N F E : ℝ) (z : JointLogSeparation.Frequency × (Fin 6 → ℝ)) (h : ℝ), 1 < Z → 0 ≤ E →
      (h = -leftHeight z ∨ h = rightHeight z) →
      (∀ s, normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 N)) Z F ≤ E*(1+‖s‖)^(2*J)) →
      normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest W h) (Z^N) Z F ≤
        C*E*(tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,huniform⟩ :=
    canonical_clipped_uniform_inj W lo b b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩ := huniform J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh
    hm
  by_cases hne : (freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc1,hcb⟩ := freshColumns_clipping_range p hp pool W lo b Z N hZ hb hs hne
    rw [normalized_energy_clipping_inj p hp hcop hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc1 hcb (by positivity) hE hm).trans
    exact mul_le_mul_of_nonneg_left
      (InverseInitialEnergyCallerUniform.initial_height_bound J z h hh) (mul_nonneg hC.le hE)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold normalizedColumnEnergyInj
    simp_rw [rowInj_zero_of_freshColumns_empty p hp hcop hg pool Ψ m _ _
      slots lists a W (Z^N) h he,mul_zero,norm_zero,zero_pow (by omega : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [tripleHeight,coordinateHeight]
    positivity

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.initial_raw_uniform_inj
