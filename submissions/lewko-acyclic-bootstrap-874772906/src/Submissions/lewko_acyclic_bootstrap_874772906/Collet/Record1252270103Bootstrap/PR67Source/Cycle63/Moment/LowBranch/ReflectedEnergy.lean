import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.FixedDeletion
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.ReflectionGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FirstBranches.Reflection
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FirstBranches.Direct
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FirstBranches.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The energy of a child state with a nonunit puncture, after reflecting one of its plain factors, is at most `Z^(width + ε)`
up to the constants of the reflection. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentEnergyReferenceScalarReserve CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentEnergyReferenceDivisors
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentSectorLocalization CenteredMomentNaturalRowSource
open CenteredMomentRetainedEnergy CenteredMomentEnergyPaidBands
open Cycle63FirstReflection Cycle63FirstDirect Cycle63FirstGeometry

universe u
variable {α : Type u} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The clipped length of a positive scale is the nonnegative part of its logarithm. -/
theorem length_eq_max_logb {Z X : ℝ} (hZ : 1 < Z) (hX : 0 < X) :
    length Z X = max 0 (Real.logb Z X) := by
  unfold length
  rcases le_total 1 X with h | h
  · rw [max_eq_right h, max_eq_right (Real.logb_nonneg hZ h)]
  · rw [max_eq_left h, Real.logb_one, max_eq_left (Real.logb_nonpos hZ hX.le h)]

/-- The clipped length of a scale divided by a norm. -/
theorem length_div_norm {Z X N : ℝ} (hZ : 1 < Z) (hX : 0 < X) (hN : 0 < N) :
    length Z (X / N) = max 0 (Real.logb Z X - Real.logb Z N) := by
  rw [← divided_scale_power Z X N hZ hX hN]
  exact length_rpow Z _ hZ

/-- The ledger terms of the reflected, direct and error bounds are dominated by the ledger sum. -/
theorem reflection_ledger_domination {Rr c₁ c₂ ℓ P₁ P₂ P₃ q₀ q₁ m Zq pr Cs R₀ : ℝ}
    (hRr : 0 ≤ Rr) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hℓ : 0 ≤ ℓ) (hP₃ : 1 ≤ P₃)
    (hP₂ : P₂ ≤ P₃ * P₁) (hq : q₀ ≤ q₁) (hq₀ : 0 ≤ q₀) (hm : 0 ≤ m) (hZq : 1 ≤ Zq) (hpr : 0 ≤ pr)
    (hledger : Rr * (P₁ + c₁ * ℓ * P₁ + c₂ * q₁ * m * Zq * pr) ≤ Cs * R₀) :
    Rr * (P₂ + c₁ * ℓ * P₂ + c₂ * q₀ * m * pr) ≤ P₃ * (Cs * R₀) := by
  have h1 : c₁ * ℓ * P₂ ≤ c₁ * ℓ * (P₃ * P₁) := mul_le_mul_of_nonneg_left hP₂ (by positivity)
  have h2 : c₂ * q₀ * m * pr ≤ c₂ * q₁ * m * Zq * pr * P₃ := by
    have h3 : c₂ * q₀ * m * pr ≤ c₂ * q₁ * m * pr :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hc₂) hm) hpr
    have h4 : 1 ≤ Zq * P₃ := by nlinarith
    have h5 : 0 ≤ c₂ * q₁ * m * pr := by
      have : 0 ≤ q₁ := hq₀.trans hq
      positivity
    calc c₂ * q₀ * m * pr ≤ c₂ * q₁ * m * pr := h3
      _ = (c₂ * q₁ * m * pr) * 1 := by ring
      _ ≤ (c₂ * q₁ * m * pr) * (Zq * P₃) := mul_le_mul_of_nonneg_left h4 h5
      _ = c₂ * q₁ * m * Zq * pr * P₃ := by ring
  have hT : P₂ + c₁ * ℓ * P₂ + c₂ * q₀ * m * pr ≤
      P₃ * (P₁ + c₁ * ℓ * P₁ + c₂ * q₁ * m * Zq * pr) := by nlinarith [hP₂, h1, h2]
  calc Rr * (P₂ + c₁ * ℓ * P₂ + c₂ * q₀ * m * pr)
      ≤ Rr * (P₃ * (P₁ + c₁ * ℓ * P₁ + c₂ * q₁ * m * Zq * pr)) := mul_le_mul_of_nonneg_left hT hRr
    _ = P₃ * (Rr * (P₁ + c₁ * ℓ * P₁ + c₂ * q₁ * m * Zq * pr)) := by ring
    _ ≤ P₃ * (Cs * R₀) := mul_le_mul_of_nonneg_left hledger (by linarith)

/-- The masked energy of a child state whose second plain factor can be reflected is at most the old bound up to
`Z^ε₀` and the constants of the reflection, which are chosen before the base `Z`. -/
theorem reflected_masked_energy_core
    (Wslot : ℝ → ℂ) (aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ δ ξ ε₀ : ℝ) (degree : ℕ)
    (S : Finset (ℕ × ℕ))
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot) (hWc : Continuous Wslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b) (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 ≤ Mcap)
    (hε : 0 ≤ ε) (hκ : 1/6 ≤ κ) (hδ : 0 ≤ δ) (hξ : 0 < ξ) (hε₀ : 0 < ε₀) :
    ∃ (Cr : ℝ) (Jexp : ℕ) (U : Finset (ℕ × ℕ)), 0 < Cr ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η₀ : Character) (Q : Ideal O) (K : ℝ), 0 ≤ K →
      PositiveAt (α := α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S K →
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap → s.width ≤ L →
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      length Z X₁ + length Z X₂ + 6 * κ * (∑ i ∈ J, w i) ≤ s.width + δ →
      max 0 (s.width - length Z X₂ + ξ) + length Z X₁ + 6 * κ * (∑ i ∈ J, w i) + δ ≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i : J => primePool M H bslot (Z ^ (w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
        (fun i : J => Z ^ (w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      Cr * (K + 1) * diagonalControl s.radial.profile * (sourceControl U W₁ * sourceControl U W₂) ^ 2 *
        (1 + |t| + height) ^ Jexp * Z ^ (s.width + ε + ε₀) := by
  have hMb : 0 < Bmask + Mcap + 2 := by linarith
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = ε₀ / (4 * (Bmask + Mcap + 2)) := ⟨_, rfl⟩
  have hd : 0 < d := by rw [hd_def]; positivity
  obtain ⟨saving₁, hs1⟩ : ∃ r : ℝ, r = 2 * Mcap + Bmask * d + 2 * Mcap * d + 1 := ⟨_, rfl⟩
  have hmain : d * (Bmask + Mcap + 2) ≤ ε₀ := by
    have : d * (Bmask + Mcap + 2) = ε₀ / 4 := by rw [hd_def]; field_simp
    linarith
  have herror : Bmask * d + Mcap * (2 * d) - 2 * saving₁ + 5 * Mcap / 4 ≤ ε₀ := by
    rw [hs1]; linarith [mul_nonneg hBmask hd.le, mul_nonneg hMcap hd.le]
  obtain ⟨Cs, hCs, hscalar⟩ := ledger_bound.{u} Mcap Bmask bΦ Mcap d saving₁ ε₀ hMcap hBmask hMcap hd hmain herror
  obtain ⟨n, T, Dchild, hDc, nlong, Slong, Cref, Dref, hCr, hDr, href⟩ :=
    reference_from_positive_with_error (α := α) M H hH Finset.univ Wslot aslot bslot lo hi haslot hWs hWc
      a b bΦ d ξ (saving₁ + Mcap / 2) Mcap ha hlo hhi hbΦ hd hξ 2 le_rfl degree S
  obtain ⟨Jenv, U, Cprof, hCp, henv⟩ :=
    reference_envelopes a b ha S T Slong degree n nlong Cref Dchild Dref hCr hDc hDr
  obtain ⟨Bslot, hBslot, hslot⟩ :=
    CenteredMomentRayMaskedFloor.slot_coefficient_bounds Wslot aslot bslot lo hi haslot hWs hWc
  have hweight_ex (T' : Finset α) := original_energy_weighted_deletion (α := ↥T')
    (fun _ => bslot) (fun _ => Bslot) (fun _ => hBslot.le) d hd
  choose Cw hCw hweight using hweight_ex
  obtain ⟨Cweight, hCweight_def⟩ : ∃ c : ℝ, c = 1 + ∑ T' : Finset α, Cw T' := ⟨_, rfl⟩
  have hCweight : 0 < Cweight := by
    have : 0 ≤ ∑ T' : Finset α, Cw T' := Finset.sum_nonneg (fun T' _ => (hCw T').le)
    rw [hCweight_def]; linarith
  have hCwle : ∀ T' : Finset α, Cw T' ≤ Cweight := by
    intro T'
    have := Finset.single_le_sum (f := Cw) (fun T'' _ => (hCw T'').le) (Finset.mem_univ T')
    rw [hCweight_def]; linarith
  refine ⟨Cweight * Cs * Cprof, Jenv, U, mul_pos (mul_pos hCweight hCs) hCp, ?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η₀ Q K hK hpos J θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL W₁ W₂ hs₁ hs₂
    X₁ X₂ hX₁ hX₂ hc₁ hc₂ hover hrefl
  have hZ0 : 0 < Z := zero_lt_one.trans hZ.1
  have hlog : 0 ≤ Real.log Z := (Real.log_pos hZ.1).le
  have hsumJ : 0 ≤ ∑ i ∈ J, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hW0 : 0 ≤ s.width := s.width_nonneg
  have hL₁ : 0 ≤ length Z X₁ := length_nonneg Z X₁ hZ.1
  have hL₂ : 0 ≤ length Z X₂ := length_nonneg Z X₂ hZ.1
  have hsumW : ∑ i ∈ J, w i ≤ s.width := by
    have h1 : 0 ≤ max 0 (s.width - length Z X₂ + ξ) := le_max_left _ _
    linarith [mul_nonneg (show (0:ℝ) ≤ 6 * κ - 1 by linarith) hsumJ]
  have hsumM : ∑ i ∈ J, w i ≤ Mcap := hsumW.trans hs
  have hl₂ : ξ ≤ length Z X₂ := by
    have h1 := le_max_right 0 (s.width - length Z X₂ + ξ)
    have h2 : 0 ≤ 6 * κ * ∑ i ∈ J, w i := by positivity
    linarith
  have hx₂eq : length Z X₂ = Real.logb Z X₂ := by
    rcases le_or_gt (Real.logb Z X₂) 0 with h | h
    · rw [length_eq_max_logb hZ.1 hX₂, max_eq_left h] at hl₂
      exact (not_le.mpr hξ hl₂).elim
    · rw [length_eq_max_logb hZ.1 hX₂, max_eq_right h.le]
  have hpoolprime : ∀ (i : ↥J), ∀ I ∈ primePool M H bslot (Z ^ (w i)), Prime I :=
    fun i I hI => (Finset.mem_filter.mp hI).2.1
  have hPpos : ∀ (i : ↥J), 0 < Z ^ (w i) := fun i => Real.rpow_pos_of_pos hZ0 _
  have hβ : ∀ (i : ↥J), ∀ I ∈ primePool M H bslot (Z ^ (w i)),
      ‖idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I‖ ≤ Bslot := by
    intro i I hI
    have hh := (hslot (relativeCharacter M H hH η₀ (θ i)) (Z ^ (w i)) (σ i) (v i) 0 (hPpos i)
      (hσlo i) (hσhi i) I (hpoolprime i I hI).ne_zero).1
    simpa only [heightCoefficient, Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one] using hh
  have hbs : ∀ (i : ↥J), ∀ I ∈ primePool M H bslot (Z ^ (w i)),
      idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I ≠ 0 →
      (I.absNorm : ℝ) ≤ bslot * Z ^ (w i) := by
    intro i I hI hn
    have hh := (hslot (relativeCharacter M H hH η₀ (θ i)) (Z ^ (w i)) (σ i) (v i) 0 (hPpos i)
      (hσlo i) (hσhi i) I (hpoolprime i I hI).ne_zero).2
    apply hh
    simpa only [heightCoefficient, Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one] using hn
  have henv' := henv W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at henv'
  obtain ⟨henv_dir, henv_main, henv_err⟩ := henv'
  obtain ⟨Cond, hCond⟩ : ∃ c : ℝ, c = max 1 ((fixedConductorFactor : ℝ) * bΦ * Z ^ s.width) := ⟨_, rfl⟩
  have hCond1 : 1 ≤ Cond := by rw [hCond]; exact le_max_left _ _
  have hCondpos : 0 < Cond := by linarith
  obtain ⟨A, hA⟩ : ∃ r : ℝ, r = Cprof * (sourceControl U W₁ * sourceControl U W₂) ^ 2 *
      (1 + |t| + height) ^ Jenv := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hdiag : 0 ≤ diagonalControl s.radial.profile := diagonalControl_nonneg _
  obtain ⟨Ebase, hEbase⟩ : ∃ r : ℝ, r = (K + 1) * diagonalControl s.radial.profile * A := ⟨_, rfl⟩
  have hEbase0 : 0 ≤ Ebase := by rw [hEbase]; positivity
  obtain ⟨ℓ, hℓ⟩ : ∃ r : ℝ, r = 1 + 2 * (Mcap * Real.log Z) := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by
    have := mul_nonneg hMcap hlog
    rw [hℓ]; linarith
  obtain ⟨Tsum, hTsum⟩ : ∃ r : ℝ, r = Z ^ (s.width + ε) + Cond ^ d * ℓ * Z ^ (s.width + ε) +
      Cond ^ (2 * d) * (Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap) * max 1 s.radial.scale *
        ∏ i ∈ J, Z ^ (w i) := ⟨_, rfl⟩
  have hTsum0 : 0 ≤ Tsum := by rw [hTsum]; positivity
  have hP₂ : Z ^ (s.width + ε) ≤ Z ^ ε * Z ^ (s.width + d) := by
    rw [← Real.rpow_add hZ0]; exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)
  have hq : Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap ≤ Z ^ (-2 * saving₁) := by
    rw [← Real.rpow_add hZ0]; apply le_of_eq; congr 1; ring
  have hq₀ : 0 ≤ Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap := by positivity
  have hm : 0 ≤ max 1 s.radial.scale := le_trans zero_le_one (le_max_left _ _)
  have hZq : 1 ≤ Z ^ (s.width / 4) := Real.one_le_rpow hZ.1.le (by linarith)
  have hpr : 0 ≤ ∏ i ∈ J, Z ^ (w i) := by positivity
  have hZe : 0 ≤ Z ^ (s.width + ε) := Real.rpow_nonneg hZ0.le _
  have hKd : 0 ≤ K * diagonalControl s.radial.profile := mul_nonneg hK hdiag
  refine le_trans (hweight J Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i : ↥J => primePool M H bslot (Z ^ (w i)))
    (fun (i : ↥J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
    (fun i : ↥J => Z ^ (w i)) t X₁ X₂ (Ebase * Tsum) 0 hpoolprime hPpos hβ hbs hX₁ hX₂
    (mul_nonneg hEbase0 hTsum0) (by norm_num) ?_) ?_
  · intro D₁ hD₁ D₂ hD₂ J'' _
    obtain ⟨hN₁, hN₁Z⟩ := divisor_norm s D₁ hD₁
    obtain ⟨hN₂, hN₂Z⟩ := divisor_norm s D₂ hD₂
    have hN₁pos : 0 < ((∏ I ∈ D₁, I).absNorm : ℝ) := zero_lt_one.trans_le hN₁
    have hN₂pos : 0 < ((∏ I ∈ D₂, I).absNorm : ℝ) := zero_lt_one.trans_le hN₂
    have ha₁ : 0 ≤ Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ) := Real.logb_nonneg hZ.1 hN₁
    have ha₂ : 0 ≤ Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ) := Real.logb_nonneg hZ.1 hN₂
    obtain ⟨F, hF⟩ : ∃ F : Finset α, F = (Finset.univ \ J'').map (Function.Embedding.subtype (· ∈ J)) :=
      ⟨_, rfl⟩
    have hFJ : F ⊆ J := by
      intro i hi
      rw [hF] at hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.2
    have hzF : ∑ i ∈ F, w i ≤ ∑ i ∈ J, w i :=
      Finset.sum_le_sum_of_subset_of_nonneg hFJ (fun i _ _ => hw i)
    have hprod : ∀ z : O, (∏ i ∈ Finset.univ \ J'', naturalSlot (naturalCharacter s.character z)
          (primePool M H bslot (Z ^ (w i)))
          (heightCoefficient (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I) t) (Z ^ (w i))) =
        ∏ i ∈ F, naturalSlot (naturalCharacter s.character z)
          (primePool M H bslot (Z ^ (w i)))
          (heightCoefficient (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I) t) (Z ^ (w i)) := by
      intro z
      rw [hF, Finset.prod_map]
      rfl
    simp only [hprod]
    have hx₁ : length Z X₁ = max 0 (Real.logb Z X₁) := length_eq_max_logb hZ.1 hX₁
    have hx₂ : length Z X₂ = max 0 (Real.logb Z X₂) := length_eq_max_logb hZ.1 hX₂
    rw [hx₁, hx₂] at hover
    rw [hx₁, hx₂eq] at hrefl
    have hcases := deleted_reflection_cases (W := s.width) (ξ := ξ) (δ := δ) (κ := κ)
      (z := ∑ i ∈ J, w i) (zF := ∑ i ∈ F, w i) (x₁ := Real.logb Z X₁) (x₂ := Real.logb Z X₂)
      (a₁ := Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ)) (a₂ := Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ))
      hδ (by linarith) hsumJ hzF ha₁ ha₂ hover hrefl
    have e₁ : X₁ / ((∏ I ∈ D₁, I).absNorm : ℝ) =
        Z ^ (Real.logb Z X₁ - Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ)) :=
      (divided_scale_power Z X₁ _ hZ.1 hX₁ hN₁pos).symm
    have e₂ : X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ) =
        Z ^ (Real.logb Z X₂ - Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ)) :=
      (divided_scale_power Z X₂ _ hZ.1 hX₂ hN₂pos).symm
    rcases hcases with hdir | ⟨hδ₂, hξx, hcapR, hlenR, hlenS⟩
    · have hc₁' : X₁ / ((∏ I ∈ D₁, I).absNorm : ℝ) ≤ Z ^ L := (div_le_self hX₁.le hN₁).trans hc₁
      have hc₂' : X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ) ≤ Z ^ L := (div_le_self hX₂.le hN₂).trans hc₂
      have hcap' : length Z (X₁ / ((∏ I ∈ D₁, I).absNorm : ℝ)) +
          length Z (X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) + 6 * κ * (∑ i ∈ F, w i) ≤ s.width := by
        rw [length_div_norm hZ.1 hX₁ hN₁pos, length_div_norm hZ.1 hX₂ hN₂pos]
        exact hdir
      have hdirect := direct_child_from_positive M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
        η₀ Q degree S K hpos hBmask ha F θ w σ v t t height hw hwL hσlo hσhi hheight hv s hQ hs W₁ W₂
        hs₁ hs₂ (X₁ / ((∏ I ∈ D₁, I).absNorm : ℝ)) (X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))
        (div_pos hX₁ hN₁pos) (div_pos hX₂ hN₂pos) hc₁' hc₂' hcap'
      refine hdirect.trans ?_
      rw [Real.rpow_zero, mul_one]
      have hctl : ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S) ^ 2 * (1 + |t| + height) ^ degree ≤ A := by
        rw [hA]; exact henv_dir
      calc K * diagonalControl s.radial.profile * ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S) ^ 2 *
            (1 + |t| + height) ^ degree * Z ^ (s.width + ε)
          = (K * diagonalControl s.radial.profile) *
            (((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S) ^ 2 * (1 + |t| + height) ^ degree) *
            Z ^ (s.width + ε) := by ring
        _ ≤ (K * diagonalControl s.radial.profile) * A * Z ^ (s.width + ε) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hctl hKd) hZe
        _ ≤ Ebase * Z ^ (s.width + ε) := by
            rw [hEbase]; linarith [mul_nonneg (mul_nonneg hdiag hA0) hZe]
        _ ≤ Ebase * Tsum := by
            apply mul_le_mul_of_nonneg_left _ hEbase0
            rw [hTsum]
            have h1 : 0 ≤ Cond ^ d * ℓ * Z ^ (s.width + ε) := by positivity
            have h2 : 0 ≤ Cond ^ (2 * d) * (Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap) *
                max 1 s.radial.scale * ∏ i ∈ J, Z ^ (w i) := by positivity
            linarith
    · have hlength : s.width ≤ Mcap +
          (Real.logb Z X₂ - Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ)) := by linarith
      have hL' : max 0 (s.width - (Real.logb Z X₂ - Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ)) + ξ) ≤ L :=
        hlenR.trans hsL
      have hbshort : Real.logb Z X₁ - Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ) ≤ L :=
        (le_max_right 0 _).trans (hlenS.trans hsL)
      have hcapacity : max 0 (s.width - (Real.logb Z X₂ - Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ)) + ξ) +
          length Z (Z ^ (Real.logb Z X₁ - Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ))) +
          6 * κ * (∑ i ∈ F, w i) ≤ s.width := by
        rw [length_rpow Z _ hZ.1]; exact hcapR
      have hrefl_inst := hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hpos hBmask F (Finset.subset_univ F)
        θ w σ v t t height hw hwL hσlo hσhi hheight hv s hQ hs W₂ W₁ hs₂ hs₁
        (Real.logb Z X₂ - Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ))
        (Real.logb Z X₁ - Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ)) hlength hL' hbshort hcapacity
      dsimp only at hrefl_inst
      refine le_of_eq_of_le ?_ (hrefl_inst.trans ?_)
      · congr 1
        funext z
        rw [e₁, e₂]
        ring
      · rw [Real.rpow_zero, mul_one]
        have hZb : Z ^ (Real.logb Z X₁ - Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ)) ≤ Z ^ Mcap :=
          Real.rpow_le_rpow_of_exponent_le hZ.1.le
            (((le_max_right 0 _).trans hlenS).trans hs)
        have hprodF : ∏ i ∈ F, Z ^ (w i) ≤ ∏ i ∈ J, Z ^ (w i) :=
          Finset.prod_le_prod_of_subset_of_one_le₀ hFJ (fun i _ => (Real.rpow_pos_of_pos hZ0 _).le)
            (fun i _ _ => Real.one_le_rpow hZ.1.le (hw i))
        refine (add_le_add
          (b := Ebase * (Cond ^ d * ℓ * Z ^ (s.width + ε)))
          (d := Ebase * (Cond ^ (2 * d) * (Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap) *
            max 1 s.radial.scale * ∏ i ∈ J, Z ^ (w i))) ?_ ?_).trans ?_
        · calc _ = (Cref * Dchild * (sourceControl Slong W₂) ^ 2 * (sourceControl T W₁) ^ 2 *
                (1 + ‖t‖) ^ (2 * nlong) * (1 + |t| + height) ^ (degree + 2 * n)) *
                (K * diagonalControl s.radial.profile) *
                (Cond ^ d * (1 + 2 * (max 0 (s.width - (Real.logb Z X₂ -
                  Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ)) + ξ) * Real.log Z)) *
                  Z ^ (s.width + ε)) := by rw [hCond]; ring
            _ ≤ A * (K * diagonalControl s.radial.profile) * (Cond ^ d * ℓ * Z ^ (s.width + ε)) := by
                have hq1 : Cref * Dchild * (sourceControl Slong W₂) ^ 2 * (sourceControl T W₁) ^ 2 *
                    (1 + ‖t‖) ^ (2 * nlong) * (1 + |t| + height) ^ (degree + 2 * n) ≤ A := by
                  rw [hA]; exact henv_main
                have hℓle : 1 + 2 * (max 0 (s.width - (Real.logb Z X₂ -
                    Real.logb Z ((∏ I ∈ D₂, I).absNorm : ℝ)) + ξ) * Real.log Z) ≤ ℓ := by
                  have := mul_le_mul_of_nonneg_right (hlenR.trans hs) hlog
                  rw [hℓ]; linarith
                apply mul_le_mul (mul_le_mul_of_nonneg_right hq1 hKd) _ (by positivity) (by positivity)
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hℓle (by positivity)) hZe
            _ ≤ Ebase * (Cond ^ d * ℓ * Z ^ (s.width + ε)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                rw [hEbase]; linarith [mul_nonneg hdiag hA0]
        · calc _ = (Dref * (sourceControl Slong W₂) ^ 2 * ((schwartzSeminormFamily ℝ ℝ ℂ (0, 0)) W₁) ^ 2 *
                (1 + ‖t‖) ^ (2 * nlong)) * diagonalControl s.radial.profile *
                ((Cond ^ (2 * d) * Z ^ (-2 * (saving₁ + Mcap / 2)) * max 1 s.radial.scale) *
                  (Z ^ (Real.logb Z X₁ - Real.logb Z ((∏ I ∈ D₁, I).absNorm : ℝ)) *
                    ∏ i ∈ F, Z ^ (w i))) := by rw [hCond]; ring
            _ ≤ A * diagonalControl s.radial.profile *
                ((Cond ^ (2 * d) * Z ^ (-2 * (saving₁ + Mcap / 2)) * max 1 s.radial.scale) *
                  (Z ^ Mcap * ∏ i ∈ J, Z ^ (w i))) := by
                have hq2 : Dref * (sourceControl Slong W₂) ^ 2 * ((schwartzSeminormFamily ℝ ℝ ℂ (0, 0)) W₁) ^ 2 *
                    (1 + ‖t‖) ^ (2 * nlong) ≤ A := by
                  rw [hA]; exact henv_err
                apply mul_le_mul (mul_le_mul_of_nonneg_right hq2 hdiag) _ (by positivity) (by positivity)
                exact mul_le_mul_of_nonneg_left (mul_le_mul hZb hprodF (by positivity) (by positivity)) (by positivity)
            _ = A * diagonalControl s.radial.profile * (Cond ^ (2 * d) *
                (Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap) * max 1 s.radial.scale *
                  ∏ i ∈ J, Z ^ (w i)) := by ring
            _ ≤ Ebase * (Cond ^ (2 * d) * (Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap) *
                max 1 s.radial.scale * ∏ i ∈ J, Z ^ (w i)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                rw [hEbase]; linarith [mul_nonneg hK (mul_nonneg hdiag hA0)]
        · rw [← mul_add]
          apply mul_le_mul_of_nonneg_left _ hEbase0
          rw [hTsum]
          linarith
  · have hledger := hscalar Z hZ.1.le s hs ↥J (fun i : ↥J => w i)
      (by simpa only [Finset.sum_coe_sort] using hsumM)
    have hprodJ : (∏ i : ↥J, Z ^ (w i)) = ∏ i ∈ J, Z ^ (w i) :=
      Finset.prod_coe_sort J (fun i => Z ^ (w i))
    simp only [hprodJ] at hledger
    rw [← hCond, ← hℓ] at hledger
    have hdom := reflection_ledger_domination
      (Rr := (s.puncture.radical.absNorm : ℝ) ^ d) (c₁ := Cond ^ d) (c₂ := Cond ^ (2 * d)) (ℓ := ℓ)
      (P₁ := Z ^ (s.width + d)) (P₂ := Z ^ (s.width + ε)) (P₃ := Z ^ ε)
      (q₀ := Z ^ (-2 * (saving₁ + Mcap / 2)) * Z ^ Mcap) (q₁ := Z ^ (-2 * saving₁))
      (m := max 1 s.radial.scale) (Zq := Z ^ (s.width / 4)) (pr := ∏ i ∈ J, Z ^ (w i))
      (Cs := Cs) (R₀ := Z ^ (s.width + ε₀))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hCondpos.le _)
      (Real.rpow_nonneg hCondpos.le _) hℓ0 (Real.one_le_rpow hZ.1.le hε) hP₂ hq hq₀ hm hZq hpr hledger
    rw [← hTsum] at hdom
    calc Cw J * (s.puncture.radical.absNorm : ℝ) ^ d * (Ebase * Tsum)
        = Cw J * Ebase * ((s.puncture.radical.absNorm : ℝ) ^ d * Tsum) := by ring
      _ ≤ Cw J * Ebase * (Z ^ ε * (Cs * Z ^ (s.width + ε₀))) :=
          mul_le_mul_of_nonneg_left hdom (mul_nonneg (hCw J).le hEbase0)
      _ ≤ Cweight * Ebase * (Z ^ ε * (Cs * Z ^ (s.width + ε₀))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCwle J) hEbase0)
            (mul_nonneg (Real.rpow_nonneg hZ0.le _) (mul_nonneg hCs.le (Real.rpow_nonneg hZ0.le _)))
      _ = Cweight * Cs * Cprof * (K + 1) * diagonalControl s.radial.profile *
            (sourceControl U W₁ * sourceControl U W₂) ^ 2 * (1 + |t| + height) ^ Jenv *
            Z ^ (s.width + ε + ε₀) := by
          have hZpow : Z ^ (s.width + ε + ε₀) = Z ^ ε * Z ^ (s.width + ε₀) := by
            rw [← Real.rpow_add hZ0]; congr 1; ring
          rw [hEbase, hA, hZpow]
          ring

/-- The energy is symmetric in its two plain factors. -/
theorem energy_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K = energy η m A t W₂ W₁ S β P X₂ X₁ keep Φ K := by
  unfold energy
  refine tsum_congr (fun z => ?_)
  have h : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ = positiveSlotRow η m A z W₂ W₁ S β P t X₂ X₁ := by
    unfold positiveSlotRow
    rw [mul_comm X₁ X₂]
    ring
  rw [h]

/-- A bound with larger coefficient, profile control, height exponent and base exponent. -/
theorem bound_upgrade {c c' d x x' h h' z z' : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c) (hcc : c ≤ c') (hx : 0 ≤ x)
    (hxx : x ≤ x') (hh : 0 ≤ h) (hhh : h ≤ h') (hz : 0 ≤ z) (hzz : z ≤ z') :
    c * d * x ^ 2 * h * z ≤ c' * d * x' ^ 2 * h' * z' := by
  have hc' : 0 ≤ c' := hc.trans hcc
  have hx' : 0 ≤ x' := hx.trans hxx
  have hh' : 0 ≤ h' := hh.trans hhh
  have hz' : 0 ≤ z' := hz.trans hzz
  have h1 : c * d ≤ c' * d := mul_le_mul_of_nonneg_right hcc hd
  have h2 : c * d * x ^ 2 ≤ c' * d * x' ^ 2 :=
    mul_le_mul h1 (pow_le_pow_left₀ hx hxx 2) (sq_nonneg x) (mul_nonneg hc' hd)
  have h3 : c * d * x ^ 2 * h ≤ c' * d * x' ^ 2 * h' :=
    mul_le_mul h2 hhh hh (mul_nonneg (mul_nonneg hc' hd) (sq_nonneg x'))
  exact mul_le_mul h3 hzz hz (mul_nonneg (mul_nonneg (mul_nonneg hc' hd) (sq_nonneg x')) hh')

/-- The energy of the state with the slots `R` deleted from `J` is bounded by the old moment when no slot remains, and
otherwise by the reflection of one plain factor, if the state exceeds the old capacity by at most `δ` and its reflected
state has margin `δ`. -/
theorem reflected_remaining_energy_bound
    (Wslot : ℝ → ℂ) (aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ δ ξ ε₀ : ℝ) (degree : ℕ)
    (S : Finset (ℕ × ℕ))
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot) (hWc : Continuous Wslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b) (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 ≤ Mcap)
    (hε : 0 ≤ ε) (hκ : 1/6 ≤ κ) (hδ : 0 ≤ δ) (hξ : 0 < ξ) (hε₀ : 0 < ε₀) :
    ∃ (Cr : ℝ) (Jexp : ℕ) (U : Finset (ℕ × ℕ)), 0 < Cr ∧ S ⊆ U ∧ degree ≤ Jexp ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η₀ : Character) (Q : Ideal O) (C₀ C₁ : ℝ), 0 ≤ C₀ → 0 ≤ C₁ →
      ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀ →
      PositiveAt (α := α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C₁ →
      ∀ (J R : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap → s.width ≤ L →
      ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      (R = J ∨
        (length Z X₁ + length Z X₂ + 6 * κ * (∑ i ∈ J \ R, w i) ≤ s.width + δ ∧
          (max 0 (s.width - length Z X₂ + ξ) + length Z X₁ + 6 * κ * (∑ i ∈ J \ R, w i) + δ ≤ s.width ∨
            max 0 (s.width - length Z X₁ + ξ) + length Z X₂ + 6 * κ * (∑ i ∈ J \ R, w i) + δ ≤ s.width))) →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : ↥(J \ R) => primePool M H bslot (Z ^ (w i)))
        (fun (i : ↥(J \ R)) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
        (fun i : ↥(J \ R) => Z ^ (w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (C₀ + Cr * (C₁ + 1)) * diagonalControl s.radial.profile * (p.control U) ^ 2 *
        (1 + |t| + height) ^ Jexp * Z ^ (s.width + ε + ε₀) := by
  obtain ⟨Cc, Jc, Uc, hCc, hcore⟩ := reflected_masked_energy_core (α := α) M H hH Wslot aslot bslot a b bΦ
    Bmask L Lslot lo hi Mcap ε κ δ ξ ε₀ degree S haslot hWs hWc ha hlo hhi hbΦ hBmask hMcap hε hκ hδ hξ hε₀
  refine ⟨Cc + 1, max Jc degree, Uc ∪ S, by linarith, Finset.subset_union_right, le_max_right _ _, ?_⟩
  filter_upwards [hcore] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η₀ Q C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hreflect
  have hZ0 : 0 < Z := zero_lt_one.trans hZ.1
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hbase : 1 ≤ 1 + |t| + height := by linarith [abs_nonneg t]
  have hexp : Z ^ (s.width + ε) ≤ Z ^ (s.width + ε + ε₀) :=
    Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)
  have hctlS : p.control S ≤ p.control (Uc ∪ S) :=
    mul_le_mul (control_mono Finset.subset_union_right (p.profile 0))
      (control_mono Finset.subset_union_right (p.profile 1)) (sourceControl_nonneg _ _)
      (sourceControl_nonneg _ _)
  have hctlU : p.control Uc ≤ p.control (Uc ∪ S) :=
    mul_le_mul (control_mono Finset.subset_union_left (p.profile 0))
      (control_mono Finset.subset_union_left (p.profile 1)) (sourceControl_nonneg _ _)
      (sourceControl_nonneg _ _)
  have hpowS : (1 + |t| + height) ^ degree ≤ (1 + |t| + height) ^ (max Jc degree) :=
    pow_le_pow_right₀ hbase (le_max_right _ _)
  have hpowU : (1 + |t| + height) ^ Jc ≤ (1 + |t| + height) ^ (max Jc degree) :=
    pow_le_pow_right₀ hbase (le_max_left _ _)
  have hZ1 : 0 ≤ Z ^ (s.width + ε) := Real.rpow_nonneg hZ0.le _
  have hpow0 : 0 ≤ (1 + |t| + height) ^ (max Jc degree) := by positivity
  rcases hreflect with hRJ | ⟨hover, hrefl | hrefl⟩
  · have hb := remaining_energy_bound M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S
      C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
      hX₁ hX₂ hc₁ hc₂ (Or.inl hRJ)
    refine hb.trans ?_
    exact bound_upgrade hdiag (by positivity) (by nlinarith [mul_nonneg hCc.le hC₁]) (p.control_nonneg S)
      hctlS (by positivity) hpowS hZ1 hexp
  · have hb := hZ.2 η₀ Q C₁ hC₁ hpos (J \ R) θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL
      (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂ hc₁ hc₂ hover hrefl
    refine hb.trans ?_
    have hshape : Cc * (C₁ + 1) * diagonalControl s.radial.profile *
        (sourceControl Uc (p.profile 0) * sourceControl Uc (p.profile 1)) ^ 2 * (1 + |t| + height) ^ Jc *
        Z ^ (s.width + ε + ε₀) =
        Cc * (C₁ + 1) * diagonalControl s.radial.profile * (p.control Uc) ^ 2 * (1 + |t| + height) ^ Jc *
        Z ^ (s.width + ε + ε₀) := rfl
    rw [hshape]
    exact bound_upgrade hdiag (by positivity) (by nlinarith [mul_nonneg hCc.le hC₁]) (p.control_nonneg Uc)
      hctlU (by positivity) hpowU (Real.rpow_nonneg hZ0.le _) le_rfl
  · rw [energy_swap]
    have hover' : length Z X₂ + length Z X₁ + 6 * κ * (∑ i ∈ J \ R, w i) ≤ s.width + δ := by linarith
    have hb := hZ.2 η₀ Q C₁ hC₁ hpos (J \ R) θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL
      (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) X₂ X₁ hX₂ hX₁ hc₂ hc₁ hover' hrefl
    refine hb.trans ?_
    have hshape : Cc * (C₁ + 1) * diagonalControl s.radial.profile *
        (sourceControl Uc (p.profile 1) * sourceControl Uc (p.profile 0)) ^ 2 * (1 + |t| + height) ^ Jc *
        Z ^ (s.width + ε + ε₀) =
        Cc * (C₁ + 1) * diagonalControl s.radial.profile * (p.control Uc) ^ 2 * (1 + |t| + height) ^ Jc *
        Z ^ (s.width + ε + ε₀) := by
      unfold Profiles.control; rw [mul_comm (sourceControl Uc (p.profile 1))]
    rw [hshape]
    exact bound_upgrade hdiag (by positivity) (by nlinarith [mul_nonneg hCc.le hC₁]) (p.control_nonneg Uc)
      hctlU (by positivity) hpowU (Real.rpow_nonneg hZ0.le _) le_rfl

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
