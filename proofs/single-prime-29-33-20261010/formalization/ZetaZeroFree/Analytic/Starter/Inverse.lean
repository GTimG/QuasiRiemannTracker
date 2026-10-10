import OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

namespace ZetaZeroFree.Analytic.Starter

noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set Filter Asymptotics

theorem compact_raw_moment (W : ℝ → ℂ) (a b c κ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (hc : 0 < c) (hκ : 0 < κ) (data : RowData) :
    ∃ C : ℝ, 0 < C ∧ RawMoment data W c κ C := by
  have hcompact : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  let Ws := hcompact.toSchwartzMap hW
  obtain ⟨J, h⟩ := DetectorDictionaryInverseRawReference.raw_reference_moment
    Ws a b c κ ha hb hs hc hκ
  obtain ⟨C, hC, h⟩ := h data
  refine ⟨C, hC, ?_⟩
  have htest : InverseMoment.childLogTest (Ws : ℝ → ℂ) 0 = W := by
    funext x
    simp [InverseMoment.childLogTest, OAI.FourierBridge.logPhase, Ws]
  simpa only [htest, norm_zero, add_zero, one_pow, mul_one] using h 0

theorem compact_raw_moment_pair (W : ℝ → ℂ) (a b c κ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (hc : 0 < c) (hκ : 0 < κ) (data : RowData) :
    ∃ C : ℝ, 0 < C ∧ RawMoment data W c κ C ∧
      RawMoment data (scaleProfile W) c κ C := by
  have hs' := scaleProfile_support W a b hs
  have hW' : ContDiff ℝ ∞ (scaleProfile W) := by
    unfold scaleProfile
    exact ((hW.neg.div_const 2).sub (Complex.ofRealCLM.contDiff.mul
      ((contDiff_infty_iff_deriv.mp hW).2)))
  obtain ⟨C₀, hC₀, h₀⟩ := compact_raw_moment W a b c κ ha hb hs hW hc hκ data
  obtain ⟨C₁, hC₁, h₁⟩ := compact_raw_moment (scaleProfile W) a b c κ
    ha hb hs' hW' hc hκ data
  refine ⟨max C₀ C₁, lt_max_of_lt_left hC₀, ?_, ?_⟩
  · intro H D hH hD hHD rows hrows
    exact (h₀ H D hH hD hHD rows hrows).trans (by gcongr; exact le_max_left _ _)
  · intro H D hH hD hHD rows hrows
    exact (h₁ H D hH hD hHD rows hrows).trans (by gcongr; exact le_max_right _ _)

/-- The all-row raw moment yields the singleton inverse bound, with its original
row character and all presentation zeros retained. -/
theorem singleton_normalized_bound
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B)
    (hφs : Function.support φ ⊆ Ioo a b) (hφB : ∀ y, φ y ≤ B)
    (data : RowData) (u : FreeRow) (W : ℝ → ℂ) (wa wb : ℝ)
    (hwa : 0 < wa) (hwb : 0 < wb) (hWs : Function.support W ⊆ Icc wa wb)
    (hW : ContDiff ℝ ∞ W) (ε : ℝ) (hε : 0 < ε) :
    (fun D : ℝ => polynomial (data.character ⟨u.val, u.property.1⟩) true W D 0 0)
      =O[atTop] (fun D : ℝ => D ^ (5 / 12 + ε)) := by
  let r : ℝ := 1 + 1 / ε
  have hr : 1 ≤ r := by dsimp [r]; linarith [div_pos zero_lt_one hε]
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hrε : 1 ≤ r * ε := by dsimp [r]; field_simp; linarith
  obtain ⟨c, κ, K, hc, _, hκ, hK, he⟩ := no_slot_endpoint
    M H hH S φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB
    r 1 hrp.le (by norm_num)
  obtain ⟨C, hC, hraw₀, hraw₁⟩ := compact_raw_moment_pair
    W wa wb c κ hwa hwb hWs hW hc hκ data
  apply Asymptotics.IsBigO.of_bound (C * K + 1)
  have hroot := tendsto_rpow_atTop (div_pos zero_lt_one hrp)
  filter_upwards [hroot.eventually he, eventually_ge_atTop (1 : ℝ),
    hroot.eventually (eventually_ge_atTop
      ((Ideal.span {u.val}).absNorm : ℝ))] with D he hD hnorm
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hU : 1 ≤ D ^ (1 / r) := Real.one_le_rpow hD (by positivity)
  have hUr : (D ^ (1 / r)) ^ r = D := by
    rw [← Real.rpow_mul hDp.le, div_mul_cancel₀ 1 hrp.ne', Real.rpow_one]
  have hsum := he r data {u} W wa wb C hrp.le le_rfl hC.le hwa hwb.le hWs hW
    (by simpa using hnorm) hraw₀ hraw₁
  simp only [Finset.sum_singleton, hUr] at hsum
  have hexp : (sourceExponent r + 1) / r ≤ 2 * (5 / 12 + ε) := by
    rw [sourceExponent, max_eq_right (by linarith)]
    apply (div_le_iff₀ hrp).mpr
    nlinarith
  have hp : (D ^ (1 / r)) ^ (sourceExponent r + 1) ≤
      (D ^ (5 / 12 + ε)) ^ 2 := by
    rw [← Real.rpow_mul hDp.le, ← Real.rpow_natCast, ← Real.rpow_mul hDp.le]
    apply Real.rpow_le_rpow_of_exponent_le hD
    simpa only [one_div, inv_mul_eq_div, Nat.cast_ofNat, mul_comm] using hexp
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hC.le hK))
  have hconst : C * K ≤ (C * K + 1) ^ 2 := by nlinarith [mul_nonneg hC.le hK]
  have hn := hsum'.trans (mul_le_mul_of_nonneg_right hconst (sq_nonneg _))
  have hbound : ‖polynomial (data.character ⟨u.val, u.property.1⟩) true W D 0 0‖ ≤
      (C * K + 1) * D ^ (5 / 12 + ε) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simpa only [mul_pow] using hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hDp.le _)] using hbound

theorem represented_normalized_bound
    (data : RowData) (u : FreeRow) (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (ε : ℝ) (hε : 0 < ε) :
    (fun D : ℝ => polynomial (data.character ⟨u.val, u.property.1⟩) true W D 0 0)
      =O[atTop] (fun D : ℝ => D ^ (5 / 12 + ε)) := by
  let φ := CenteredMomentSectorLocalization.annulus
  have hφs : Function.support φ ⊆ Ioo (1 / 4 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_not_ge (fun h => hx
      (CenteredMomentSectorLocalization.annulus_zero_low x h)),
      lt_of_not_ge (fun h => hx
      (CenteredMomentSectorLocalization.annulus_zero_high x h))⟩
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (hφs.trans Ioo_subset_Icc_self)
  have hφp : tsupport φ ⊆ Ioi 0 := by
    intro x hx
    have hx' := (closure_minimal (hφs.trans Ioo_subset_Icc_self) isClosed_Icc) hx
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hx'.1
  have hφne : φ ≠ 0 := by
    intro hz
    have hz' := congrFun hz (1 / 2)
    norm_num [φ, CenteredMomentSectorLocalization.annulus,
      CenteredMomentSectorLocalization.cutoff_one _ le_rfl,
      CenteredMomentSectorLocalization.cutoff_zero _ le_rfl] at hz'
  let M : Ideal O := ⊤
  let : NeZero M := ⟨top_ne_bot⟩
  exact singleton_normalized_bound M ⊤ le_top ∅ φ
    CenteredMomentSectorLocalization.annulus_smooth hφc hφp
    (fun x => (CenteredMomentSectorLocalization.annulus_bounds x).1) hφne
    (1 / 4) 1 1 (by norm_num) (by norm_num) (by norm_num) hφs
    (fun x => (CenteredMomentSectorLocalization.annulus_bounds x).2)
    data u W a b ha hb hs hW ε hε

def inverseSum (χ : Character) (W : ℝ → ℂ) (D : ℝ) : ℂ :=
  ∑' I : HeckeDyadic.NonzeroIdeal, coefficient χ true I.val * W (norm I / D)

theorem inverseSum_eq_normalized (χ : Character) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) :
    inverseSum χ W D = (D : ℂ) ^ (1 / 2 : ℂ) * polynomial χ true W D 0 0 := by
  unfold polynomial
  simp only [summand, HeckeDyadic.shift, Complex.ofReal_zero, zero_mul, sub_zero,
    neg_zero, Complex.cpow_zero, mul_one]
  rw [← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  simp [inverseSum]

theorem represented_inverse_bound
    (data : RowData) (u : FreeRow) (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (ε : ℝ) (hε : 0 < ε) :
    inverseSum (data.character ⟨u.val, u.property.1⟩) W
      =O[atTop] (fun D : ℝ => D ^ (11 / 12 + ε)) := by
  have hp := represented_normalized_bound data u W a b ha hb hs hW ε hε
  have hroot : (fun D : ℝ => (D : ℂ) ^ (1 / 2 : ℂ))
      =O[atTop] (fun D : ℝ => D ^ (1 / 2 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
    norm_num [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hD.le _)]

  apply (hroot.mul hp).congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    exact (inverseSum_eq_normalized _ W D hD).symm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    rw [← Real.rpow_add hD]
    congr 1
    ring

theorem inverseSum_eq_finite (χ : Character) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J ≠ 0 → W ((J.absNorm : ℝ) / D) ≠ 0 → J ∈ S) :
    inverseSum χ W D = ∑ J ∈ S, coefficient χ true J * W ((J.absNorm : ℝ) / D) := by
  rw [inverseSum_eq_normalized χ W D hD,
    HeckeDetectorDyadicBridge.polynomial_eq_finite χ true W D 0 0 S hc]
  simp only [HeckeDyadic.shift, Complex.ofReal_zero, zero_mul, sub_zero,
    neg_zero, Complex.cpow_zero, mul_one]
  rw [← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  simp

theorem inverseSum_continuousOn (χ : Character) (W : ℝ → ℂ) (a b : ℝ)
    (hb : 0 < b) (hs : Function.support W ⊆ Icc a b) (hW : Continuous W) :
    ContinuousOn (inverseSum χ W) (Ioi 0) := by
  intro D₀ hD₀
  have hD₀p : 0 < D₀ := hD₀
  let S := (Ideal.finite_setOfPred_absNorm_le (S := O) ⌈2 * D₀ * b⌉₊).toFinset
  have heq : inverseSum χ W =ᶠ[𝓝 D₀]
      (fun D => ∑ J ∈ S, coefficient χ true J * W ((J.absNorm : ℝ) / D)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : D₀ / 2 < D₀)
      (by linarith : D₀ < 2 * D₀)] with D hD
    rcases hD with ⟨hDl, hDu⟩
    apply inverseSum_eq_finite χ W D (by linarith) S
    intro J hJ hw
    have hn : (J.absNorm : ℝ) ≤ D * b :=
      by simpa only [mul_comm] using (div_le_iff₀ (by linarith : 0 < D)).mp (hs hw).2
    have hn' : (J.absNorm : ℝ) ≤ (⌈2 * D₀ * b⌉₊ : ℝ) :=
      (hn.trans (by nlinarith)).trans (Nat.le_ceil _)
    simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact_mod_cast hn'
  have hcont : ContinuousAt
      (fun D => ∑ J ∈ S, coefficient χ true J * W ((J.absNorm : ℝ) / D)) D₀ := by
    apply tendsto_finsetSum
    intro J hJ
    exact continuousAt_const.mul (hW.continuousAt.comp
      (continuousAt_const.div continuousAt_id hD₀p.ne'))
  exact (hcont.congr_of_eventuallyEq heq).continuousWithinAt

theorem inverseSum_zero_near_zero (χ : Character) (W : ℝ → ℂ) (a b : ℝ)
    (hb : 0 < b) (hs : Function.support W ⊆ Icc a b) :
    inverseSum χ W =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
  filter_upwards [Ioo_mem_nhdsGT (div_pos zero_lt_one hb)] with D hD
  change (∑' I : HeckeDyadic.NonzeroIdeal, coefficient χ true I.val * W (norm I / D)) = 0
  trans ∑' _ : HeckeDyadic.NonzeroIdeal, (0 : ℂ)
  · apply tsum_congr
    intro I
    have hnorm : 1 ≤ norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hw : W (norm I / D) = 0 := by
      by_contra hw
      have hh := (div_le_iff₀ hD.1).mp (hs hw).2
      have hd := (lt_div_iff₀ hb).mp hD.2
      nlinarith
    simp [hw]
  · exact tsum_zero

end
end ZetaZeroFree.Analytic.Starter

