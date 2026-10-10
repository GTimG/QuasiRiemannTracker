import ZetaZeroFree.Analytic.Starter.Inverse
import OAI.NumberTheory.DirichletL.Continuation
import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import OAI.NumberTheory.DirichletL.Mellin.CompactWeights
import OAI.NumberTheory.DirichletL.Hecke.UnitRows
import OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration

namespace ZetaZeroFree.Analytic.Starter

noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open Set Filter Asymptotics MeasureTheory
open scoped Classical Topology ContDiff

theorem inverseSum_mellin (χ : Character) (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) (hs : 1 < s.re) :
    mellin (inverseSum χ W) (-s) = mellin W s * HeckeDyadic.series χ true s := by
  let a := ShortDraftHeckeBridge.normFiberCoeff (coefficient χ true)
  have ha0 : a 0 = 0 := by
    unfold a ShortDraftHeckeBridge.normFiberCoeff
    apply Finset.sum_eq_zero
    intro I hI
    have hi : I.absNorm = 0 := by simpa using hI
    rw [Ideal.absNorm_eq_zero_iff.mp hi]
    exact coefficient_zero χ true
  have hlsum : LSeriesSummable a s := by
    have h := (SmoothMobiusCorrection.idealDirichlet_summable (coefficient χ true)
      (coefficient_norm_le χ true) s hs).hasSum.tsum_fiberwise Ideal.absNorm
    change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // I.absNorm = n},
      coefficient χ true I.val * CubicEisenstein.fullIdealWeight s I.val) _ at h
    simp_rw [SmoothMobiusCorrection.idealDirichlet_fiber] at h
    exact h.summable
  have hF : ∀ t : ℝ, 0 < t → HasSum
      (fun n : ℕ => a n * W ((n : ℝ) * t)) (inverseSum χ W t⁻¹) := by
    intro t ht
    let f : Ideal O → ℂ := fun I => coefficient χ true I * W ((I.absNorm : ℝ) * t)
    have hfin : (Function.support f).Finite := by
      apply (Ideal.finite_setOfPred_absNorm_le (S := O) ⌈2 / t⌉₊).subset
      intro I hI
      have hw : W ((I.absNorm : ℝ) * t) ≠ 0 := right_ne_zero_of_mul hI
      have hlo : (I.absNorm : ℝ) * t < 2 :=
        lt_of_not_ge (fun h => hw (hsupp _ (Or.inr h)))
      have hn : (I.absNorm : ℝ) ≤ (⌈2 / t⌉₊ : ℝ) :=
        ((lt_div_iff₀ ht).mpr hlo).le.trans (Nat.le_ceil _)
      exact_mod_cast hn
    have heq : (∑' I : Ideal O, f I) = inverseSum χ W t⁻¹ := by
      rw [← tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I ≠ 0})]
      · apply tsum_congr
        intro I
        simp [f, HeckeDyadic.norm, div_inv_eq_mul]
      · intro I hI hi
        subst I
        exact hI (by change coefficient χ true 0 * W _ = 0; rw [coefficient_zero, zero_mul])
    have hfiber (n : ℕ) : (∑' I : {I : Ideal O // I.absNorm = n}, f I.val) =
        a n * W ((n : ℝ) * t) := by
      simp only [f]
      have hi (I : {I : Ideal O // I.absNorm = n}) : I.val.absNorm = n := I.property
      simp_rw [hi]
      rw [tsum_mul_right, SmoothMobiusCorrection.normFiber_tsum]
    have hsum : Summable f := hasSum_sum_of_ne_finset_zero (s := hfin.toFinset)
      (fun I hI => by
        by_contra hn
        exact hI (by simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hn)) |>.summable
    have h := hsum.hasSum.tsum_fiberwise Ideal.absNorm
    change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // I.absNorm = n}, f I.val) _ at h
    rw [heq] at h
    simpa only [hfiber] using h
  have hm := CompactMellinBridge.mellin_weighted_sum a W
    (fun t => inverseSum χ W t⁻¹) s ha0 hF
    (CompactMellinBridge.weighted_term_integrable a ha0 W s
      (CompactMellinBridge.compact_weight_mellin_convergent W hW hsupp s))
    (CompactMellinBridge.weighted_terms_fubini a ha0 W s hlsum) hlsum
  have hseries : LSeries a s = HeckeDyadic.series χ true s := by
    rw [← SmoothMobiusCorrection.idealDirichlet_eq_LSeries (coefficient χ true)
      (coefficient_norm_le χ true) s hs, HeckeDyadic.series_eq_tsum χ true hs]
    have hsub : (∑' I : HeckeDyadic.NonzeroIdeal, coefficient χ true I.val *
        CubicEisenstein.fullIdealWeight s I.val) =
        ∑' I : Ideal O, coefficient χ true I * CubicEisenstein.fullIdealWeight s I := by
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I ≠ 0})
        (f := fun I => coefficient χ true I * CubicEisenstein.fullIdealWeight s I)
      intro I hI hi
      subst I
      exact hI (by dsimp only; rw [coefficient_zero, zero_mul])
    rw [← hsub]
    apply tsum_congr
    intro I
    rw [CubicEisenstein.fullIdealWeight, ite_eq_right I.property]
    simp only [HeckeDyadic.norm, Complex.ofReal_natCast]

  simpa only [inv_inv, hseries] using hm

theorem inverseSum_mellin_eq_div (χ : Character) (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) (hs : 1 < s.re) :
    mellin (inverseSum χ W) (-s) = mellin W s / LFunction χ s := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  rw [inverseSum_mellin χ W hW hsupp s hs]
  change mellin W s * HeckeReciprocal.reciprocal χ s = _
  rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
  rfl

theorem represented_inverse_mellin_analytic
    (data : RowData) (u : FreeRow) (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) :
    AnalyticOnNhd ℂ (fun s : ℂ =>
      mellin (inverseSum (data.character ⟨u.val, u.property.1⟩) W) (-s))
      {s : ℂ | 11 / 12 < s.re} := by
  let χ := data.character ⟨u.val, u.property.1⟩
  have hlocal : LocallyIntegrableOn (inverseSum χ W) (Ioi 0) :=
    (inverseSum_continuousOn χ W a b hb hs hW.continuous).locallyIntegrableOn
      measurableSet_Ioi
  have hzero : Continuation.RapidDecayAtZero (inverseSum χ W) := by
    intro B
    exact (inverseSum_zero_near_zero χ W a b hb hs).isBigO.trans (isBigO_zero _ _)
  intro s hs'
  let ε : ℝ := (s.re - 11 / 12) / 2
  have hε : 0 < ε := by dsimp [ε]; change 11 / 12 < s.re at hs'; linarith
  have htop := represented_inverse_bound data u W a b ha hb hs hW ε hε
  have hm := Continuation.signalMellin_analytic (inverseSum χ W) (11 / 12 + ε) 0
    hlocal (by simpa only [add_zero] using htop) hzero
  have hs'' : 11 / 12 + ε < s.re := by
    dsimp [ε]; change 11 / 12 < s.re at hs'; linarith
  have hf : Continuation.signalMellin (inverseSum χ W) 0 =
      (fun z : ℂ => mellin (inverseSum χ W) (-z)) := by
    funext z
    simp [Continuation.signalMellin]
  rw [hf] at hm
  exact hm s hs''

/-- The test-dependent Mellin product identity transports the independently
proved inverse bound to nonvanishing, including the principal regularizer. -/
theorem represented_nonzero_of_mellin_identity
    (data : RowData) (u : FreeRow) (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W)
    (hM : AnalyticOnNhd ℂ (mellin W) {s : ℂ | 11 / 12 < s.re})
    (heq : ∀ s : ℂ, 1 < s.re →
      HeckeSignal.regularL (data.character ⟨u.val, u.property.1⟩) s *
        mellin (inverseSum (data.character ⟨u.val, u.property.1⟩) W) (-s) =
      HeckeSignal.targetRegularizer (data.character ⟨u.val, u.property.1⟩) s * mellin W s)
    {ρ : ℂ} (hρ : 11 / 12 < ρ.re)
    (hpole : ρ ≠ 1 ∨ (data.character ⟨u.val, u.property.1⟩).residue ≠ 1)
    (hprobe : mellin W ρ ≠ 0) :
    LFunction (data.character ⟨u.val, u.property.1⟩) ρ ≠ 0 := by
  let χ := data.character ⟨u.val, u.property.1⟩
  have hL : AnalyticOnNhd ℂ (HeckeSignal.regularL χ) {s : ℂ | 11 / 12 < s.re} :=
    (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
      (HeckeSignal.regularL_entire χ).differentiableOn
  have hR : AnalyticOnNhd ℂ (HeckeSignal.targetRegularizer χ)
      {s : ℂ | 11 / 12 < s.re} :=
    (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
      (HeckeSignal.targetRegularizer_entire χ).differentiableOn
  have hid := Continuation.product_identity_on_halfPlane (11 / 12) 1
    (HeckeSignal.regularL χ) (fun s => mellin (inverseSum χ W) (-s))
    (fun s => HeckeSignal.targetRegularizer χ s * mellin W s)
    hL (represented_inverse_mellin_analytic data u W a b ha hb hs hW)
    (hR.mul hM) (by simpa only [max_eq_right (by norm_num : (11 / 12 : ℝ) ≤ 1)] using heq) hρ
  have h0 : ρ ≠ 0 := by intro h; norm_num [h] at hρ
  intro hz
  change HeckeSignal.regularL χ ρ * mellin (inverseSum χ W) (-ρ) =
    HeckeSignal.targetRegularizer χ ρ * mellin W ρ at hid
  rw [HeckeSignal.regularL_eq χ h0 hpole, hz, mul_zero, zero_mul] at hid
  exact (mul_ne_zero (HeckeSignal.targetRegularizer_ne_zero χ hpole) hprobe) hid.symm

theorem compact_test_mellin_entire (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0) :
    Differentiable ℂ (mellin W) := by
  have hlocal : LocallyIntegrableOn W (Ioi 0) :=
    hW.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have ht : W =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    exact hsupp y (Or.inr hy)
  have hz : W =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    exact hsupp y (Or.inl hy.2.le)
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1) hlocal
    (ht.isBigO.trans (isBigO_zero _ _)) (by linarith)
    (hz.isBigO.trans (isBigO_zero _ _)) (by linarith)

theorem represented_LFunction_ne_zero (data : RowData) (u : FreeRow)
    {ρ : ℂ} (hρ : 11 / 12 < ρ.re)
    (hpole : ρ ≠ 1 ∨ (data.character ⟨u.val, u.property.1⟩).residue ≠ 1) :
    LFunction (data.character ⟨u.val, u.property.1⟩) ρ ≠ 0 := by
  let χ := data.character ⟨u.val, u.property.1⟩
  let W := ConcreteCompactWeight.weight ρ
  have hW := ConcreteCompactWeight.weight_smooth ρ
  have hsupp := ConcreteCompactWeight.weight_support ρ
  have hs : Function.support W ⊆ Icc (1 : ℝ) 2 := by
    intro y hy
    exact ⟨(lt_of_not_ge (fun h => hy (hsupp y (Or.inl h)))).le,
      (lt_of_not_ge (fun h => hy (hsupp y (Or.inr h)))).le⟩
  have hM : AnalyticOnNhd ℂ (mellin W) {s : ℂ | 11 / 12 < s.re} :=
    (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
      (compact_test_mellin_entire W hW hsupp).differentiableOn
  apply represented_nonzero_of_mellin_identity data u W 1 2
    (by norm_num) (by norm_num) hs hW hM ?_ hρ hpole
    (ConcreteCompactWeight.weight_mellin_ne_zero ρ)
  intro s hs'
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs'
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs'
  rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
    inverseSum_mellin χ W hW hsupp s hs']
  change (HeckeSignal.targetRegularizer χ s * LFunction χ s) *
    (mellin W s * HeckeReciprocal.reciprocal χ s) = _
  rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
  have hn := LFunction_ne_zero_of_one_lt_re χ hs'
  field_simp
  ring


def starterData (χ : Character) : RowData where
  η := χ
  m := 36
  f := 1
  m_ne_zero := by norm_num
  f_ne_zero := one_ne_zero
  lambda_dvd := ((dvd_pow_self ConcretePrimeRowBridge.goodLambda
    (by decide : (2 : ℕ) ≠ 0)).trans ActualEisensteinCubic.lambda_sq_dvd_three).trans
    ⟨12, by norm_num⟩
  two_dvd := ⟨18, by norm_num⟩

def starterRow : FreeRow := ⟨1, one_ne_zero, by
  intro P
  simp [Ideal.span_singleton_one, ← Ideal.one_eq_top,
    UniqueFactorizationMonoid.normalizedFactors_one]⟩

theorem starterData_mask (χ : Character) (J : Ideal O) :
    idealCoeff ((starterData χ).character ⟨1, one_ne_zero⟩) J =
      if IsCoprime J (Ideal.span {(36 : O)}) then idealCoeff χ J else 0 := by
  by_cases hJ : J = 0
  · subst J
    rw [map_zero, map_zero]
    split_ifs <;> rfl
  have hrow := HeckeRowClosure.idealCoeff_eq_row χ
    ((starterData χ).character ⟨1, one_ne_zero⟩) 36 1 1
    ((starterData χ).character_spec ⟨1, one_ne_zero⟩) J
  simp only [one_pow, mul_one] at hrow
  by_cases hsup : CanonicalQuadraticSieve.Supported J
  · rw [hrow, CanonicalRowCompletion.idealRowHom_sixth_mask 36 J hsup]
    split_ifs <;> simp
  · have hzero := row_coeff_zero_unsupported χ
      ((starterData χ).character ⟨1, one_ne_zero⟩) 36 1 1
      ((starterData χ).character_spec ⟨1, one_ne_zero⟩)
      (starterData χ).lambda_dvd (starterData χ).two_dvd J hsup
    rw [hzero]
    have hnc : ¬IsCoprime J (Ideal.span {(36 : O)}) := by
      intro hc
      let n := ConcretePrimeRowBridge.idealGenerator J
      have hn : Ideal.span {n} = J := ConcretePrimeRowBridge.span_idealGenerator J
      have hcn : IsCoprime n (36 : O) :=
        (Ideal.isCoprime_span_singleton_iff _ _).mp (hn ▸ hc)
      apply hsup
      rw [← hn, CanonicalQuadraticSieve.supported_span_iff]
      refine ⟨?_, ?_⟩
      · intro hd
        exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit
          (hcn.isUnit_of_dvd' hd (starterData χ).lambda_dvd)
      · intro hd
        exact CanonicalRowCompletion.negative_two_prime.not_isUnit
          (hcn.isUnit_of_dvd' hd (starterData χ).two_dvd).neg
    simp [hnc]

theorem starter_regularized_mask (χ : Character) :
    EqOn (HeckeReciprocal.regularizedL
      ((starterData χ).character ⟨1, one_ne_zero⟩))
      (fun s => HeckeReciprocal.regularizedL χ s *
        HeckeFiniteDeletion.factors (Ideal.span {(36 : O)}) χ s) {s : ℂ | 0 < s.re} := by
  let ψ := (starterData χ).character ⟨1, one_ne_zero⟩
  apply EqOn.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (HeckeReciprocal.regularizedL χ)
    (HeckeFiniteDeletion.factors (Ideal.span {(36 : O)}) χ)
    (HeckeReciprocal.regularizedL ψ)
    (HeckeFiniteDeletion.regularizedL_analytic χ)
    ((Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
      (HeckeFiniteDeletion.factors_differentiable _ _).differentiableOn)
    (HeckeFiniteDeletion.regularizedL_analytic ψ)
  intro s hs
  have hs1 : 1 < s.re := by simpa using hs
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeReciprocal.regularizedL_eq χ h0 h1,
    HeckeReciprocal.regularizedL_eq ψ h0 h1, LFunction_eq_series χ hs1,
    LFunction_eq_series ψ hs1, HeckeFiniteDeletion.factors_eq]
  have he := IdealEuler.series_of_coprime_mask (Ideal.span {(36 : O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
    (idealCoeff ψ) (idealCoeff χ) (idealCoeff_norm_le_one χ)
    (starterData_mask χ) s hs1
  rw [he]
  ring

theorem beta_le_eleven_twelfths_of_nonvanishing
    (h : ∀ (χ : Character) (s : ℂ), 11 / 12 < s.re →
      (s ≠ 1 ∨ χ.residue ≠ 1) → LFunction χ s ≠ 0) :
    HeckeZeroSupremum.beta ≤ 11 / 12 := by
  apply csSup_le HeckeZeroSupremum.zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · obtain ⟨χ, s, _, hpole, hz, rfl⟩ := hx
    by_contra hle
    exact h χ s (lt_of_not_ge hle) hpole hz

theorem LFunction_ne_zero_of_eleven_twelfths_lt_re (χ : Character) {s : ℂ}
    (hs : 11 / 12 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact LFunction_ne_zero_of_one_le_re χ hge hpole
  have hlt : s.re < 1 := lt_of_not_ge hge
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hlt
  have hψ := represented_LFunction_ne_zero (starterData χ) starterRow hs (Or.inl h1)
  have hmask := starter_regularized_mask χ (show 0 < s.re by linarith)
  dsimp only at hmask
  rw [HeckeReciprocal.regularizedL_eq _ h0 h1,
    HeckeReciprocal.regularizedL_eq χ h0 h1] at hmask
  intro hz
  rw [hz, mul_zero, zero_mul] at hmask
  apply hψ
  exact (mul_eq_zero.mp hmask).resolve_left (sub_ne_zero.mpr h1)

theorem beta_le_eleven_twelfths : HeckeZeroSupremum.beta ≤ 11 / 12 :=
  beta_le_eleven_twelfths_of_nonvanishing
    (fun χ _ hs hpole => LFunction_ne_zero_of_eleven_twelfths_lt_re χ hs hpole)

end
end ZetaZeroFree.Analytic.Starter
