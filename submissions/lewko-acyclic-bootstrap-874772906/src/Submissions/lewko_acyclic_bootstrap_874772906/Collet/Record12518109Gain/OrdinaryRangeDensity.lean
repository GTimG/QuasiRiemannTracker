/- Range extension of Cycle61 density wrappers, Hailey Collet, Apache-2.0.
The actual maxima count already has lower boundary 51/100; every extended
wrapper body below is checked at the literal boundary 81/100. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.BufferedPartition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.OrdinaryRangeUniform
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.ActualZeros
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.Record12518109GainOrdinaryRange
open ProbePhysical
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily
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

theorem actual_zero_regular_bin {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (a T : ℝ) (ha : 81/100 ≤ a)
    (u : FreeRow) (hu : ¬D.exceptionalCore u)
    (hz : actualZeroRow D.data a T ⟨u.val, u.property.1⟩) :
    rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩ := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  have hn := D.regular_nonprincipal u hu
  have hmax := zero_re_le_maximum (fun j => (D.data j).character ⟨u.val, u.property.1⟩)
    hn T j (by linarith) ht hz
  have hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta := by
    have hh := HeckeZeroSupremum.zero_re_le_beta ((D.data j).character ⟨u.val, u.property.1⟩)
      (by linarith) hpole hz
    linarith
  exact ⟨hn, hs.trans hmax, (zeroMaximum_le_beta _ hn hβlo T).trans incumbent_beta_upper⟩

/-- Actual zeros of any orientation lie over either a counted nonprincipal
core or one of the fixed exceptional cores. Conjugation applies to the
whole character, including its Euler holes. -/
theorem oriented_zero_core_predicate {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (reverse : Label → Bool) (a T : ℝ)
    (ha : 81/100 ≤ a) (u : NonzeroFrequency)
    (hz : orientedActualZeroRow D.data reverse a T u) :
    let core := (sixthFrequencyEquiv.symm u).1
    rawZeroBin D.data a (7/8) T ⟨core.val, core.property.1⟩ ∨ D.exceptionalCore core := by
  let p := sixthFrequencyEquiv.symm u
  have hpu : sixthFrequencyEquiv p = u := sixthFrequencyEquiv.apply_symm_apply u
  change rawZeroBin D.data a (7/8) T ⟨p.1.val, p.1.property.1⟩ ∨ D.exceptionalCore p.1
  by_cases hex : D.exceptionalCore p.1
  · exact Or.inr hex
  · have hn := D.regular_nonprincipal p.1 hex
    obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
    have hraw : ((D.data j).character u).residue ≠ 1 := by
      have hh := amplified_nonprincipal (D.data j) ⟨p.1.val, p.1.property.1⟩ p.2 (hn j)
      change ((D.data j).character (sixthFrequencyEquiv p)).residue ≠ 1 at hh
      rw [hpu] at hh
      exact hh
    have hz' : actualZeroRow D.data a T u := by
      cases hr : reverse j
      · exact ⟨j, s, by simpa only [hr, Bool.false_eq_true, ite_false] using hz,
          Or.inr hraw, hs, ht⟩
      · have hi : LFunction ((D.data j).character u) (starRingEnd ℂ s) = 0 := by
          simpa only [hr, ite_true, LFunction_inverse_conj _ hraw, map_eq_zero] using hz
        exact ⟨j, starRingEnd ℂ s, hi, Or.inr hraw,
          by simpa only [Complex.conj_re] using hs, by simpa using ht⟩
    obtain ⟨j', s', hz', hpole', hs', ht'⟩ := hz'
    have hzero : LFunction ((D.data j').character ⟨p.1.val, p.1.property.1⟩) s' = 0 := by
      apply (sixthFrequency_positive_zeros (D.data j') p (hn j') (show 0 < s'.re by linarith)).mp
      rw [hpu]
      exact hz'
    exact Or.inl (actual_zero_regular_bin D a T ha p.1 hex
      ⟨j', s', hzero, Or.inr (hn j'), hs', ht'⟩)

theorem fixed_dictionary_eventual_with_exceptions {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℝ in atTop,
      ∀ a T : ℝ, 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ Y ∧
        (rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩ ∨ D.exceptionalCore u)) →
        (rows.card : ℝ) ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hf⟩ := fixed_dictionary_eventual_free_density D loss hloss
  let E : Finset FreeRow := D.exceptional_cores_finite.toFinset
  refine ⟨J, C+(E.card : ℝ), by positivity, ?_⟩
  filter_upwards [hf, eventually_ge_atTop (1 : ℝ)] with Y hf hY
  intro a T ha ha' hT rows hrows
  let good : FreeRow → Prop := fun u => rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩
  let kept := rows.filter good
  let removed := rows.filter (fun u => ¬good u)
  have hk := hf a T ha ha' hT kept (fun u hu =>
    ⟨(hrows u (Finset.mem_filter.mp hu).1).1, (Finset.mem_filter.mp hu).2⟩)
  have hsub : removed ⊆ E := by
    intro u hu
    have hr := hrows u (Finset.mem_filter.mp hu).1
    exact (Set.Finite.mem_toFinset _).mpr (hr.2.resolve_left (Finset.mem_filter.mp hu).2)
  have hc : (removed.card : ℝ) ≤ (E.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  have hpart : (rows.card : ℝ) = (kept.card : ℝ)+(removed.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := rows) (p := good)).symm
  have hρ : 0 ≤ unmarkedDensity (2*a-1)+loss := by
    linarith [unmarkedDensity_ge_two_sevenths (show 2*a-1 ≤ 3/4 by linarith)]
  have hweight : 1 ≤ (1+T)^J := one_le_pow₀ (by linarith)
  have hpower : 1 ≤ Y^(unmarkedDensity (2*a-1)+loss) := Real.one_le_rpow hY hρ
  have he : (E.card : ℝ) ≤ (E.card : ℝ)*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
    have he0 : 0 ≤ (E.card : ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ (E.card : ℝ)*(1+T)^J := le_mul_of_one_le_right he0 hweight
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpower
  rw [hpart]
  calc
    _ ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss)+
        (E.card : ℝ)*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := add_le_add hk (hc.trans he)
    _ = _ := by ring


end SevenEighths.Record12518109GainOrdinaryRange
end
end OAI
