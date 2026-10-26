import Candidate.Cycle63.Density.ExceptionalLift

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily ProbePhysical

def actualZeroRow {Label : Type*} (data : Label → RowData) (a T : ℝ)
    (u : NonzeroElement) : Prop :=
  ∃ j s, LFunction ((data j).character u) s = 0 ∧
    (s ≠ 1 ∨ ((data j).character u).residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

def orientedActualZeroRow {Label : Type*} (data : Label → RowData)
    (reverse : Label → Bool) (a T : ℝ) (u : NonzeroElement) : Prop :=
  ∃ j s, let χ := if reverse j then ((data j).character u).inverse else (data j).character u
    LFunction χ s = 0 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

theorem actual_zero_regular_bin {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (a T : ℝ) (ha : 33/40 ≤ a)
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
    (ha : 33/40 ≤ a) (u : NonzeroFrequency)
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
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
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

/-- Actual D+ for every member of the fixed natural dictionary, in either
whole-character orientation. Finite inducing cores and all their infinitely
many raw sixth-power multiples are paid by the same uniform convolution. -/
theorem fixed_dictionary_actual_raw_zero_density {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ orientedActualZeroRow D.data reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hf⟩ := fixed_dictionary_eventual_with_exceptions D loss hloss
  let P : DensityParameter → FreeRow → Prop := fun p u =>
    rawZeroBin D.data p.val.1 (7/8) p.val.2 ⟨u.val, u.property.1⟩ ∨ D.exceptionalCore u
  let exponent : DensityParameter → ℝ := fun p => unmarkedDensity (2*p.val.1-1)+loss
  let weight : DensityParameter → ℝ := fun p => (1+p.val.2)^J
  have hρ (p : DensityParameter) : 2/7 ≤ exponent p := by
    dsimp [exponent]
    linarith [unmarkedDensity_ge_two_sevenths (show 2*p.val.1-1 ≤ 3/4 by linarith [p.property.2.1])]
  have hw (p : DensityParameter) : 1 ≤ weight p := one_le_pow₀ (by linarith [p.property.2.2])
  have hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : DensityParameter, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C*weight p*Y^exponent p := by
    filter_upwards [hf] with Y hf
    intro p
    exact hf p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨C', hC', _, hfree⟩ := uniform_free_density_weighted_of_eventually P C exponent weight
    (fun p => by linarith [hρ p]) hw hevent
  obtain ⟨D₀, hD₀, hraw⟩ := raw_core_density_uniform
  refine ⟨J, C'*D₀, mul_pos hC' hD₀, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  let p : DensityParameter := ⟨(a,T), ha, ha', hT⟩
  have hb := hraw (P p) (C'*weight p) (exponent p) (by have := hw p; positivity) (hρ p)
    (fun Y hY F hF => hfree Y hY p F hF) H hH rows
    (fun u hu => ⟨(hrows u hu).1, oriented_zero_core_predicate D reverse a T ha u (hrows u hu).2⟩)
  convert hb using 1
  dsimp [p, weight, exponent]
  ring

#print axioms fixed_dictionary_actual_raw_zero_density
end SevenEighths.LocalMoment
end
end OAI
