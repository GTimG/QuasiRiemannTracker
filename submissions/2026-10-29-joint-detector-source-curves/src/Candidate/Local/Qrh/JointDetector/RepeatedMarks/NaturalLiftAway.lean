/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FiniteCoreLifts
import Candidate.Local.Qrh.JointDetector.AdaptivePrice
import Candidate.Local.Qrh.JointDetector.RefinedSupplier
import Candidate.Local.Qrh.JointDetector.FineAdaptiveSupplier.High
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint

namespace Qrh.JointDetector.RepeatedMarks
open FineNaturalCount FineDetectorWords FineDetectorCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open HeckeDetectorWitnessRows
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- Lift a literal uniform free-core count to the complete natural row
population. The root-dependent predicate stays inside the free count;
principal and small-core rows are paid explicitly, not discarded. -/
theorem natural_count_of_uniform_free_count_away
    {Label : Type} [Fintype Label] (base : Label → Character) (reverse : Label → Bool) (extra : Finset FreeRow) :
    ∃ D Cpr : ℝ, 0 < D ∧ 0 < Cpr ∧
    ∀ (Z B b T dmin R Ccore : ℝ) (J : ℕ)
    (hZ : 1 < Z) (hdmin : 0 < dmin) (hBlower : Z^(20*dmin) ≤ B)
    (hT : 0 ≤ T) (hR : (1/4:ℝ) ≤ R) (hCcore : 0 < Ccore)
    (P : HeckeInverseAmplification.NonzeroIdeal → FreeRow → Prop)
    (hcore : ∀ (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (F : Finset FreeRow),
      Z^dmin ≤ Y → Y ≤ B →
      (∀ u ∈ F, rowNorm u ≤ Y ∧
        ¬(FixedUnmarkedDictionary.ofBases base).exceptionalCore u ∧ u ∉ extra ∧
        naturalActualZeroRow base reverse b T (sixthFrequencyEquiv (u,root)) ∧ P root u) →
      (F.card:ℝ) ≤ Ccore*(1+T)^J*Y^R)
    (rows : Finset NonzeroFrequency)
    (hrows : ∀ z ∈ rows, rawFrequencyNorm z ≤ B ∧ naturalActualZeroRow base reverse b T z ∧
      P (sixthFrequencyEquiv.symm z).2 (sixthFrequencyEquiv.symm z).1),
    (rows.card:ℝ) ≤ (Ccore*D+Cpr+98304)*(1+T)^J*B^R := by
  obtain ⟨D,hD,hroots⟩ := natural_root_count_of_uniform_free_counts
  let Dct := FixedUnmarkedDictionary.ofBases base
  let badSet := Dct.exceptional_cores_finite.toFinset ∪ extra
  have hbad (u : FreeRow) : u ∈ badSet ↔ Dct.exceptionalCore u ∨ u ∈ extra := by
    simp only [badSet,Finset.mem_union,Set.Finite.mem_toFinset,Set.mem_setOf_eq,FixedUnmarkedDictionary.exceptionalCore]
  obtain ⟨Cpr,hCpr,hprincipal⟩ := finite_exceptional_raw_count badSet
  refine ⟨D,Cpr,hD,hCpr,?_⟩
  intro Z B b T dmin R Ccore J hZ hdmin hBlower hT hR hCcore P hcore rows hrows
  let C := Ccore*D+Cpr+98304
  have hC : 0 < C := by dsimp [C]; positivity
  change (rows.card:ℝ) ≤ C*(1+T)^J*B^R
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hB1 : 1 ≤ B := (Real.one_le_rpow hZ.le (by linarith : 0 ≤ 20*dmin)).trans hBlower
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hBsmall : Z^dmin ≤ B^(1/20 : ℝ) := by
    calc
      _ = (Z^(20*dmin))^(1/20 : ℝ) := by rw [← Real.rpow_mul hZp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hBlower (by norm_num)
  let Q : HeckeInverseAmplification.NonzeroIdeal → FreeRow → Prop := fun root u =>
    rowNorm u ≤ B ∧ u ∉ badSet ∧ B^(1/20 : ℝ) ≤ rowNorm u ∧
    naturalActualZeroRow base reverse b T (sixthFrequencyEquiv (u,root)) ∧ P root u
  have hfree (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (hY : 1 ≤ Y)
      (F : Finset FreeRow) (hF : ∀ u ∈ F, rowNorm u ≤ Y ∧ Q root u) :
      (F.card : ℝ) ≤ (Ccore*(1+T)^J)*Y^R := by
    by_cases hne : F.Nonempty
    · obtain ⟨u₀,hu₀⟩ := hne
      let Ystar := min Y B
      have hFscale : ∀ u ∈ F, rowNorm u ≤ Ystar := by
        intro u hu
        exact le_min (hF u hu).1 (hF u hu).2.1
      have hsmallY : B^(1/20 : ℝ) ≤ Ystar :=
        (hF u₀ hu₀).2.2.2.1.trans (hFscale u₀ hu₀)
      have hYlower : Z^dmin ≤ Ystar := hBsmall.trans hsmallY
      have hc := hcore root Ystar F hYlower (min_le_right Y B)
        (fun u hu => ⟨hFscale u hu,
          (not_or.mp (mt (hbad u).mpr (hF u hu).2.2.1)).1,
          (not_or.mp (mt (hbad u).mpr (hF u hu).2.2.1)).2,
          (hF u hu).2.2.2.2.1,(hF u hu).2.2.2.2.2⟩)
      exact hc.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity [Ystar]) (min_le_left Y B) (by linarith)) (by positivity))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  let exceptional := rows.filter fun z => (sixthFrequencyEquiv.symm z).1 ∈ badSet
  let regular := rows.filter fun z => ¬(sixthFrequencyEquiv.symm z).1 ∈ badSet
  let small := regular.filter fun z => rowNorm (sixthFrequencyEquiv.symm z).1 < B^(1/20 : ℝ)
  let large := regular.filter fun z => ¬rowNorm (sixthFrequencyEquiv.symm z).1 < B^(1/20 : ℝ)
  have hcard : (rows.card : ℝ) = (exceptional.card : ℝ)+(small.card : ℝ)+(large.card : ℝ) := by
    have h1 := Finset.card_filter_add_card_filter_not (s := rows) (fun z => (sixthFrequencyEquiv.symm z).1 ∈ badSet)
    have h2 := Finset.card_filter_add_card_filter_not (s := regular)
      (fun z => rowNorm (sixthFrequencyEquiv.symm z).1 < B^(1/20 : ℝ))
    change exceptional.card+regular.card = rows.card at h1
    change small.card+large.card = regular.card at h2
    change (rows.card : ℝ) = _
    exact_mod_cast (show rows.card = exceptional.card+small.card+large.card by
      omega)
  have hexceptional : (exceptional.card : ℝ) ≤ Cpr*B^R := by
    have hp := hprincipal B hB1 exceptional (by
      intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      exact ⟨(hrows z hz).1,he⟩)
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) hCpr.le)
  have hsmall : (small.card : ℝ) ≤ 98304*B^R := by
    have hs := small_sixth_core_count_le_joint (small.image Subtype.val) B R hB1 hR
      (by intro z hz; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz; exact u.property)
      (by intro z hz; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
          exact (hrows u (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1).1)
      (by intro z hz; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
          rw [raw_sixth_remainder]
          exact (Finset.mem_filter.mp hu).2.le)
    simpa only [Finset.card_image_of_injective small Subtype.val_injective] using hs
  have hlarge : (large.card : ℝ) ≤ (Ccore*(1+T)^J)*D*B^R := by
    apply hroots Q (Ccore*(1+T)^J) R (by positivity) hR hfree B hBp large
    intro z hz
    obtain ⟨hz,hbig⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz,hregular⟩ := Finset.mem_filter.mp hz
    have hrow := hrows z hz
    have hcoreNorm : rowNorm (sixthFrequencyEquiv.symm z).1 ≤ B := by
      have hn := raw_sixth_norm (sixthFrequencyEquiv.symm z)
      simp only [Equiv.apply_symm_apply] at hn
      have hroot : 1 ≤ (((sixthFrequencyEquiv.symm z).2.val.absNorm : ℝ))^6 := by
        have hp : 1 ≤ ((sixthFrequencyEquiv.symm z).2.val.absNorm : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (sixthFrequencyEquiv.symm z).2.property)
        exact one_le_pow₀ hp
      have hu := rowNorm_ge_one (sixthFrequencyEquiv.symm z).1
      nlinarith [hrow.1]
    refine ⟨hrow.1,hcoreNorm,hregular,le_of_not_gt hbig,?_,hrow.2.2⟩
    change naturalActualZeroRow base reverse b T (sixthFrequencyEquiv (sixthFrequencyEquiv.symm z))
    rw [Equiv.apply_symm_apply]
    exact hrow.2.1
  have hheight : 1 ≤ (1+T)^J := one_le_pow₀ (by linarith)
  calc
    _ = (exceptional.card : ℝ)+(small.card : ℝ)+(large.card : ℝ) := hcard
    _ ≤ Cpr*B^R+98304*B^R+(Ccore*(1+T)^J)*D*B^R := add_le_add (add_le_add hexceptional hsmall) hlarge
    _ ≤ C*(1+T)^J*B^R := by
      dsimp only [C]
      have hp : 0 ≤ B^R := by positivity
      nlinarith

end
end Qrh.JointDetector.RepeatedMarks
