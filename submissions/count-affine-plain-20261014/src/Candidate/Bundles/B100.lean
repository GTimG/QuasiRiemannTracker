/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B097
import Candidate.Bundles.B099
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

/- BEGIN ORIGINAL Cycle61.Density.ActualMaximaCount; sha256 5a08866dc7d633db6061d0f4fc289fd49f88a2b41b658ac3574096f55f4d18c4 -/
section
                                       
                                        
                               

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily

/-- Count a bin of actual natural-character maxima. All moment and detector
inputs are proved; only the literal finite population and its zero-bin
membership enter the live universal statement. -/
theorem actual_maxima_bin_count {Label : Type*} [Fintype Label]
    (S : DensityCountingSetup) (D : FixedUnmarkedDictionary Label)
    (εm ηloss ε e κ ηaux : ℝ) (I : ℕ)
    (hεm : 0 < εm) (hηloss : 0 < ηloss)
    (hε : 0 < ε) (hε' : ε ≤ 1/1000)
    (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hηaux : 0 ≤ ηaux)
    (hbudget : 288*e+8*κ+2*ηaux ≤ ε/2)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ,
      0 < τ → τ < 1/2 → 4*τ < ηaux → ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (b height : ℝ) (i : ℕ), i ≤ I → 51/100 < b → b ≤ 7/8 →
      0 ≤ height → 2*Real.pi*U^(τ/2) + (3*i : ℕ)*U^τ ≤ height →
      ∀ (rows : Finset FreeRow),
      (∀ u ∈ rows, rowNorm u ≤ U) →
      ∀ (hn : ∀ u : rows, ∀ j, (D.naturalFamily u.val j).residue ≠ 1),
      (∀ u : rows, ∀ j, ((D.naturalFamily u.val j).modulus.absNorm : ℝ) ≤ U) →
      (∀ u : rows, zeroMaximum (D.naturalFamily u.val) (hn u)
        (3*(i+1 : ℕ)*U^τ) < b+2*e) →
      (∀ u : rows, b ≤ zeroMaximum (D.naturalFamily u.val) (hn u)
        ((3*i : ℕ)*U^τ)) →
        (rows.card : ℝ) ≤ C*(1+height)^J*
          U^(unmarkedDensity (2*b-1)+156*ε+εm+ηloss) := by
  obtain ⟨J, C, hC, hb⟩ := S.actual_batch_count D εm ηloss hεm hηloss hβ
  refine ⟨J, C, hC, ?_⟩
  intro τ hτ hτ' hτheight
  obtain ⟨U₀, hw⟩ := unmarked_batch_from_actual_maxima
    1 1 τ ε e κ ηaux I (by norm_num) le_rfl hτ hτ' (by simpa using hτheight)
    hε he he' hκ hκ' hηaux (by norm_num; linarith)
  filter_upwards [hb, eventually_ge_atTop U₀] with U hb hU₀
  refine ⟨hb.1, ?_⟩
  intro b height i hi hb0 hb1 hh hf rows hrows hn hmod hnext hcurrent
  by_cases hne : rows.Nonempty
  · have hδ : 0 ≤ 2*b-1 := by linarith
    have hδ' : 2*b-1 ≤ 5/6 := by linarith
    have hcut := unmarkedCutoff_bounds hδ hδ'
    have hrow : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U^(1 : ℝ) := by
      simpa only [Real.rpow_one, rowNorm] using hrows
    have hc : ∀ u : rows, ∀ j, ∀ Q : Ideal O, idealCoeff (D.naturalFamily u.val j) Q =
        if (fun _ : Label => false) j then
          starRingEnd ℂ (idealCoeff ((D.data j).character ⟨u.val.val, u.val.property.1⟩) Q)
        else idealCoeff ((D.data j).character ⟨u.val.val, u.val.property.1⟩) Q := by
      intro u j Q
      exact D.natural_coefficients u.val j Q
    have hw' := hw U hU₀ 1 le_rfl le_rfl rows hne
      (fun u => D.naturalFamily u.val) hn D.data (fun _ => false) hrow hc b i hi hb0
      (by linarith) hnext hcurrent (by simpa only [Real.rpow_one] using hmod)
      (unmarkedCutoff (2*b-1)) hcut.1 hcut.2
    obtain ⟨B, hBr, hBd, hBrev, hBfam⟩ := hw'
    let B' : UnmarkedBatch Label U b ε (unmarkedCutoff (2*b-1)) (U^τ) (U^(τ/2)) i :=
      { rows := B.rows
        family := B.family
        witness := by
          convert B.witness using 1
          simp only [Real.rpow_one, mul_one]
        row_norm := by simpa only [Real.rpow_one] using B.row_norm
        data := B.data
        reverse := B.reverse
        row_coeff := B.row_coeff }
    rw [← hBr]
    exact hb.2 b ε (U^τ) (U^(τ/2)) height i (by linarith) hδ' hε.le hε' hh hf B' hBd
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity))
      (Real.rpow_nonneg (zero_lt_one.trans hb.1).le _)

#print axioms actual_maxima_bin_count
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.ActualMaximaCount -/

/- BEGIN ORIGINAL Cycle61.Density.SmallHeight; sha256 52087ec99e55d65f42d1c6b9b030cb1995d3dbcfffa806501b120b20a0dc6ee9 -/
section
                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily

theorem actual_small_height_density {Label : Type*} [Fintype Label]
    (S : DensityCountingSetup) (D : FixedUnmarkedDictionary Label)
    (εm ηloss ε e κ ηaux : ℝ)
    (hεm : 0 < εm) (hηloss : 0 < ηloss)
    (hε : 0 < ε) (hε' : ε ≤ 1/1000)
    (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hηaux : 0 ≤ ηaux)
    (hbudget : 288*e+8*κ+2*ηaux ≤ ε/2)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ,
      0 < τ → τ < 1/2 → 4*τ < ηaux → ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → T ≤ U^τ →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ U ∧ rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩) →
      (∀ u ∈ rows, ∀ j, ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤ U) →
        (rows.card : ℝ) ≤ C *
          U^(unmarkedDensity (2*a-1)+156*ε+εm+ηloss+3*e+(J : ℝ)*τ) := by
  let I := bufferCount e
  obtain ⟨J, C, hC, hb⟩ := actual_maxima_bin_count S D εm ηloss ε e κ ηaux I
    hεm hηloss hε hε' he he' hκ hκ' hηaux hbudget hβlo
  let A : ℝ := (1+2*Real.pi+(3*I : ℕ))^J
  let C' : ℝ := (Fintype.card (BufferIndex e) : ℝ)*C*A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨J, C', by dsimp [C', A]; positivity, ?_⟩
  intro τ hτ hτ' hτheight
  have ht : ∀ᶠ U : ℝ in atTop, 2 < U^τ :=
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  filter_upwards [hb τ hτ hτ' hτheight, ht] with U hb ht
  have hUp : 0 < U := zero_lt_one.trans hb.1
  refine ⟨hb.1, ?_⟩
  intro a T ha ha' hT rows hrows hmod
  obtain ⟨select, hp⟩ := actual_buffered_partition D e T (U^τ) a he ht hT hβhi rows ha
    (fun u hu => (hrows u hu).2)
  let parts : BufferIndex e → Finset FreeRow := fun p =>
    (rows.attach.filter (fun u => select u = p)).image Subtype.val
  have hpart (p : BufferIndex e) (u : FreeRow) (hu : u ∈ parts p) :
      ∃ hmem : u ∈ rows, select ⟨u, hmem⟩ = p := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨v.property, (Finset.mem_filter.mp hv).2⟩
  have hsub (p : BufferIndex e) : parts p ⊆ rows := by
    intro u hu
    exact (hpart p u hu).choose
  have hcard (p : BufferIndex e) :
      (parts p).card = (rows.attach.filter (fun u => select u = p)).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have htotal : (rows.card : ℝ) = ∑ p : BufferIndex e, ((parts p).card : ℝ) := by
    have hh := selected_partition_card rows e select
    simp_rw [← hcard] at hh
    exact_mod_cast hh
  let height : ℝ := 2*Real.pi*U^(τ/2)+(3*I : ℕ)*U^τ
  have hh : 0 ≤ height := by dsimp [height]; positivity
  have hhpow := witness_height_power U τ I J hb.1.le hτ.le
  have hone (p : BufferIndex e) : ((parts p).card : ℝ) ≤
      C*A*U^(unmarkedDensity (2*a-1)+156*ε+εm+ηloss+3*e+(J : ℝ)*τ) := by
    by_cases hne : (parts p).Nonempty
    · obtain ⟨u₀, hu₀⟩ := hne
      obtain ⟨hu₀rows, hselect⟩ := hpart p u₀ hu₀
      have hinfo := hp ⟨u₀, hu₀rows⟩
      rw [hselect] at hinfo
      obtain ⟨hi, hn₀, hbcap, hba, hcurr₀, hround₀, hnext₀⟩ := hinfo
      have hb0 : 51/100 < bufferValue e p := by
        have hbe : bufferValue e p > a-e := hba
        linarith
      let hn : ∀ u : parts p, ∀ j, (D.naturalFamily u.val j).residue ≠ 1 := fun u =>
        D.natural_nonprincipal u.val (Classical.choose (hrows u.val (hsub p u.property)).2)
      have hnext : ∀ u : parts p, zeroMaximum (D.naturalFamily u.val) (hn u)
          (3*(p.1.val+1 : ℕ)*U^τ) < bufferValue e p+2*e := by
        intro u
        obtain ⟨hur, hsel⟩ := hpart p u.val u.property
        have hx := hp ⟨u.val, hur⟩
        rw [hsel] at hx
        obtain ⟨_, hnu, _, _, _, _, hx⟩ := hx
        exact hx
      have hcurrent : ∀ u : parts p, bufferValue e p ≤
          zeroMaximum (D.naturalFamily u.val) (hn u) ((3*p.1.val : ℕ)*U^τ) := by
        intro u
        obtain ⟨hur, hsel⟩ := hpart p u.val u.property
        have hx := hp ⟨u.val, hur⟩
        rw [hsel] at hx
        obtain ⟨_, hnu, _, _, hx, _, _⟩ := hx
        exact hx
      have hi' : p.1.val ≤ I := by have := p.1.isLt; dsimp [I]; omega
      have hf : 2*Real.pi*U^(τ/2)+(3*p.1.val : ℕ)*U^τ ≤ height := by
        dsimp [height]
        have hm : ((3*p.1.val : ℕ) : ℝ) ≤ (3*I : ℕ) := by exact_mod_cast Nat.mul_le_mul_left 3 hi'
        linarith [mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hUp.le τ)]
      have hc := hb.2 (bufferValue e p) height p.1.val hi' hb0 hbcap hh hf
        (parts p) (fun u hu => (hrows u (hsub p hu)).1) hn
        (fun u j => hmod u.val (hsub p u.property) j) hnext hcurrent
      have hround := unmarkedDensity_rounding ha' hbcap he.le hba.le
      apply hc.trans
      calc
        _ ≤ C*(A*U^((J : ℝ)*τ))*
            U^(unmarkedDensity (2*bufferValue e p-1)+156*ε+εm+ηloss) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhpow hC) (by positivity)
        _ = C*A*U^(unmarkedDensity (2*bufferValue e p-1)+156*ε+εm+ηloss+(J : ℝ)*τ) := by
          rw [Real.rpow_add hUp
            (unmarkedDensity (2*bufferValue e p-1)+156*ε+εm+ηloss) ((J : ℝ)*τ)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hb.1.le (by linarith)) (by positivity)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  rw [htotal]
  calc
    _ ≤ ∑ _p : BufferIndex e, C*A*
        U^(unmarkedDensity (2*a-1)+156*ε+εm+ηloss+3*e+(J : ℝ)*τ) :=
      Finset.sum_le_sum (fun p _ => hone p)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [C']; ring

#print axioms actual_small_height_density
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.SmallHeight -/

/- BEGIN ORIGINAL Cycle61.Density.UniformFree; sha256 7e3813bcb902b34be9561ef8a50bee60ae52ad9bb45d3cd33e5ce3976bdc8adc -/
section
                                  
                                    

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily

/-- The independent height is chosen after the returned moment degree.
The eventual threshold is common to every boundary and every height. -/
theorem actual_uniform_free_density_normalized {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ U ∧ rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩) →
      (∀ u ∈ rows, ∀ j, ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤ U) →
        (rows.card : ℝ) ≤ C*(1+T)^J*U^(unmarkedDensity (2*a-1)+loss) := by
  by_cases hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta
  · let ε : ℝ := min (loss/1000) (1/1000)
    let e : ℝ := min (ε/2000) (1/2000)
    have hε : 0 < ε := lt_min (by positivity) (by norm_num)
    have hεcap : ε ≤ 1/1000 := min_le_right _ _
    have hεloss : ε ≤ loss/1000 := min_le_left _ _
    have he : 0 < e := lt_min (by positivity) (by norm_num)
    have heε : e ≤ ε/2000 := min_le_left _ _
    have hecap : e ≤ 1/2000 := min_le_right _ _
    obtain ⟨J₀, C₀, hC₀, hsmall⟩ := actual_small_height_density
      canonicalDensityCountingSetup D (loss/10) (loss/10) ε e e e
      (by positivity) (by positivity) hε hεcap he (by linarith)
      he (by linarith) he.le (by linarith) hβlo hβhi
    let τ : ℝ := min (e/8) (min (loss/(10*((J₀ : ℝ)+1))) (1/4))
    have hJ : 0 ≤ (J₀ : ℝ) := Nat.cast_nonneg _
    have hτ : 0 < τ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
    have hτe : τ ≤ e/8 := min_le_left _ _
    have hτcap : τ ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
    have hτloss : τ ≤ loss/(10*((J₀ : ℝ)+1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hτbudget : (J₀ : ℝ)*τ ≤ loss/10 := by
      have h := (le_div_iff₀ (by positivity : 0 < 10*((J₀ : ℝ)+1))).mp hτloss
      nlinarith
    have hbudget : 156*ε+loss/10+loss/10+3*e+(J₀ : ℝ)*τ ≤ loss := by
      linarith
    let J : ℕ := ⌈(1 : ℝ)/τ⌉₊
    have hJτ : 1 ≤ τ*(J : ℝ) := by
      have h := Nat.le_ceil ((1 : ℝ)/τ)
      have hh := (div_le_iff₀ hτ).mp h
      dsimp [J]
      nlinarith
    let C : ℝ := C₀+129
    have hC : 0 < C := by dsimp [C]; linarith
    refine ⟨J, C, hC, ?_⟩
    filter_upwards [hsmall τ hτ (by linarith) (by linarith)] with U hs
    have hUp : 0 < U := zero_lt_one.trans hs.1
    refine ⟨hs.1, ?_⟩
    intro a T ha ha' hT rows hrows hmod
    have hδcap : 2*a-1 ≤ 3/4 := by linarith
    have hρ : 0 ≤ unmarkedDensity (2*a-1)+loss := by
      linarith [unmarkedDensity_ge_two_sevenths hδcap]
    have hweight : 1 ≤ (1+T)^J := one_le_pow₀ (by linarith)
    have hpower : 1 ≤ U^(unmarkedDensity (2*a-1)+loss) := Real.one_le_rpow hs.1.le hρ
    by_cases ht : T ≤ U^τ
    · have hh := hs.2 a T ha ha' ht rows hrows hmod
      apply hh.trans
      have hexp : unmarkedDensity (2*a-1)+156*ε+loss/10+loss/10+3*e+(J₀ : ℝ)*τ ≤
          unmarkedDensity (2*a-1)+loss := by linarith
      calc
        _ ≤ C₀*U^(unmarkedDensity (2*a-1)+loss) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hs.1.le hexp) hC₀
        _ ≤ C*(1+T)^J*U^(unmarkedDensity (2*a-1)+loss) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
          dsimp [C]
          nlinarith
    · have ht' : U^τ ≤ 1+T := by linarith [lt_of_not_ge ht]
      have hheight : U ≤ (1+T)^J := by
        calc
          U = U^(1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ U^(τ*(J : ℝ)) := Real.rpow_le_rpow_of_exponent_le hs.1.le hJτ
          _ = (U^τ)^J := by rw [Real.rpow_mul hUp.le, Real.rpow_natCast]
          _ ≤ (1+T)^J := pow_le_pow_left₀ (Real.rpow_nonneg hUp.le _) ht' J
      have hc := freeRow_count rows U hs.1.le (fun u hu => (hrows u hu).1)
      calc
        (rows.card : ℝ) ≤ 128*U := hc
        _ ≤ 128*(1+T)^J := mul_le_mul_of_nonneg_left hheight (by norm_num)
        _ ≤ C*(1+T)^J := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
        _ ≤ C*(1+T)^J*U^(unmarkedDensity (2*a-1)+loss) :=
          le_mul_of_one_le_right (by positivity) hpower
  · refine ⟨0, 1, by norm_num, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with U hU
    refine ⟨hU, ?_⟩
    intro a T ha ha' hT rows hrows hmod
    have hnone : rows = ∅ := by
      by_contra hn
      have hne := Finset.nonempty_iff_ne_empty.mpr hn
      exact hβlo (beta_lower_of_nonempty_bin D.data a (7/8) T (by linarith)
        rows hne (fun u hu => (hrows u hu).2))
    rw [hnone, Finset.card_empty, Nat.cast_zero]
    positivity

#print axioms actual_uniform_free_density_normalized
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.UniformFree -/

/- BEGIN ORIGINAL Cycle61.Density.FixedDensity; sha256 92d3aeac73e8c884fc87f62e957569a9b53b21a6b9bde2bed4f5cc0717c11e79 -/
section
                                  
                                                                      

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

end
/- END ORIGINAL Cycle61.Density.FixedDensity -/
