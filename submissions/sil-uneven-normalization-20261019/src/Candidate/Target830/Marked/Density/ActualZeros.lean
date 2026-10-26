import Candidate.Cycle63.Density.BufferedPartition
import Candidate.Cycle63.Density.SmallHeight
import Candidate.Cycle63.Density.UniformFree
import Candidate.Cycle63.Density.CountingSetup
import Candidate.Cycle63.Density.FixedDensity
import Candidate.Cycle63.Density.ActualZeros

/- Original module: Candidate.Target830.Marked.Density.BufferedPartition. -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace OAI.SevenEighths.Target830MarkedDensity
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalRowSource HeckeFiniteDeletion

theorem actual_buffered_partition {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (e U T a : ℝ)
    (he : 0 < e) (hT : 2 < T)
    (hheight : U ≤ T)
    (hβ : HeckeZeroSupremum.beta ≤ 7/8)
    (rows : Finset FreeRow)
    (ha : 81/100 ≤ a)
    (hrows : ∀ u ∈ rows, rawZeroBin D.data a (7/8) U ⟨u.val, u.property.1⟩) :
    ∃ select : rows → BufferIndex e,
      ∀ u : rows, 1 ≤ (select u).1.val ∧
        let b := bufferValue e (select u)
        ∃ hn : ∀ j, (D.naturalFamily u.val j).residue ≠ 1,
          b ≤ 7/8 ∧ a-e < b ∧
          b ≤ zeroMaximum (D.naturalFamily u.val) hn ((3*(select u).1.val : ℕ)*T) ∧
          zeroMaximum (D.naturalFamily u.val) hn ((3*(select u).1.val : ℕ)*T) < b+e ∧
          zeroMaximum (D.naturalFamily u.val) hn (3*((select u).1.val+1 : ℕ)*T) < b+2*e := by
  have one (u : rows) : ∃ p : BufferIndex e, 1 ≤ p.1.val ∧
      let b := bufferValue e p
      ∃ hn : ∀ j, (D.naturalFamily u.val j).residue ≠ 1,
        b ≤ 7/8 ∧ a-e < b ∧
        b ≤ zeroMaximum (D.naturalFamily u.val) hn ((3*p.1.val : ℕ)*T) ∧
        zeroMaximum (D.naturalFamily u.val) hn ((3*p.1.val : ℕ)*T) < b+e ∧
        zeroMaximum (D.naturalFamily u.val) hn (3*(p.1.val+1 : ℕ)*T) < b+2*e := by
    obtain ⟨hraw, hlo, hhi⟩ := hrows u.val u.property
    let hn := D.natural_nonprincipal u.val hraw
    have hbn : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta :=
      beta_lower_of_nonempty_bin D.data a (7/8) U (by linarith) rows ⟨u.val, u.property⟩ hrows
    obtain ⟨i, k, hi, hi', hone, hcurrent, hround, hnext, hrest⟩ :=
      exists_actual_buffered_bin (D.naturalFamily u.val) hn T e hT he
        (bufferCount e) (bufferCount_spec e he).1 (bufferCount_spec e he).2
    have hki : k ≤ bufferGridCount e := by
      have hk : (k : ℝ) ≤ 1/e := (le_div_iff₀ he).mpr (by nlinarith)
      exact_mod_cast hk.trans (Nat.le_ceil (1/e))
    let p : BufferIndex e := (⟨i, by omega⟩, ⟨k, by omega⟩)
    refine ⟨p, hi, hn, ?_, ?_, ?_, ?_, ?_⟩
    · exact hcurrent.trans ((zeroMaximum_le_beta _ hn hbn _).trans hβ)
    · have hlarge : U ≤ (3*i : ℕ)*T := by
        have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
        push_cast
        nlinarith
      have hz := zeroMaximum_mono (D.naturalFamily u.val) hn hlarge
      rw [D.natural_maximum u.val hraw U] at hz
      push_cast at hz
      dsimp [bufferValue, p]
      linarith
    · simpa only [bufferValue, p, Nat.cast_mul, Nat.cast_ofNat] using hcurrent
    · simpa only [bufferValue, p, Nat.cast_mul, Nat.cast_ofNat] using hround
    · simpa only [bufferValue, p] using hnext
  choose select hselect using one
  exact ⟨select, hselect⟩


end OAI.SevenEighths.Target830MarkedDensity
#print axioms OAI.SevenEighths.Target830MarkedDensity.actual_buffered_partition
end

/- Original module: Candidate.Target830.Marked.Density.SmallHeight. -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace OAI.SevenEighths.Target830MarkedDensity
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalRowSource HeckeFiniteDeletion

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
      ∀ a T : ℝ, 81/100 ≤ a → a ≤ 7/8 → T ≤ U^τ →
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


end OAI.SevenEighths.Target830MarkedDensity
#print axioms OAI.SevenEighths.Target830MarkedDensity.actual_small_height_density
end

/- Original module: Candidate.Target830.Marked.Density.UniformFree. -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace OAI.SevenEighths.Target830MarkedDensity
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalRowSource HeckeFiniteDeletion

theorem actual_uniform_free_density_normalized {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ a T : ℝ, 81/100 ≤ a → a ≤ 7/8 → 0 ≤ T →
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


end OAI.SevenEighths.Target830MarkedDensity
#print axioms OAI.SevenEighths.Target830MarkedDensity.actual_uniform_free_density_normalized
end

/- Original module: Candidate.Target830.Marked.Density.FixedDensity. -/
section
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
end

/- Original module: Candidate.Target830.Marked.Density.ActualZeros. -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace OAI.SevenEighths.Target830MarkedDensity
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalRowSource HeckeFiniteDeletion

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


end OAI.SevenEighths.Target830MarkedDensity
#print axioms OAI.SevenEighths.Target830MarkedDensity.actual_zero_regular_bin
#print axioms OAI.SevenEighths.Target830MarkedDensity.oriented_zero_core_predicate
#print axioms OAI.SevenEighths.Target830MarkedDensity.fixed_dictionary_eventual_with_exceptions
end
