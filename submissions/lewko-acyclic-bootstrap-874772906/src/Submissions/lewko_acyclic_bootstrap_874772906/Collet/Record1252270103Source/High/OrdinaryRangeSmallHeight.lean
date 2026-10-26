/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The earlier ordinary-density wrapper is extended to a ≥ 3/4; actual kernel checking is separate. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.OrdinaryRangePartition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.ActualMaximaCount

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.Record1252270103HighOrdinaryRange
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily

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
      ∀ a T : ℝ, 3/4 ≤ a → a ≤ 7/8 → T ≤ U^τ →
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
end SevenEighths.Record1252270103HighOrdinaryRange
end
end OAI
