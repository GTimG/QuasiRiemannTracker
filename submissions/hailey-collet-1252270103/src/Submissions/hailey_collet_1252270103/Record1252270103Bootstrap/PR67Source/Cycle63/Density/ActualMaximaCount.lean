import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Density.ActualBatchCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Density.BufferedPartition
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Density.Rounding
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
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
    (S : DensityCountingSetup)
    (εm ηloss ε e κ ηaux : ℝ) (I : ℕ)
    (hεm : 0 < εm) (hηloss : 0 < ηloss)
    (hε : 0 < ε) (hε' : ε ≤ 1/1000)
    (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hηaux : 0 ≤ ηaux)
    (hbudget : 288*e+8*κ+2*ηaux ≤ ε/2)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∀ D : FixedUnmarkedDictionary Label, ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ,
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
  obtain ⟨J, hJ⟩ := S.actual_batch_count (Label := Label) εm ηloss hεm hηloss hβ
  refine ⟨J, fun D => ?_⟩
  obtain ⟨C, hC, hb⟩ := hJ D
  refine ⟨C, hC, ?_⟩
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

end SevenEighths.LocalMoment
end
end OAI

end Record1252270103Bootstrap.PR67
