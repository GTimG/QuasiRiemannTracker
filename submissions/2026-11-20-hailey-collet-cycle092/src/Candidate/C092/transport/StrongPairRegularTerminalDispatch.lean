/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual length cell precedes finite response windows and every live row.
Low is tested at its fixed true threshold; medium windows start there. -/
import Candidate.C092.transport.StrongPairRegularTerminalWindow
import Candidate.C092.transport.SourceInverseP6CloseWindows

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.Cycle092.SourceInverseP6

theorem terminal_interval_windows {lo hi step : ℝ} (hlo : lo ≤ hi) (hs : 0 < step) :
    ∃ J : ℕ,∃ grid : Fin J→ℝ,(∀ j,lo ≤ grid j ∧ grid j ≤ hi) ∧
      ∀ e : ℝ,lo ≤ e → e ≤ hi →∃ j : Fin J,grid j ≤ e ∧ e < grid j+step := by
  let J := ⌊(hi-lo)/step⌋₊+1
  let grid : Fin J→ℝ := fun j=>lo+(j.val:ℝ)*step
  refine ⟨J,grid,?_,?_⟩
  · intro j
    have hj : j.val ≤ ⌊(hi-lo)/step⌋₊ := Nat.le_of_lt_succ j.isLt
    have hf := Nat.floor_le (div_nonneg (sub_nonneg.mpr hlo) hs.le)
    have hnum := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hs.le
    have hbound := (le_div_iff₀ hs).mp hf
    constructor
    · dsimp [grid]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hs.le)
    · dsimp [grid]
      linarith
  · intro e he he'
    let j := ⌊(e-lo)/step⌋₊
    have hj : j < J := Nat.lt_succ_of_le
      (Nat.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right he' lo) hs.le))
    refine ⟨⟨j,hj⟩,?_,?_⟩
    · have h := (le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr he) hs.le))
      dsimp [grid,j]
      linarith
    · have h := (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one ((e-lo)/step))
      dsimp [grid,j]
      push_cast at h
      nlinarith

/-- A SINGLE actual checked cell is fixed before the window size. The low
route uses its exact threshold. Every later medium pair has endpoints in a
finite early table, with eLower<=nuLower on all diagonal windows. Every table
entry has an actual recorded simultaneous inverse/ordinary cutoff. -/
theorem terminal_checked_windows {y : ℝ}
    (hy0 : (369/1000:ℝ) ≤ y) (hy1 : y ≤ (243/625:ℝ)) :
    ∃ c∈sourceCells,(c.lower:ℝ) ≤ y ∧ y ≤ (c.upper:ℝ) ∧
      0 < (c.threshold:ℝ) ∧ (c.threshold:ℝ) ≤ (responseUpper:ℝ) ∧
      (c.threshold:ℝ)*max 0 (lowBracketAt y) < (u-rho:ℚ) ∧
    ∀ step : ℝ,0 < step →
    ∃ Je Jν : ℕ,∃ egrid : Fin Je→ℝ,∃ νgrid : Fin Jν→ℝ,
      (∀ ie,(c.threshold:ℝ) ≤ egrid ie ∧ egrid ie ≤ (responseUpper:ℝ)) ∧
      (∀ iv,0 ≤ νgrid iv ∧ νgrid iv ≤ 3/4) ∧
      (∀ ie iv,∃ p∈c.cutoffs.zipIdx,CutoffGuard c.upper p.1 ∧
        PaidWithBand y (egrid ie) (max (egrid ie) (νgrid iv)) p.1 ∧
        2*y/(H:ℝ) ≤ (p.1.inverse:ℝ) ∧ y/(H:ℝ) ≤ (p.1.ordinary:ℝ) ∧
        y < (H:ℝ)*((p.1.inverse:ℝ)+(p.1.ordinary:ℝ))/2) ∧
      ∀ e ν : ℝ,(c.threshold:ℝ) ≤ e → e ≤ (responseUpper:ℝ) → e ≤ ν → ν ≤ 3/4 →
        ∃ ie iv,egrid ie ≤ e ∧ e < egrid ie+step ∧
          max (egrid ie) (νgrid iv) ≤ ν ∧ ν < max (egrid ie) (νgrid iv)+step ∧
          0 ≤ egrid ie ∧ egrid ie ≤ max (egrid ie) (νgrid iv) ∧
          max (egrid ie) (νgrid iv) ≤ 3/4 := by
  obtain ⟨c,hc,hyl,hyu,hcheck⟩ := sourceCells_cover y hy0 hy1
  have hcheck' := hcheck
  simp only [cellCheck,Bool.and_eq_true] at hcheck'
  have hgeom := of_decide_eq_true hcheck'.1.1
  obtain ⟨_,_,_,_,_,hth0,hth1,_⟩ := hgeom
  have ht0 : 0 < (c.threshold:ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hth0
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
    linarith
  have ht1 : (c.threshold:ℝ) ≤ (responseUpper:ℝ) := by exact_mod_cast hth1
  have hlow := cellCheck_low_positive_part c hcheck hyl hyu ht0.le (le_refl (c.threshold:ℝ))
  refine ⟨c,hc,hyl,hyu,ht0,ht1,hlow,?_⟩
  intro step hs
  obtain ⟨Je,egrid,hegrid,hecover⟩ := terminal_interval_windows ht1 hs
  obtain ⟨Jν,νgrid,hνgrid,hνcover⟩ := finite_response_zero_windows hs
  refine ⟨Je,Jν,egrid,νgrid,hegrid,hνgrid,?_,?_⟩
  · intro ie iv
    exact cellCheck_real_band_response c hcheck hyl hyu (hegrid ie).1 (hegrid ie).2 (le_max_left _ _)
  · intro e ν he he' heν hν
    obtain ⟨ie,hie,hie'⟩ := hecover e he he'
    obtain ⟨_,iv,_,_,hiv,hiv',_⟩ := hνcover ν ν ((ht0.le.trans he).trans heν) le_rfl hν
    refine ⟨ie,iv,hie,hie',max_le (hie.trans heν) hiv,?_,ht0.le.trans (hegrid ie).1,le_max_left _ _,?_⟩
    · exact hiv'.trans_le (by linarith [le_max_right (egrid ie) (νgrid iv)])
    · exact max_le ((hegrid ie).2.trans (by norm_num [responseUpper])) (hνgrid iv).2

#print axioms terminal_checked_windows
end
end QRH.Cycle092.StrongPair
