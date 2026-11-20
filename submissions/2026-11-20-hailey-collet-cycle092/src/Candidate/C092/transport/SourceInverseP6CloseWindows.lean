/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early finite windows for the real measured response and real zero band.
Their lower endpoints preserve e<=nu, so the actual finite P2 certificate
applies before live arrays and rows. -/
import Candidate.C092.transport.SourceInverseP6CloseUnmarked
import Candidate.C092.Intake.QRH.SourceContinuum

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set QRH.Cycle090 QRH.SourceCertificate

theorem finite_response_zero_windows {step : ℝ} (hs : 0<step) :
    ∃ J : ℕ, ∃ grid : Fin J→ℝ,
      (∀ j,0≤grid j ∧ grid j≤3/4) ∧
      ∀ e ν : ℝ,0≤e → e≤ν → ν≤3/4 →
      ∃ ie iv : Fin J,grid ie≤e ∧ e<grid ie+step ∧
        grid iv≤ν ∧ ν<grid iv+step ∧ grid ie≤grid iv := by
  let J := ⌊(3/4:ℝ)/step⌋₊+1
  let grid : Fin J→ℝ := fun j=>(j.val:ℝ)*step
  refine ⟨J,grid,?_,?_⟩
  · intro j
    have hj : j.val≤⌊(3/4:ℝ)/step⌋₊ := Nat.le_of_lt_succ j.isLt
    have hf := Nat.floor_le (div_nonneg (by norm_num : (0:ℝ)≤3/4) hs.le)
    refine ⟨by dsimp [grid]; positivity,?_⟩
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hs.le).trans ((le_div_iff₀ hs).mp hf)
  · intro e ν he heν hν
    let ie := ⌊e/step⌋₊
    let iv := ⌊ν/step⌋₊
    have hν0 : 0≤ν := he.trans heν
    have hie : ie<J := Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (heν.trans hν) hs.le))
    have hiv : iv<J := Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right hν hs.le))
    refine ⟨⟨ie,hie⟩,⟨iv,hiv⟩,?_,?_,?_,?_,?_⟩
    · exact (le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg he hs.le))
    · have h := (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (e/step)); dsimp [grid]; push_cast at h; nlinarith
    · exact (le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hν0 hs.le))
    · have h := (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (ν/step)); dsimp [grid]; push_cast at h; nlinarith
    · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
        (Nat.floor_mono (div_le_div_of_nonneg_right heν hs.le))) hs.le

/-- Every real response/band pair has an actual checked cutoff at an early
finite window, or the checked low route. The grid precedes all late data. -/
theorem finite_checked_response_windows {y step : ℝ}
    (hy0 : (369/1000:ℝ)≤y) (hy1 : y≤(243/625:ℝ)) (hs : 0<step) :
    ∃ J : ℕ,∃ grid : Fin J→ℝ,
      (∀ j,0≤grid j ∧ grid j≤3/4) ∧
      (∀ ie iv : Fin J,grid ie≤(responseUpper:ℝ) → grid ie≤grid iv →
        ∃ c∈sourceCells,(c.lower:ℝ)≤y ∧ y≤(c.upper:ℝ) ∧
          ((grid ie≤(c.threshold:ℝ) ∧ grid ie*max 0 (lowBracketAt y)<(u-rho:ℚ)) ∨
            ((c.threshold:ℝ)≤grid ie ∧ ∃ p∈c.cutoffs.zipIdx,
              CutoffGuard c.upper p.1 ∧ PaidWithBand y (grid ie) (grid iv) p.1 ∧
              2*y/(H:ℝ)≤(p.1.inverse:ℝ) ∧ y/(H:ℝ)≤(p.1.ordinary:ℝ) ∧
              y<(H:ℝ)*((p.1.inverse:ℝ)+(p.1.ordinary:ℝ))/2))) ∧
      ∀ e ν : ℝ,0≤e → e≤ν → ν≤3/4 →
        ∃ ie iv : Fin J,grid ie≤e ∧ e<grid ie+step ∧
          grid iv≤ν ∧ ν<grid iv+step ∧ grid ie≤grid iv := by
  obtain ⟨J,grid,hgrid,hcover⟩ := finite_response_zero_windows hs
  exact ⟨J,grid,hgrid,fun ie iv he hν=>source_scalar_continuum_with_band hy0 hy1
    (hgrid ie).1 he hν,hcover⟩

#print axioms finite_checked_response_windows
end
end QRH.Cycle092.SourceInverseP6
