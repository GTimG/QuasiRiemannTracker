/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original plain/opened native short-profile gates at the same rows. -/
import Candidate.C092.transport.TerminalProfileUniformPair
import Candidate.C092.transport.TerminalActualRowProfiles
set_option autoImplicit false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap ContDiff
open Set OAI OAI.SevenEighths CenteredMomentFiniteProfileExceptional HeckeDetectorDyadicProfiles

theorem actualShort_eq_native (V W : ℝ→ℂ) (opened : Bool) (Dstar D : ℝ) :
    actualShort V W opened (D/Dstar) = TerminalActualRow.shortProfile V W opened Dstar D := by
  simp only [actualShort,TerminalActualRow.shortProfile,inverseProfile_eq_ratio]

/-- One finite bank verifies precisely the native all-row Mellin gates.
The zero-band and detector height are unchanged, and no bound depends on rows. -/
theorem native_short_unit_gates {a b lo hi : ℝ} (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (orders : Finset ℕ) (extra : Finset (ℕ×ℕ)) (p : Profiles a b)
    (hg : UnitGates V lo hi orders extra p)
    (i : Fin 2) (opened : Bool) (Dstar D : ℝ)
    (hDs : 0 < Dstar) (hD : 0 ≤ D) (hDc : D ≤ 4*Dstar) :
    Function.support (TerminalActualRow.shortProfile V (p.profile i) opened Dstar D) ⊆ Icc a b ∧
    ContDiff ℝ ∞ (TerminalActualRow.shortProfile V (p.profile i) opened Dstar D) ∧
    ∀ j ∈ orders, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (TerminalActualRow.shortProfile V (p.profile i) opened Dstar D)
        ((σ:ℂ)+t*Complex.I)‖ ≤ 1 := by
  rw [←actualShort_eq_native]
  have hr : D/Dstar ∈ Icc (0:ℝ) 4 := ⟨div_nonneg hD hDs.le,(div_le_iff₀ hDs).mpr hDc⟩
  cases opened with
  | false =>
    exact ⟨p.support i,(p.profile i).smooth ⊤,fun j hj σ hσ t => (hg.2 i j hj σ hσ t).1⟩
  | true =>
    refine ⟨(ratioProfile_support V (p.profile i) (D/Dstar)).trans (p.support i),?_,?_⟩
    · change ContDiff ℝ ∞ (ratioProfile V (p.profile i) (D/Dstar))
      unfold ratioProfile
      exact (hV.comp (contDiff_const.mul contDiff_id)).mul ((p.profile i).smooth ⊤)
    · intro j hj σ hσ t
      exact (hg.2 i j hj σ hσ t).2 (D/Dstar) hr

/-- The actual zero band with sigma_i=0 lies in the single early strip. -/
theorem actual_zero_band_strip {a ez : ℝ} (ha : 51/100 ≤ a) (ha' : a ≤ 1)
    (he : 0 < ez) (he' : ez < 1/1000) : Icc (1-a-6*ez) 2 ⊆ Icc (-1:ℝ) 2 := by
  intro σ hσ
  constructor <;> linarith [hσ.1,hσ.2]

/-- Every individual early long-source control is paid by the unit bank. -/
theorem unit_long_source_cost {a b lo hi : ℝ} (V : ℝ→ℂ) (orders : Finset ℕ)
    (extra : Finset (ℕ×ℕ)) (p : Profiles a b) (hg : UnitGates V lo hi orders extra p)
    (i : Fin 2) (T : Finset (ℕ×ℕ)) (hT : T ⊆ extra)
    (Cl diag : ℝ) (hCl : 0 ≤ Cl) (hd : 0 ≤ diag) :
    Cl*diag*(sourceControl T (p.profile i))^4+1 ≤ Cl*diag+1 := by
  have hctl : sourceControl T (p.profile i) ≤ 1 :=
    (Seminorm.le_def.mp (Finset.sup_mono hT) (p.profile i)).trans (hg.1 i)
  have hp : (sourceControl T (p.profile i))^4 ≤ 1 := by
    simpa using pow_le_pow_left₀ (sourceControl_nonneg _ _) hctl 4
  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg hCl hd)]

#print axioms native_short_unit_gates
#print axioms actual_zero_band_strip
#print axioms unit_long_source_cost
end
end QRH.Cycle092.TerminalProfileUniform
