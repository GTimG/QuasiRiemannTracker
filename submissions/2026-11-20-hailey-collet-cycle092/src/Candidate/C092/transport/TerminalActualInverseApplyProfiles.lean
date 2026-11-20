/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal unit-profile gates for the actual P6 short column and its height. -/
import Candidate.C092.transport.TerminalActualInverseApplySmall
import Candidate.C092.transport.TerminalProfileUniformSup
set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualInverseApply
noncomputable section
open scoped Classical SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeInverseAmplification HeckeDetectorDyadicProfiles
open CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.TerminalProfileUniform

theorem twist_zero_norm {W : ℝ→ℂ} {A B : ℝ} (hA : 0<A)
    (hs : Function.support W ⊆ Icc A B) (freq x : ℝ) :
    ‖twistProfile W 0 freq x‖ = ‖W x‖ := by
  by_cases hw : W x=0
  · simp [twistProfile,hw]
  have hx : 0 < x := hA.trans_le (hs hw).1
  rw [twistProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [HeckeDyadic.shift]

/-- A single amplitude bound precedes the unit-profile bank, all Fourier
heights, the opened/unopened choice, and every actual shortened scale. -/
theorem actual_unit_short_gates (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V) :
    ∃ Bshort : ℝ,1 ≤ Bshort ∧
    ∀ (S : Finset (ℕ×ℕ)),(0,0)∈S → ∀ C : ℝ,1≤C →
    ∀ (p : Profiles (1/4) (9/4)) (orders : Finset ℕ) (extra : Finset (ℕ×ℕ)),
    UnitGates V (-1) 2 orders extra (unitPair S C p) →
    ∀ (j : Fin 2) (opened : Bool) (Dstar D freq a ez : ℝ),
      0<Dstar → 0≤D → D≤4*Dstar → 51/100≤a → a≤1 → 0<ez → ez<1/1000 →
    let Wi := TerminalActualRow.shortProfile V ((unitPair S C p).profile j) opened Dstar D;
      Function.support Wi ⊆ Icc (1/4:ℝ) (9/4) ∧ ContDiff ℝ ∞ Wi ∧
      Function.support (twistProfile Wi 0 freq) ⊆ Iic (9/4:ℝ) ∧
      (∀ x,‖twistProfile Wi 0 freq x‖≤Bshort) ∧
      ∀ k∈orders,∀ σ∈Icc (1-a-6*ez) 2,∀ t : ℝ,
        (1+|t|)^k*‖mellin Wi ((σ:ℂ)+t*Complex.I)‖ ≤ 1 := by
  obtain ⟨Bshort,hB,hbound⟩ := native_short_unit_sup V hV.continuous
  refine ⟨Bshort,hB,?_⟩
  intro S hS C hC p orders extra hg j opened Dstar D freq a ez hDs hD hDc ha ha' he he'
  dsimp only
  obtain ⟨hs,hsm,hm⟩ := native_short_unit_gates V hV orders extra (unitPair S C p) hg
    j opened Dstar D hDs hD hDc
  refine ⟨hs,hsm,twist_profile_support hs,?_,?_⟩
  · intro x
    rw [twist_zero_norm (by norm_num : (0:ℝ)<1/4) hs]
    exact hbound S hS C hC (p.profile j) (p.support j) opened Dstar D hDs hD hDc x
  · intro k hk σ hσ t
    exact hm k hk σ (actual_zero_band_strip ha ha' he he' hσ) t

#print axioms twist_zero_norm
#print axioms actual_unit_short_gates
end
end QRH.Cycle092.TerminalActualInverseApply
