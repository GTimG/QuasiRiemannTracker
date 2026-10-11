import OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

/-! Exact zero-bin transport through retained finite Euler holes.  This
interface compares zeros, rather than asserting equality of the two
imprimitive L-functions. -/

namespace OAI
noncomputable section
open scoped Classical

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDetectorZeros HeckeFiniteDeletion

/-- A retained Euler puncture has no zeros on the positive half-plane.
Both directions include the point `s = 1`, since the actual row is
nonprincipal. -/
theorem positive_zeros_eq_of_mask (χ ψ : Character)
    (hχ : χ.residue ≠ 1)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = 0 ↔ LFunction ψ s = 0 := by
  rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_eq_zero]
  exact or_iff_left (factors_ne_zero χ.modulus ψ hs)

/-- Inclusion of the positive-real zero sets is enough to compare the
buffered detector maximum; equality of the L-functions is unnecessary. -/
theorem zeroMaximum_le_of_zero_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι → Character) (ψ : κ → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ j, (ψ j).residue ≠ 1) (T : ℝ)
    (hinclude : ∀ i, ∃ j, ∀ s : ℂ, 0 < s.re →
      LFunction (χ i) s = 0 → LFunction (ψ j) s = 0) :
    zeroMaximum χ hχ T ≤ zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51 / 100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i, s, hz, ht, hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j, hj⟩ := hinclude i
    rw [← hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · exact hj s (by rw [hs]; linarith) hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

/-- Every retained finite Euler puncture preserves the complete buffered
bin of a finite row-character family, including its baseline and boundary. -/
theorem zeroMaximum_eq_of_mask {ι : Type*} [Fintype ι]
    (χ ψ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (hψ : ∀ i, (ψ i).residue ≠ 1) (T : ℝ)
    (hmask : ∀ i, ∀ I : Ideal O, idealCoeff (χ i) I =
      if IsCoprime I (χ i).modulus then idealCoeff (ψ i) I else 0) :
    zeroMaximum χ hχ T = zeroMaximum ψ hψ T := by
  apply le_antisymm
  · apply zeroMaximum_le_of_zero_inclusion χ ψ hχ hψ T
    intro i
    exact ⟨i, fun s hs hz => (positive_zeros_eq_of_mask (χ i) (ψ i)
      (hχ i) (hmask i) hs).mp hz⟩
  · apply zeroMaximum_le_of_zero_inclusion ψ χ hψ hχ T
    intro i
    exact ⟨i, fun s hs hz => (positive_zeros_eq_of_mask (χ i) (ψ i)
      (hχ i) (hmask i) hs).mpr hz⟩

end SevenEighths.LocalMoment
end
end OAI
