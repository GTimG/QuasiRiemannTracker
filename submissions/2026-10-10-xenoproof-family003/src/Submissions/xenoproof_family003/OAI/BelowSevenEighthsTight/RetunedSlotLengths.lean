import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate

/- Reuses the pinned slot construction at an arbitrary positive total length.
   The mesh and range are inputs; the number of slots is chosen afterward. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight
noncomputable section
open scoped BigOperators

theorem exists_retuned_physical_slot_lengths (L dmin dmax mesh R : ℝ)
    (hL : 0 < L) (hdmin : 0 < dmin) (hd : dmin ≤ dmax)
    (hm : 0 < mesh) (hR : 0 < R) :
    ∃ N : ℕ, 0 < N ∧ ∃ ell : Fin N → ℝ, ∃ rmin : ℝ, 0 < rmin ∧
      Function.Injective ell ∧ (∑ j, ell j) = L ∧
      (∀ j, 0 < ell j ∧ dmax*rmin ≤ ell j ∧ ell j ≤ dmin*mesh ∧ ell j ≤ dmin*R) ∧
      (∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ j,
        rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) := by
  have hs : 0 < 6*L := by positivity
  obtain ⟨N, hN, ell, rmin, hr, hi, hsum, hb, _⟩ :=
    OAI.SevenEighths.Parameters.exists_physical_slot_lengths
      dmin dmax (mesh/(6*L)) (R/(6*L)) hdmin hd (by positivity) (by positivity)
  let ell' : Fin N → ℝ := fun j => (6*L)*ell j
  let rmin' := (6*L)*rmin
  have hpos : 0 < rmin' := mul_pos hs hr
  have hbounds (j : Fin N) :
      0 < ell' j ∧ dmax*rmin' ≤ ell' j ∧ ell' j ≤ dmin*mesh ∧ ell' j ≤ dmin*R := by
    have h1 := mul_le_mul_of_nonneg_left (hb j).2.1 hs.le
    have h2 := mul_le_mul_of_nonneg_left (hb j).2.2.1 hs.le
    have h3 := mul_le_mul_of_nonneg_left (hb j).2.2.2 hs.le
    have he2 : (6*L)*(dmin*(mesh/(6*L))) = dmin*mesh := by field_simp
    have he3 : (6*L)*(dmin*(R/(6*L))) = dmin*R := by field_simp
    rw [he2] at h2
    rw [he3] at h3
    refine ⟨mul_pos hs (hb j).1, ?_, h2, h3⟩
    dsimp [ell', rmin']
    nlinarith
  refine ⟨N, hN, ell', rmin', hpos, ?_, ?_, hbounds, ?_⟩
  · intro j k he
    apply hi
    exact (mul_left_cancel₀ hs.ne') he
  · dsimp [ell']
    rw [← Finset.mul_sum, hsum]
    ring
  · intro d hd' hd'' j
    have hd0 : 0 < d := hdmin.trans_le hd'
    refine ⟨(le_div_iff₀ hd0).mpr ?_, (div_le_iff₀ hd0).mpr ?_, (div_le_iff₀ hd0).mpr ?_⟩
    · have hh := mul_le_mul_of_nonneg_left hd'' hpos.le
      nlinarith [(hbounds j).2.1]
    · have hh := mul_le_mul_of_nonneg_right hd' hm.le
      nlinarith [(hbounds j).2.2.1]
    · have hh := mul_le_mul_of_nonneg_right hd' hR.le
      nlinarith [(hbounds j).2.2.2]

theorem exists_rational_physical_slot_lengths (mesh R : ℝ) (hm : 0 < mesh) (hR : 0 < R) :
    ∃ N : ℕ, 0 < N ∧ ∃ ell : Fin N → ℝ, ∃ rmin : ℝ, 0 < rmin ∧
      Function.Injective ell ∧ (∑ j, ell j) = ellRat ∧
      (∀ j, 0 < ell j ∧ (7/8)*rmin ≤ ell j ∧ ell j ≤ mesh/200 ∧ ell j ≤ R/200) ∧
      (∀ d : ℝ, 1/200 ≤ d → d ≤ 7/8 → ∀ j,
        rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) := by
  simpa only [one_div_mul_eq_div] using exists_retuned_physical_slot_lengths
    ellRat (1/200) (7/8) mesh R (by norm_num [ellRat]) (by norm_num) (by norm_num) hm hR

#print axioms exists_retuned_physical_slot_lengths
#print axioms exists_rational_physical_slot_lengths
end
end BelowSevenEighthsTight
