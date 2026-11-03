/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighSlotLengths.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

theorem exists_distinct_slot_lengths_with_mass
    (mass cap : ℝ) (hmass : 0 < mass) (hcap : 0 < cap) :
    ∃ N : ℕ, 0 < N ∧ ∃ ell : Fin N → ℝ,
      Function.Injective ell ∧
      (∀ j, 0 < ell j ∧ ell j < cap) ∧
      (∑ j, ell j) = mass := by
  obtain ⟨N, hN, ell, hinj, hell, hsum⟩ :=
    exists_distinct_slot_lengths (cap / (6 * mass))
      (div_pos hcap (by positivity))
  let scaled : Fin N → ℝ := fun j => 6 * mass * ell j
  refine ⟨N, hN, scaled, ?_, ?_, ?_⟩
  · intro j k h
    apply hinj
    have hmk : 6 * mass * ell j = 6 * mass * ell k := h
    nlinarith
  · intro j
    constructor
    · exact mul_pos (by positivity) (hell j).1
    · have hj := (hell j).2
      dsimp [scaled]
      have hlt := (lt_div_iff₀ (show 0 < 6 * mass by positivity)).mp hj
      nlinarith
  · dsimp [scaled]
    rw [← Finset.mul_sum, hsum]
    ring

theorem exists_physical_slot_lengths_with_mass
    (mass dmin dmax mesh R : ℝ)
    (hmass : 0 < mass) (hdmin : 0 < dmin)
    (hd : dmin ≤ dmax) (hm : 0 < mesh) (hR : 0 < R) :
    ∃ N : ℕ, 0 < N ∧ ∃ ell : Fin N → ℝ, ∃ rmin : ℝ,
      0 < rmin ∧ Function.Injective ell ∧ (∑ j, ell j) = mass ∧
      (∀ j, 0 < ell j ∧ dmax * rmin ≤ ell j ∧
        ell j ≤ dmin * mesh ∧ ell j ≤ dmin * R) ∧
      (∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ j,
        rmin ≤ ell j / d ∧ ell j / d ≤ mesh ∧ ell j / d ≤ R) := by
  obtain ⟨N, hN, ell, hinj, hell, hsum⟩ :=
    exists_distinct_slot_lengths_with_mass mass (dmin * min mesh R)
      hmass (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0 < dmax := hdmin.trans_le hd
  let rmin := ell j / (2 * dmax)
  have hr : 0 < rmin := div_pos (hell j).1 (by positivity)
  have hlo (k : Fin N) : dmax * rmin ≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax * rmin = ell j / 2 := by
      dsimp [rmin]
      field_simp
    rw [hiden]
    linarith [(hell j).1]
  have hup (k : Fin N) : ell k ≤ dmin * mesh ∧ ell k ≤ dmin * R := by
    constructor
    · exact (hell k).2.le.trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (hell k).2.le.trans
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N, hN, ell, rmin, hr, hinj, hsum,
    fun k => ⟨(hell k).1, hlo k, (hup k).1, (hup k).2⟩, ?_⟩
  intro d hd' hd'' k
  have hd0 : 0 < d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,
    (div_le_iff₀ hd0).mpr ?_,
    (div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin * d ≤ dmax * rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end SevenEighths.Parameters

end

end OAI
