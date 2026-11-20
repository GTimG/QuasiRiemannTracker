/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Authentic sources and a finite upward cap bank for the P4 ordinary escape. -/
import Candidate.C092.transport.StrongPairOrdinaryNative
import Candidate.C092.transport.StrongPairOrdinarySwap

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.LowActual
open QRH.Cycle092.SourceFurtherWitness
open OAI OAI.SevenEighths

/-- Every actual dominating ordinary cap through .51 is served by a genuine
previous source, native split fourths, or marked/unmarked native collar.
The actual short length need not equal this upper cap. -/
theorem ordinary_frozen_pair_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y m l : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hm0 : y/(H:ℝ) ≤ m) (hm1 : m ≤ 51/100) (hl0 : 0 ≤ l) (hl : l < frozenCapacity n m) :
    PairUniformBox (n/(H:ℝ)) m l := by
  by_cases hmY : m ≤ sourceY
  · exact ordinary_earlier_pair cover hy0 hn0 hn1 hm0 hmY hl0 hl
  · have hypos : 0 ≤ y := source_domain.1.le.trans hy0
    have hyH : y ≤ y/(H:ℝ) := (le_div_iff₀ H_real_bounds.1).2
      (mul_le_of_le_one_right hypos H_real_bounds.2.le)
    have hnH : y ≤ n/(H:ℝ) := hyH.trans (div_le_div_of_nonneg_right hn0 H_real_bounds.1.le)
    have hNlo : (7/20:ℝ) ≤ n/(H:ℝ) := by norm_num [sourceY0] at hy0; linarith
    have hmlo : (7/20:ℝ) ≤ m := by norm_num [sourceY0] at hy0; linarith
    have hN : n/(H:ℝ) < 1/2 := by
      apply (div_lt_iff₀ H_real_bounds.1).2
      norm_num [sourceY,sourceRatio] at hy1 hn1
      norm_num [H,u]
      linarith
    have hmean : l < (1-n/(H:ℝ)-m)/2 := by
      simpa only [frozenCapacity,continuedGain,ite_eq_right hmY,add_zero] using hl
    by_cases hmhalf : m < 1/2
    · exact native_mean_pair_box hβ hNlo hmlo hN hmhalf hl0 hmean
    · have hhalf : (1/2:ℝ) ≤ m := le_of_not_gt hmhalf
      apply native_marked_unmarked_box hβ hN.le (by linarith) hl0
      · linarith
      · linarith

/-- An upward finite cap bank, clipped at the true .51 endpoint. -/
theorem finite_upper_cap_bank {lo hi δ : ℝ} (hlo : lo ≤ hi) (hδ : 0 < δ) :
    ∃ bank : Finset ℝ,(∀ B∈bank,lo ≤ B ∧ B ≤ hi) ∧
      ∀ m : ℝ,lo ≤ m → m ≤ hi → ∃ B∈bank,m ≤ B ∧ B-m < δ := by
  obtain ⟨s,hs,hnet⟩ := finite_left_radius_bank (show -hi ≤ -lo by linarith) hδ
  refine ⟨s.image Neg.neg,?_,?_⟩
  · intro B hB
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨ha,hb⟩ := hs r hr
    exact ⟨by linarith,by linarith⟩
  · intro m hm hm'
    obtain ⟨r,hr,hrm,hgap⟩ := hnet (-m) (by linarith) (by linarith)
    exact ⟨-r,Finset.mem_image.mpr ⟨r,hr,rfl⟩,by linarith,by linarith⟩

/-- True strict quotas for every cap in one early bank. A single early mesh
can now be obtained by pair_finite_bank_mesh before any live row or dyad. -/
theorem ordinary_bank_sources (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y m0 δ : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hm0 : y/(H:ℝ) ≤ m0) (hm01 : m0 ≤ 51/100) (hδ : 0 < δ) :
    ∃ bank : Finset ℝ,∃ decrement : ℝ→ℝ,
      (∀ B∈bank,m0 ≤ B ∧ B ≤ 51/100 ∧ 0 < decrement B ∧ decrement B ≤ δ ∧
        0 < frozenCapacity n B-decrement B ∧
        PairUniformBox (n/(H:ℝ)) B (frozenCapacity n B-decrement B)) ∧
      ∀ m : ℝ,m0 ≤ m → m ≤ 51/100 → ∃ B∈bank,m ≤ B ∧ B-m < δ := by
  obtain ⟨bank,hbank,hnet⟩ := finite_upper_cap_bank hm01 hδ
  let decrement := fun B=>min (frozenCapacity n B/2) δ
  have hcap B (hB : B∈bank) : 0 < frozenCapacity n B := by
    have hh := ordinaryCapacity_positive_extended hy1 hn1 (hbank B hB).2 (by norm_num : (98/100:ℝ) ≤ 1)
    simpa only [ordinaryCapacity,ite_eq_right (show ¬(1:ℝ) ≤ (H:ℝ) by norm_num [H,u]),one_mul] using hh
  refine ⟨bank,decrement,?_,hnet⟩
  intro B hB
  have hd : 0 < decrement B := lt_min (by linarith [hcap B hB]) hδ
  have hd' : decrement B < frozenCapacity n B :=
    (min_le_left _ _).trans_lt (by linarith [hcap B hB])
  have hl : 0 < frozenCapacity n B-decrement B := sub_pos.mpr hd'
  exact ⟨(hbank B hB).1,(hbank B hB).2,hd,min_le_right _ _,hl,
    ordinary_frozen_pair_source hβ cover hy0 hy1 hn0 hn1 (hm0.trans (hbank B hB).1)
      (hbank B hB).2 hl.le (sub_lt_self _ hd)⟩

#print axioms ordinary_frozen_pair_source
#print axioms ordinary_bank_sources
end
end QRH.Cycle092.StrongPair
