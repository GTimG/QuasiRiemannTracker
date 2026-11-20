/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early downward-radius/upward-cap bank of authentic ordinary sources. -/
import Candidate.C092.transport.StrongPairOrdinaryNearSource

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.LowActual
open OAI OAI.SevenEighths

theorem ordinary_near_bank_sources (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y m0 δ : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hm0 : y/(H:ℝ) ≤ m0) (hm01 : m0 ≤ 51/100) (hδ : 0 < δ) :
    ∃ bank : Finset (ℝ×ℝ),∃ decrement : (ℝ×ℝ)→ℝ,
      (∀ p∈bank,(98/100:ℝ) ≤ p.1 ∧ p.1 ≤ (H:ℝ) ∧ m0 ≤ p.2 ∧ p.2 ≤ 51/100 ∧
        0 < decrement p ∧ decrement p ≤ δ ∧ 0 < nearOrdinaryQuota n p.2 p.1-decrement p ∧
        PairUniformBox (n/p.1) (nearOrdinaryCap n p.2 p.1)
          (nearOrdinaryQuota n p.2 p.1-decrement p)) ∧
      ∀ d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
        ∃ p∈bank,p.1 ≤ min d (H:ℝ) ∧ min d (H:ℝ)-p.1 < δ ∧ m ≤ p.2 ∧ p.2-m < δ := by
  obtain ⟨radii,hradii,hrnet⟩ := finite_left_radius_bank
    (show (98/100:ℝ) ≤ (H:ℝ) by norm_num [H,u]) hδ
  obtain ⟨caps,hcaps,hcnet⟩ := finite_upper_cap_bank hm01 hδ
  let bank := radii.product caps
  let decrement := fun p : ℝ×ℝ=>min (nearOrdinaryQuota n p.2 p.1/2) δ
  have hpos (p : ℝ×ℝ) (hp : p∈bank) : 0 < nearOrdinaryQuota n p.2 p.1 := by
    obtain ⟨hr,hc⟩ := Finset.mem_product.mp hp
    exact ordinary_near_positive hy1 hn1 (hcaps p.2 hc).2 (hradii p.1 hr).1 (hradii p.1 hr).2
  refine ⟨bank,decrement,?_,?_⟩
  · intro p hp
    obtain ⟨hr,hc⟩ := Finset.mem_product.mp hp
    obtain ⟨hr0,hr1⟩ := hradii p.1 hr
    obtain ⟨hc0,hc1⟩ := hcaps p.2 hc
    have hdec : 0 < decrement p := lt_min (by linarith [hpos p hp]) hδ
    have hdeclt : decrement p < nearOrdinaryQuota n p.2 p.1 :=
      (min_le_left _ _).trans_lt (by linarith [hpos p hp])
    have hl : 0 < nearOrdinaryQuota n p.2 p.1-decrement p := sub_pos.mpr hdeclt
    exact ⟨hr0,hr1,hc0,hc1,hdec,min_le_right _ _,hl,
      ordinary_near_source hβ cover hy0 hy1 hn0 hn1 (hm0.trans hc0) hc1 hr0 hr1 hl.le
        (sub_lt_self _ hdec)⟩
  · intro d m hd hm hm'
    have hclip : (98/100:ℝ) ≤ min d (H:ℝ) := le_min hd (by norm_num [H,u])
    obtain ⟨r,hr,hrx,hgap⟩ := hrnet (min d (H:ℝ)) hclip (min_le_right _ _)
    obtain ⟨B,hB,hmB,hBgap⟩ := hcnet m hm hm'
    exact ⟨(r,B),Finset.mem_product.mpr ⟨hr,hB⟩,hrx,hgap,hmB,hBgap⟩

#print axioms ordinary_near_bank_sources
end
end QRH.Cycle092.StrongPair
