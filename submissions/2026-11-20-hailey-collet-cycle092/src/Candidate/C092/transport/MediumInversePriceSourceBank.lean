/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine finite inverse source banks, with anchors chosen before the scale
and strictly above every actual length to which they are applied. -/
import Candidate.C092.transport.MediumInversePriceSources
import Candidate.C092.transport.MediumInversePriceNativeBank

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open OAI OAI.SevenEighths Qrh.MarkedAnchor
open Qrh.MarkedAnchor.Interface.Contract
open Qrh.TwoSlot.AnchorContinuum
open QRH.Cycle092.Source

theorem finite_tangent_source_bank
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {δ ζ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/1000) (hζ : 3*δ ≤ ζ) :
    ∃ J : ℕ, ∃ bank : Fin J → AnchorRect,
      (∀ i, UniformInverseRectSource canonicalFamily (bank i)) ∧
      ∀ r : ℝ, 367/500 ≤ r → r < 3/4 → 0 ≤ inverseQuota r-ζ →
        ∃ i, (bank i).Admissible r (inverseQuota r-ζ) 1 := by
  obtain ⟨J,hbounds,hcover⟩ := finite_anchor_grid (by norm_num : (367/500 : ℝ) ≤ 3/4) hδ
  let R : Fin J → ℝ := fun i => 367/500+((i.val : ℝ)+2)*δ
  let bank : Fin J → AnchorRect := fun i =>
    anchorRect (R i) (Contact.exactLine.g0-Contact.exactLine.g1*(R i)) δ
  have hR (i : Fin J) : 1467/2000 ≤ R i ∧ R i ≤ 311/400 := by
    have h := hbounds i.val (Finset.mem_range.mpr i.isLt)
    dsimp [R]
    constructor <;> linarith
  refine ⟨J,bank,?_,?_⟩
  · intro i
    exact genuine_tangent_rect hβ (hR i).1 (hR i).2 hδ
  · intro r hr hr1 hz
    obtain ⟨k,hk,hlo,hhi⟩ := hcover r hr hr1.le
    let i : Fin J := ⟨k,Finset.mem_range.mp hk⟩
    refine ⟨i,?_⟩
    exact (genuine_tangent_anchor hβ (by linarith) hr1 hδ
      (hR i).1 (hR i).2 hlo hhi hζ hz).2

theorem finite_curved_source_bank
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {δ ζ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/1000) (hζ : 3*δ ≤ ζ) :
    ∃ J : ℕ, ∃ bank : Fin J → AnchorRect,
      (∀ i, UniformInverseRectSource canonicalFamily (bank i)) ∧
      ∀ r : ℝ, 3/4 ≤ r → r ≤ 7/9-3*δ → 0 ≤ inverseQuota r-ζ →
        ∃ i, (bank i).Admissible r (inverseQuota r-ζ) 1 := by
  obtain ⟨J,hbounds,hcover⟩ := finite_anchor_grid
    (by linarith : (3/4 : ℝ) ≤ 7/9-3*δ) hδ
  let R : Fin J → ℝ := fun i => 3/4+((i.val : ℝ)+2)*δ
  let bank : Fin J → AnchorRect := fun i => anchorRect (R i) (Curve.Z (7/9) (R i)) δ
  have hR (i : Fin J) : 3/4 ≤ R i ∧ R i < 7/9 := by
    have h := hbounds i.val (Finset.mem_range.mpr i.isLt)
    dsimp [R]
    constructor <;> linarith
  refine ⟨J,bank,?_,?_⟩
  · intro i
    exact genuine_ideal_rect hβ (hR i).1 (hR i).2 hδ
  · intro r hr hr1 hz
    obtain ⟨k,hk,hlo,hhi⟩ := hcover r hr hr1
    let i : Fin J := ⟨k,Finset.mem_range.mp hk⟩
    refine ⟨i,?_⟩
    exact (genuine_curved_anchor hβ hr hδ hlo hhi (hR i).2 hζ hz).2

/-- A positive scalar fee fixes one common open decrement before all actual
row lengths, scales, source arrays, and repetition choices. -/
theorem finite_genuine_inverse_sources
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/1000 ∧ 3*δ ≤ ζ ∧
    ∃ J : ℕ, ∃ bank : Fin J → AnchorRect,
      (∀ i, UniformInverseRectSource canonicalFamily (bank i)) ∧
      ∀ r : ℝ, 367/500 ≤ r → r ≤ 1 →
        inverseQuota r ≤ ζ ∨
          (0 ≤ inverseQuota r-ζ → ∃ i, (bank i).Admissible r (inverseQuota r-ζ) 1) := by
  let δ : ℝ := min (ζ/6) (1/1000)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδsmall : δ ≤ 1/1000 := min_le_right _ _
  have hζδ : 3*δ ≤ ζ := by have h := min_le_left (ζ/6) (1/1000 : ℝ);dsimp [δ];linarith
  obtain ⟨Jt,bt,ht,hct⟩ := finite_tangent_source_bank hβ hδ hδsmall hζδ
  obtain ⟨Jc,bc,hc,hcc⟩ := finite_curved_source_bank hβ hδ hδsmall hζδ
  obtain ⟨Jn,bn,hn,hcn⟩ := finite_native_source_bank hδ hδsmall hζδ
  let bank : Fin (Jt+Jc+Jn) → AnchorRect := Fin.addCases (Fin.addCases bt bc) bn
  refine ⟨δ,hδ,hδsmall,hζδ,Jt+Jc+Jn,bank,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => by simpa [bank] using hn j) i
    exact Fin.addCases (fun k => by simpa [bank] using ht k) (fun k => by simpa [bank] using hc k) j
  · intro r hr hr1
    by_cases htop : 1-3*δ ≤ r
    · exact Or.inl (by have h := top_unmarked_quota hδ.le hδsmall htop hζδ;linarith)
    · right
      intro hz
      by_cases hrt : r < 3/4
      · obtain ⟨i,hi⟩ := hct r hr hrt hz
        exact ⟨Fin.castAdd Jn (Fin.castAdd Jc i),by simpa [bank] using hi⟩
      · by_cases hrc : r ≤ 7/9-3*δ
        · obtain ⟨i,hi⟩ := hcc r (le_of_not_gt hrt) hrc hz
          exact ⟨Fin.castAdd Jn (Fin.natAdd Jt i),by simpa [bank] using hi⟩
        · obtain ⟨i,hi⟩ := hcn r (lt_of_not_ge hrc).le (lt_of_not_ge htop).le hz
          exact ⟨Fin.natAdd (Jt+Jc) i,by simpa [bank] using hi⟩

#print axioms finite_genuine_inverse_sources
end
end QRH.Cycle092.MediumInversePrice
