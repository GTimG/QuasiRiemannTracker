/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite genuine native inverse rectangle bank through the upper seam. -/
import Candidate.C092.transport.MediumInversePriceBank
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.NativeBridge
namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Interface.Contract
open QRH.Cycle092.Source
/-- The seam and native arm also have a finite source bank. The last collar
near r=1 needs no inverse marks, by `top_unmarked_quota`. -/
theorem finite_native_source_bank
    {δ ζ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/1000) (hζ : 3*δ ≤ ζ) :
    ∃ J : ℕ, ∃ bank : Fin J → AnchorRect,
      (∀ i, UniformInverseRectSource canonicalFamily (bank i)) ∧
      ∀ r : ℝ, 7/9-3*δ ≤ r → r ≤ 1-3*δ → 0 ≤ inverseQuota r-ζ →
        ∃ i, (bank i).Admissible r (inverseQuota r-ζ) 1 := by
  obtain ⟨J,hbounds,hcover⟩ := finite_anchor_grid
    (by linarith : (7/9 : ℝ)-3*δ ≤ 1-3*δ) hδ
  let R : Fin J → ℝ := fun i => 7/9-3*δ+((i.val : ℝ)+2)*δ
  let bank : Fin J → AnchorRect := fun i => anchorRect (R i) 0 δ
  have hR (i : Fin J) : 7/9-3*δ ≤ R i ∧ R i ≤ 1-δ := by
    have h := hbounds i.val (Finset.mem_range.mpr i.isLt)
    dsimp [R]
    constructor <;> linarith
  refine ⟨J,bank,?_,?_⟩
  · intro i
    apply Inverse.inverseRectSource_native
    constructor <;> dsimp [bank,anchorRect] <;> linarith [(hR i).1,(hR i).2]
  · intro r hr hr1 hz
    obtain ⟨k,hk,hlo,hhi⟩ := hcover r hr hr1
    let i : Fin J := ⟨k,Finset.mem_range.mp hk⟩
    have hquota := near_native_quota hδ.le hδsmall hr
    refine ⟨i,by linarith,?_,hz,?_⟩
    · dsimp [bank,anchorRect,R,i]
      linarith
    · dsimp [bank,anchorRect,R,i]
      linarith


#print axioms finite_native_source_bank
end
end QRH.Cycle092.MediumInversePrice
