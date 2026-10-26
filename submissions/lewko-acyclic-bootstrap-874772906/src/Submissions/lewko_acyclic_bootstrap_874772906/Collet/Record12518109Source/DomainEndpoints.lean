/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.DomainCompletion
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
theorem first_cap_admission_endpoints {f : SourceFace}
    {K rlo rhi plo phi mmax P Q m₁ m₂ : ℝ}
    (hK : 0 ≤ K) (hL : 0 < f.lam)
    (hu : 0 ≤ f.plainHi)
    (hQlo : rlo≤Q) (hQhi : Q≤rhi) (hPlo : plo≤P) (hPhi : P≤phi)
    (hP : m₁+m₂ = P) (hm₁ : m₁ ≤ mmax) (hm₂ : m₂ ≤ mmax)
    (hBLo : 0 ≤ f.B-f.lam*f.slotLo)
    (hBHi : 0 ≤ f.B-f.lam*f.slotHi)
    (hNLo : 0 ≤ 1-K*f.slotLo)
    (hCoeff : 1-f.plainLo-K*f.B/f.lam ≤ 0)
    (hslotLo : phi ≤ (f.B-f.lam*f.slotLo)*rlo)
    (hslotHi : (f.B-f.lam*f.slotHi)*rhi ≤ plo)
    (hplain : mmax ≤ f.plainHi*rlo)
    (hnaturalSlot : phi ≤ (1-K*f.slotLo)*rlo)
    (hnaturalPlain : mmax ≤
      (1-f.plainLo-K*f.B/f.lam)*rhi+(K/f.lam)*plo) :
    f.slotLo*Q ≤ firstSlotCap f P Q ∧
      firstSlotCap f P Q ≤ f.slotHi*Q ∧
      DownwardCaps f K m₁ m₂ (firstSlotCap f P Q) Q := by
  have hL0 := ne_of_gt hL
  have hz : f.lam*firstSlotCap f P Q = f.B*Q-P := by
    dsimp [firstSlotCap]
    field_simp
  have hlo : f.slotLo*Q ≤ firstSlotCap f P Q := by
    have := mul_le_mul_of_nonneg_left hQlo hBLo
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith only [hz,hslotLo,this,hPhi]
  have hhi : firstSlotCap f P Q ≤ f.slotHi*Q := by
    have := mul_le_mul_of_nonneg_left hQhi hBHi
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith only [hz,hslotHi,this,hPlo]
  refine ⟨hlo,hhi,⟨hK,hL.le,?_,?_,hhi,?_,?_,?_⟩⟩
  · exact hm₁.trans (hplain.trans (mul_le_mul_of_nonneg_left hQlo hu))
  · exact hm₂.trans (hplain.trans (mul_le_mul_of_nonneg_left hQlo hu))
  · linarith only [hz,hP]
  · have := mul_le_mul_of_nonneg_left hQlo hNLo
    nlinarith only [hP,hnaturalSlot,this,hPhi]
  · have hc := mul_le_mul_of_nonpos_left hQhi hCoeff
    have hkp : (K/f.lam)*plo ≤ (K/f.lam)*P :=
      mul_le_mul_of_nonneg_left hPlo (div_nonneg hK hL.le)
    have hm : max m₁ m₂ ≤ mmax := max_le hm₁ hm₂
    have hid : Q-(max m₁ m₂+f.plainLo*Q+K*firstSlotCap f P Q) =
        (1-f.plainLo-K*f.B/f.lam)*Q+(K/f.lam)*P-max m₁ m₂ := by
      dsimp [firstSlotCap]
      field_simp
      <;> ring
    linarith only [hc,hkp,hm,hnaturalPlain,hid]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.first_cap_admission_endpoints
