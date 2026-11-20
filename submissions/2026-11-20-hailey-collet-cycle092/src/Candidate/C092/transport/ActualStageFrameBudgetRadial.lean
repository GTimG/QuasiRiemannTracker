/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Carry the actual public radial support cap through the analytic producer.
All physical frame fields and the literal grouped physical terms are unchanged. -/
import Candidate.C092.transport.RegularPhysicalClassBudgetAll
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.RegularPhysicalClassBudget
variable {L mesh Z:ℝ}

def withRadialCap (θ:GData L)(cap:ℝ)(hcap:2 ≤ cap) :GData L:={θ with bΦ:=cap,hbΦ:=hcap}

def frameWithRadialCap {θ:GData L}(cap:ℝ)(hcap:2 ≤ cap)(rs:GSrc θ mesh Z) :
    GSrc (withRadialCap θ cap hcap) mesh Z:={rs with}

/-- The producer is allowed its actual radial support cap. Its conclusion
returns to the original physical frame without a radial-support assumption
at the original θ.bΦ and without changing any source, coefficient or keep. -/
theorem part_of_radial_packet (θ:GData L)(cap:ℝ)(hcap:2 ≤ cap)
    (η ω₁ ω₂:Character)(Mmin Mmax ε δ:ℝ)(J:ℕ)(controls:Finset (ℕ×ℕ))(C Cg:ℝ)
    (price:∀U:ℝ,GSrc θ mesh U→ℝ→ℝ)(caps:∀U:ℝ,GSrc θ mesh U→Prop)
    (price':∀U:ℝ,GSrc (withRadialCap θ cap hcap) mesh U→ℝ→ℝ)
    (caps':∀U:ℝ,GSrc (withRadialCap θ cap hcap) mesh U→Prop)
    (hprice:∀U rs w,price' U (frameWithRadialCap cap hcap rs) w=price U rs w)
    (hcaps:∀U rs,caps U rs→caps' U (frameWithRadialCap cap hcap rs))
    (h:PartAt (withRadialCap θ cap hcap) mesh η ω₁ ω₂ Mmin Mmax ε δ J controls C Cg price' caps' Z) :
    PartAt θ mesh η ω₁ ω₂ Mmin Mmax ε δ J controls C Cg price caps Z := by
  refine ⟨h.1,?_⟩
  intro P ξ χ₀ s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hH hB hR hX hlo hhi hc
    Q m hm hl h2 hQ72 hQ t Kc Tsec ξr H w₀ u' hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hpaid
  have hp:price' Z (frameWithRadialCap cap hcap rs) w₀+ε ≤ u':=by
    rw [hprice];exact hpaid
  exact h.2 P ξ χ₀ s (frameWithRadialCap cap hcap rs) hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
    (by exact ⟨hcan.S,hcan.H,hcan.pool,hcan.ν,hcan.Wslot,hcan.P,hcan.R,hcan.d⟩) hV₀ hCR hH hB hR hX hlo hhi (hcaps Z rs hc) Q m hm hl h2 hQ72 hQ
    t Kc Tsec ξr H w₀ u' hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hp

/-- The same cap transport preserves the exhausted native/group fee. -/
theorem part_fee_of_radial_packet (θ:GData L)(cap:ℝ)(hcap:2 ≤ cap)
    (η ω₁ ω₂:Character)(Mmin Mmax ε δ fee:ℝ)(J:ℕ)(controls:Finset (ℕ×ℕ))(C Cg:ℝ)
    (price:∀U:ℝ,GSrc θ mesh U→ℝ→ℝ)(caps:∀U:ℝ,GSrc θ mesh U→Prop)
    (price':∀U:ℝ,GSrc (withRadialCap θ cap hcap) mesh U→ℝ→ℝ)
    (caps':∀U:ℝ,GSrc (withRadialCap θ cap hcap) mesh U→Prop)
    (hprice:∀U rs w,price' U (frameWithRadialCap cap hcap rs) w=price U rs w)
    (hcaps:∀U rs,caps U rs→caps' U (frameWithRadialCap cap hcap rs))
    (h:PartWithFeeAt (withRadialCap θ cap hcap) mesh η ω₁ ω₂ Mmin Mmax ε δ fee J controls C Cg price' caps' Z) :
    PartWithFeeAt θ mesh η ω₁ ω₂ Mmin Mmax ε δ fee J controls C Cg price caps Z := by
  refine ⟨h.1,?_⟩
  intro P ξ χ₀ s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ hcan hV₀ hCR hH hB hR hX hlo hhi hc
    Q m hm hl h2 hQ72 hQ t Kc Tsec ξr H w₀ u' hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hpaid
  have hp:price' Z (frameWithRadialCap cap hcap rs) w₀+ε ≤ u'+fee:=by
    rw [hprice];exact hpaid
  exact h.2 P ξ χ₀ s (frameWithRadialCap cap hcap rs) hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
    (by exact ⟨hcan.S,hcan.H,hcan.pool,hcan.ν,hcan.Wslot,hcan.P,hcan.R,hcan.d⟩) hV₀ hCR hH hB hR hX hlo hhi (hcaps Z rs hc) Q m hm hl h2 hQ72 hQ
    t Kc Tsec ξr H w₀ u' hK hklog hcut hk8 hk2 hT0 hT hξ hH8 hp

#print axioms part_of_radial_packet
#print axioms part_fee_of_radial_packet
end
end QRH.Cycle092.ActualStageFrameBudget
