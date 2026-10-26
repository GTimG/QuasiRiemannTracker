/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact bounded analytic source inlet supplies the unchanged seed and NF
callbacks. No unconditional source theorem is asserted by these adapters. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialTruncatedUniform
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.HeightAnchorCallbacks
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialTruncated
noncomputable section
open OAI.SevenEighths Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record1252270103Low
open QRH.Record1252270103Source.FixedWidthPhysical

def SeedTruncatedInlet : Prop :=
  ∀n low:Source,∀hb:(51/100:ℝ)≤HeckeZeroSupremum.beta,
  ∀hK:6*(2*HeckeZeroSupremum.beta-1)≤seedK,
  ∀hv:SeedSourceValid n low,ParentGood low→P low→
    ∃loss:ℝ,∀ε:ℝ,0<ε→
      ∀b∈activeWidthGrid (crossing n low) n.cap (seedWidthDelta n low hv loss),
      ∃m x:ℝ,0<m ∧ 0<x ∧ ∀mesh ξ:ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
        FixedSubsetTruncatedSupplier n.B n.L n.cap (crossing n low) seedK
          mesh ξ ε b (seedWidthDelta n low hv loss)

def NFTruncatedInlet : Prop :=
  ∀(n low:Source)(high:Option Source),∀hb:(51/100:ℝ)≤HeckeZeroSupremum.beta,
  ∀hK:6*(2*HeckeZeroSupremum.beta-1)≤finalK,
  ∀hv:SourceValid n low high,ParentGood low→∀ha:NFAccounting n,
    P low→(∀h∈high,P h)→
    ∃loss:ℝ,∀ε:ℝ,0<ε→
      ∀b∈activeWidthGrid (crossing n low) n.cap (nfWidthDelta n low high hv ha loss),
      ∃m x:ℝ,0<m ∧ 0<x ∧ ∀mesh ξ:ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
        FixedSubsetTruncatedSupplier n.B n.L n.cap (crossing n low) finalK
          mesh ξ ε b (nfWidthDelta n low high hv ha loss)

theorem seed_physical_of_truncated (h:SeedTruncatedInlet) : HeightAnchor.SeedPhysicalInlet := by
  intro n low hb hK hv hlow hp
  obtain ⟨loss,hfixed⟩:=h n low hb hK hv hlow hp
  have hc:=seed_width_certificate n low hv loss
  refine ⟨loss,?_⟩
  intro ε hε
  apply physical_supplier_of_truncated_widths n.B n.L n.cap (crossing n low) seedK ε
    (seedWidthDelta n low hv loss) (by exact_mod_cast hv.2.1)
    (by exact_mod_cast hv.2.2.1.le) (by exact_mod_cast hv.2.2.2.2.1.le) hε hc.2.1
  · intro b hb
    have hr:=(hc.2.2.2.2.2.1.radius_pos b (activeWidthGrid_bounds _ _ _ b hb)).le
    have he:=upperWidthCell_fixed_on_grid (crossing n low) n.cap _ b hc.2.1 hb
    simpa only [seedWidthCell,he] using hr
  · exact hfixed ε hε

theorem nf_physical_of_truncated (h:NFTruncatedInlet) : HeightAnchor.NFPhysicalInlet := by
  intro n low high hb hK hv hlow ha hp hhigh
  obtain ⟨loss,hfixed⟩:=h n low high hb hK hv hlow ha hp hhigh
  have hc:=nf_width_certificate n low high hv ha loss
  refine ⟨loss,?_⟩
  intro ε hε
  apply physical_supplier_of_truncated_widths n.B n.L n.cap (crossing n low) finalK ε
    (nfWidthDelta n low high hv ha loss) (by exact_mod_cast hv.2.1)
    (by exact_mod_cast hv.2.2.1.le) (by exact_mod_cast hv.2.2.2.2.1.le) hε hc.2.1
  · intro b hb
    have hr:=(hc.2.2.2.2.2.1.radius_pos b (activeWidthGrid_bounds _ _ _ b hb)).le
    have he:=upperWidthCell_fixed_on_grid (crossing n low) n.cap _ b hc.2.1 hb
    simpa only [nfWidthCell,he] using hr
  · exact hfixed ε hε

theorem seed_step_of_truncated (h:SeedTruncatedInlet) : SeedStep :=
  HeightAnchor.seed_step_of_physical (seed_physical_of_truncated h)

theorem nf_step_of_truncated (h:NFTruncatedInlet) : NFStep :=
  HeightAnchor.nf_step_of_physical (nf_physical_of_truncated h)

end
end QRH.Record1252270103Source.InitialTruncated
#print axioms QRH.Record1252270103Source.InitialTruncated.SeedTruncatedInlet
#print axioms QRH.Record1252270103Source.InitialTruncated.NFTruncatedInlet
#print axioms QRH.Record1252270103Source.InitialTruncated.seed_physical_of_truncated
#print axioms QRH.Record1252270103Source.InitialTruncated.nf_physical_of_truncated
#print axioms QRH.Record1252270103Source.InitialTruncated.seed_step_of_truncated
#print axioms QRH.Record1252270103Source.InitialTruncated.nf_step_of_truncated
