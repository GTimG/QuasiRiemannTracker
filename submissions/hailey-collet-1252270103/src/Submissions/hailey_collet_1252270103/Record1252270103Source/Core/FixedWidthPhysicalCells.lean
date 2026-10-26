/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical finite width cells and the literal seed/NF physical inlet assembly. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.FixedWidthPhysicalUniform
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.AnchorCallbacks

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FixedWidthPhysical
noncomputable section
open OAI.SevenEighths Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record1252270103Low

def activeWidthGrid (cross cap δ : ℝ) : Finset ℝ :=
  (widthCellGrid cross cap δ).filter (fun b=>cross≤b ∧ b≤cap)

theorem activeWidthGrid_bounds (cross cap δ b : ℝ) (hb : b∈activeWidthGrid cross cap δ) :
    b∈Set.Icc cross cap := (Finset.mem_filter.mp hb).2

theorem upperWidthCell_active_grid (cross cap δ s : ℝ) (hδ : 0<δ)
    (hs : s∈Set.Icc cross cap) :
    upperWidthCell cross cap δ s∈activeWidthGrid cross cap δ ∧
      upperWidthCell cross cap δ s-δ≤s ∧ s≤upperWidthCell cross cap δ s := by
  have hb:=upperWidthCell_bounds cross cap δ s hδ hs.1 hs.2
  refine ⟨Finset.mem_filter.mpr ⟨upperWidthCell_mem_grid cross cap δ s hδ,
    hs.1.trans hb.1,hb.2.1⟩,?_,hb.1⟩
  linarith [hb.2.2.2]

theorem physical_supplier_of_upper_width_cells
    (B lam cap cross K ε δ : ℝ) (hδ : 0<δ)
    (hfixed : ∀b∈activeWidthGrid cross cap δ,∃m x : ℝ,0<m ∧ 0<x ∧
      ∀mesh ξ : ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
        FixedWidthMarkedPhysicalSupplier B lam cap cross K mesh ξ ε b δ) :
    ∃mesh ξ : ℝ,0<mesh ∧ 0<ξ ∧
      Anchor.InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε (upperWidthCell cross cap δ) :=
  physical_supplier_of_fixed_width_ceilings B lam cap cross K ε δ (upperWidthCell cross cap δ)
    (activeWidthGrid cross cap δ) (fun s hs=>upperWidthCell_active_grid cross cap δ s hδ hs) hfixed

/-- Analytic obligation at each fixed seed width. The grid and its rounding
loss precede epsilon, and the positive parameter ceilings precede slot types. -/
def SeedFixedWidthInlet : Prop :=
  ∀n low : Source,∀hb : (51/100:ℝ)≤HeckeZeroSupremum.beta,
  ∀hK : 6*(2*HeckeZeroSupremum.beta-1)≤seedK,
  ∀hv : SeedSourceValid n low,ParentGood low→P low→
    ∃loss : ℝ,∀ε : ℝ,0<ε→
      ∀b∈activeWidthGrid (crossing n low) n.cap (seedWidthDelta n low hv loss),
      ∃m x : ℝ,0<m ∧ 0<x ∧
        ∀mesh ξ : ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
          FixedWidthMarkedPhysicalSupplier n.B n.L n.cap (crossing n low) seedK
            mesh ξ ε b (seedWidthDelta n low hv loss)

/-- Both actual NF accounting profiles are retained through the canonical
width delta. No hypothesis on the new source energy is introduced. -/
def NFFixedWidthInlet : Prop :=
  ∀(n low : Source)(high : Option Source),∀hb : (51/100:ℝ)≤HeckeZeroSupremum.beta,
  ∀hK : 6*(2*HeckeZeroSupremum.beta-1)≤finalK,
  ∀hv : SourceValid n low high,ParentGood low→∀ha : NFAccounting n,
    P low→(∀h∈high,P h)→
    ∃loss : ℝ,∀ε : ℝ,0<ε→
      ∀b∈activeWidthGrid (crossing n low) n.cap (nfWidthDelta n low high hv ha loss),
      ∃m x : ℝ,0<m ∧ 0<x ∧
        ∀mesh ξ : ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
          FixedWidthMarkedPhysicalSupplier n.B n.L n.cap (crossing n low) finalK
            mesh ξ ε b (nfWidthDelta n low high hv ha loss)

theorem seed_physical_of_fixed_width (hfixed : SeedFixedWidthInlet) : Anchor.SeedPhysicalInlet := by
  intro n low hb hK hv hlow hp
  obtain ⟨loss,h⟩:=hfixed n low hb hK hv hlow hp
  refine ⟨loss,?_⟩
  intro ε hε
  exact physical_supplier_of_upper_width_cells n.B n.L n.cap (crossing n low) seedK ε
    (seedWidthDelta n low hv loss) (seed_width_certificate n low hv loss).2.1 (h ε hε)

theorem nf_physical_of_fixed_width (hfixed : NFFixedWidthInlet) : Anchor.NFPhysicalInlet := by
  intro n low high hb hK hv hlow ha hp hhigh
  obtain ⟨loss,h⟩:=hfixed n low high hb hK hv hlow ha hp hhigh
  refine ⟨loss,?_⟩
  intro ε hε
  exact physical_supplier_of_upper_width_cells n.B n.L n.cap (crossing n low) finalK ε
    (nfWidthDelta n low high hv ha loss) (nf_width_certificate n low high hv ha loss).2.1 (h ε hε)

end
end QRH.Record1252270103Source.FixedWidthPhysical
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.activeWidthGrid
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.activeWidthGrid_bounds
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.upperWidthCell_active_grid
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.physical_supplier_of_upper_width_cells
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.SeedFixedWidthInlet
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.NFFixedWidthInlet
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.seed_physical_of_fixed_width
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.nf_physical_of_fixed_width
