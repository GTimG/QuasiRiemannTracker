/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Callable graph closures. The sole pending analytic inlet is the literal marked
first physical norm on canonical initial data, at a fixed certified width grid. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.HeightAnchorUniform
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialCallbacks
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low.HeightAnchor
noncomputable section
open OAI.SevenEighths Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record1252270103Source QRH.Record1252270103Restoration

def SeedPhysicalInlet : Prop :=
  ∀n low : Source,∀hb : (51/100:ℝ)≤HeckeZeroSupremum.beta,
  ∀hK : 6*(2*HeckeZeroSupremum.beta-1)≤seedK,
  ∀hv : SeedSourceValid n low,ParentGood low → P low →
    ∃loss : ℝ,∀ε : ℝ,0<ε → ∃mesh ξ : ℝ,0<mesh ∧ 0<ξ ∧
      InitialMarkedPhysicalSupplier n.B n.L n.cap (crossing n low) seedK mesh ξ ε
        (seedWidthCell n low hv loss)

def NFPhysicalInlet : Prop :=
  ∀(n low : Source)(high : Option Source),∀hb : (51/100:ℝ)≤HeckeZeroSupremum.beta,
  ∀hK : 6*(2*HeckeZeroSupremum.beta-1)≤finalK,
  ∀hv : SourceValid n low high,ParentGood low → ∀ha : NFAccounting n,
    P low → (∀h∈high,P h) →
    ∃loss : ℝ,∀ε : ℝ,0<ε → ∃mesh ξ : ℝ,0<mesh ∧ 0<ξ ∧
      InitialMarkedPhysicalSupplier n.B n.L n.cap (crossing n low) finalK mesh ξ ε
        (nfWidthCell n low high hv ha loss)

theorem seed_step_of_physical (hphysical : SeedPhysicalInlet) : SeedStep := by
  intro n low hb hK hv hlow hp
  obtain ⟨loss,hphys⟩:=hphysical n low hb hK hv hlow hp
  have hfields:=hv
  obtain ⟨hBn,hBn1,hLn,_,_,_,_,hL,_,_,hcrosslow,_⟩:=hfields
  have hn0 : 0≤(n.B:ℝ):=by exact_mod_cast hBn.le
  have hn1 : (n.B:ℝ)≤1:=by exact_mod_cast hBn1
  have hLn' : 1≤(n.L:ℝ):=by exact_mod_cast hLn.le
  have hL' : (n.L:ℝ)≤(low.L:ℝ):=by exact_mod_cast hL.le
  have hcross : (crossing n low:ℝ)≤(low.cap:ℝ):=by exact_mod_cast hcrosslow
  have hbudget : (n.B:ℝ)-(low.B:ℝ)+((low.L:ℝ)-(n.L:ℝ))*(crossing n low:ℝ)≤0:=
    (crossing_real_identity n low hL).le
  have hcells : ReferenceWidthCells (crossing n low) n.cap seedK (seedWidthCell n low hv loss):=
    (seed_width_certificate n low hv loss).2.2.2.2.2.1.reference
  change GlobalSource n.B n.L n.cap
  apply globalSource_of_squarefree n.B n.L n.cap hn0 (by linarith)
  apply uniform_squarefree_source_step n.B n.L n.cap low.B low.L low.cap (crossing n low)
    seedK (seedK/6) (seedWidthCell n low hv loss) hn0 hn1
    (by exact_mod_cast hlow.2.1) hLn' hL' hcross hbudget
  · norm_num [seedK]
  · norm_num [seedK]
  · linarith only [hK]
  · ring_nf
    exact le_rfl
  · exact hb
  · exact hcells
  · exact hp
  · exact hphys

theorem nf_step_of_physical (hphysical : NFPhysicalInlet) : NFStep := by
  intro n low high hb hK hv hlow ha hp hhigh
  obtain ⟨loss,hphys⟩:=hphysical n low high hb hK hv hlow ha hp hhigh
  have hfields:=hv
  obtain ⟨hBn,hBn1,hLn,_,_,_,_,hL,_,_,hcrosslow,_⟩:=hfields
  have hn0 : 0≤(n.B:ℝ):=by exact_mod_cast hBn.le
  have hn1 : (n.B:ℝ)≤1:=by exact_mod_cast hBn1
  have hLn' : 1≤(n.L:ℝ):=by exact_mod_cast hLn.le
  have hL' : (n.L:ℝ)≤(low.L:ℝ):=by exact_mod_cast hL.le
  have hcross : (crossing n low:ℝ)≤(low.cap:ℝ):=by exact_mod_cast hcrosslow
  have hbudget : (n.B:ℝ)-(low.B:ℝ)+((low.L:ℝ)-(n.L:ℝ))*(crossing n low:ℝ)≤0:=
    (crossing_real_identity n low hL).le
  have hcells : ReferenceWidthCells (crossing n low) n.cap finalK (nfWidthCell n low high hv ha loss):=
    (nf_width_certificate n low high hv ha loss).2.2.2.2.2.1.reference
  change GlobalSource n.B n.L n.cap
  apply globalSource_of_squarefree n.B n.L n.cap hn0 (by linarith)
  apply uniform_squarefree_source_step n.B n.L n.cap low.B low.L low.cap (crossing n low)
    finalK (finalK/6) (nfWidthCell n low high hv ha loss) hn0 hn1
    (by exact_mod_cast hlow.2.1) hLn' hL' hcross hbudget
  · norm_num [finalK]
  · norm_num [finalK]
  · linarith only [hK]
  · ring_nf
    exact le_rfl
  · exact hb
  · exact hcells
  · exact hp
  · exact hphys

end
end QRH.Record1252270103Low.HeightAnchor
#print axioms QRH.Record1252270103Low.HeightAnchor.seed_step_of_physical
#print axioms QRH.Record1252270103Low.HeightAnchor.nf_step_of_physical
