/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Callable graph closures. The sole pending analytic inlet is the literal marked
first physical norm on canonical initial data, at a fixed certified width grid. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyUniform
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialAssemblyMargins
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.UniformSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI.SevenEighths Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record1252270103Source QRH.Record1252270103Restoration

def nfWidthMargin (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) (loss : ℝ) : ℝ :=
  (nf_finite_width_cells n low high hv ha loss).choose
def nfWidthDelta (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) (loss : ℝ) : ℝ :=
  (nf_finite_width_cells n low high hv ha loss).choose_spec.choose
def nfWidthCell (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) (loss : ℝ) : ℝ→ℝ :=
  upperWidthCell (crossing n low) n.cap (nfWidthDelta n low high hv ha loss)

def seedWidthMargin (n low : Source) (hv : SeedSourceValid n low) (loss : ℝ) : ℝ :=
  (seed_finite_width_cells n low hv loss).choose
def seedWidthDelta (n low : Source) (hv : SeedSourceValid n low) (loss : ℝ) : ℝ :=
  (seed_finite_width_cells n low hv loss).choose_spec.choose
def seedWidthCell (n low : Source) (hv : SeedSourceValid n low) (loss : ℝ) : ℝ→ℝ :=
  upperWidthCell (crossing n low) n.cap (seedWidthDelta n low hv loss)

theorem nf_width_certificate (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) (loss : ℝ) :
    0<nfWidthMargin n low high hv ha loss ∧ 0<nfWidthDelta n low high hv ha loss ∧
    nfWidthDelta n low high hv ha loss≤1 ∧
    |loss| *nfWidthDelta n low high hv ha loss≤(n.allowance:ℝ) ∧
    2*(|loss| *nfWidthDelta n low high hv ha loss)≤nfWidthMargin n low high hv ha loss ∧
    FiniteReferenceCells (crossing n low) n.cap finalK (nfWidthDelta n low high hv ha loss)
      (nfWidthCell n low high hv ha loss) ∧
    ∀s∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,nfWidthMargin n low high hv ha loss/2≤sourceScalarReal (11243277/2500000) n low
        (nfWidthCell n low high hv ha loss s) j-|loss| *nfWidthDelta n low high hv ha loss) ∧
      0≤sourceWeakReal n low (nfWidthCell n low high hv ha loss s) ∧
      ∀j,nfWidthMargin n low high hv ha loss/2≤sourceDensityWidthReal n low high
        (nfWidthCell n low high hv ha loss s) ν j-|loss| *nfWidthDelta n low high hv ha loss :=
  (nf_finite_width_cells n low high hv ha loss).choose_spec.choose_spec

theorem seed_width_certificate (n low : Source) (hv : SeedSourceValid n low) (loss : ℝ) :
    0<seedWidthMargin n low hv loss ∧ 0<seedWidthDelta n low hv loss ∧
    seedWidthDelta n low hv loss≤1 ∧
    |loss| *seedWidthDelta n low hv loss≤(n.allowance:ℝ) ∧
    2*(|loss| *seedWidthDelta n low hv loss)≤seedWidthMargin n low hv loss ∧
    FiniteReferenceCells (crossing n low) n.cap seedK (seedWidthDelta n low hv loss)
      (seedWidthCell n low hv loss) ∧
    ∀s∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,seedWidthMargin n low hv loss/2≤sourceScalarReal (112445673/25000000) n low
        (seedWidthCell n low hv loss s) j-|loss| *seedWidthDelta n low hv loss) ∧
      0≤sourceWeakReal n low (seedWidthCell n low hv loss s) ∧
      ∀j : Fin 6,seedWidthMargin n low hv loss/2≤sourceDensityWidthReal n low none
        (seedWidthCell n low hv loss s) ν (Fin.castLE (by decide) j)-|loss| *seedWidthDelta n low hv loss :=
  (seed_finite_width_cells n low hv loss).choose_spec.choose_spec

theorem crossing_real_identity (n low : Source) (hL : n.L<low.L) :
    (n.B:ℝ)-(low.B:ℝ)+((low.L:ℝ)-(n.L:ℝ))*(crossing n low:ℝ)=0 := by
  have hd : (low.L:ℝ)-(n.L:ℝ)≠0:=ne_of_gt (by exact_mod_cast sub_pos.mpr hL)
  have he : (crossing n low:ℝ)=((low.B:ℝ)-(n.B:ℝ))/((low.L:ℝ)-(n.L:ℝ)):=by simp [crossing]
  have hh : (crossing n low:ℝ)*((low.L:ℝ)-(n.L:ℝ))=(low.B:ℝ)-(n.B:ℝ):=by
    rw [he]
    exact div_mul_cancel₀ _ hd
  nlinarith only [hh]

/-- HIGH chooses a fixed rounding-loss coefficient, then supplies only the
literal first physical norm on the canonically certified finite width grid. -/
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
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.nf_width_certificate
#print axioms QRH.Record1252270103Low.seed_width_certificate
#print axioms QRH.Record1252270103Low.seed_step_of_physical
#print axioms QRH.Record1252270103Low.nf_step_of_physical
