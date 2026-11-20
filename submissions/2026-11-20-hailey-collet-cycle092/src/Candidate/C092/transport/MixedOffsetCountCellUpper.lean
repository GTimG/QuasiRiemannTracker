/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native bank slot uppers derived on the caller's actual selected amplitude cell. -/
import Candidate.C092.transport.MixedOffsetCountPhaseUpper
import Candidate.C092.transport.MixedOffsetCountLayoutFacts
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition HeckeDetectorAmplitudeFirst HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank
variable [Geometry.Parameters]

/-- The numerical slot upper comes from the actual selected detector band.
The native fiber keeps the original physical phase bin and full slots at
EVERY bank offset; only membership in the common class is needed. -/
theorem actual_buffered_cell_native_upper (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0<τ)
    (hheight : 4*τ<(1/200:ℝ)*D.cost) (n : ℕ) (η : Character) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀ (idx grid : FreeRow→ℕ),ProbeAssembly.selected D F padding τ n η Z idx grid →
    ∀ (d threshold : ℝ),(1/200:ℝ) ≤ d → d ≤ 7/8 → 1/50<threshold →
    ∀ (i k : ℕ) (z : Fin D.N→ℂ),(∀s,(z s).re=17/50) →
      (∀s,|(z s).im| ≤ (3*i+1:ℕ)*Z^τ) →
    let rows:=mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k
    rows.Nonempty →
    ∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t,
    let cell:=amplitudeCell D F Z d (bandLower D k) rows z bin
    ∀ (t₀ γ T allowance mesh : ℝ)
      (hm : 0 ≤ mesh)
      (hwp : ∀s∈(Finset.univ:Finset (Fin D.N)),0<D.length s/d)
      (hwm : ∀s∈(Finset.univ:Finset (Fin D.N)),D.length s/d ≤ mesh)
      (hsupply : 7/37 ≤ ∑s : Fin D.N,D.length s/d)
      (B : SourceBank F.modulus ⊤ le_top F.S F.exclusions η cell (Z^d) (bandLower D k)
        D.ε t₀ γ T allowance i)
      (hne : cell.Nonempty) (hrow : ∀u∈cell,rowNorm u ≤ Z^d),
    let L:=BankLayout.ofAmplitudeCell rows (Z^d) (bandLower D k) D.ε t₀ γ T allowance i
      Finset.univ (fun _ x=>(F.w x:ℂ)) (fun _=>2) (fun s=>D.length s/d) z
      mesh D.t hm D.t_pos hwp hwm hsupply bin B hne hrow
    ∀ (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
      (hσ : (L.common σ).Nonempty) (j : Offset),
    let f:=L.fiber σ hσ j
    f.slots=Finset.univ ∧ f.binWidth=D.t ∧
      ∀u∈L.common σ,∀s : Fin D.N,
        ‖physical F.modulus ⊤ (fun w : FreeRow=>w.val) f.profile f.upper f.widths f.external (Z^d) u s‖
          ≤ (Z^d)^(f.widths s*(f.bin s+f.binWidth)) := by
  have hu:=actual_buffered_cell_slot_upper D F P padding τ hτ hheight n η
  filter_upwards [hu] with Z hu
  refine ⟨hu.1,?_⟩
  intro idx grid hsel d threshold hd hd' hthreshold i k z hz him
  dsimp only
  intro hneRows bin t₀ γ T allowance mesh hm hwp hwm hsupply B hne hrow
  let L:=BankLayout.ofAmplitudeCell
    (mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k)
    (Z^d) (bandLower D k) D.ε t₀ γ T allowance i
    Finset.univ (fun _ x=>(F.w x:ℂ)) (fun _=>2) (fun s=>D.length s/d) z
    mesh D.t hm D.t_pos hwp hwm hsupply bin B hne hrow
  intro σ hσ j
  refine ⟨rfl,rfl,?_⟩
  intro u hum s
  have hcell:=class_subset _ L.labels (fun j u=>(L.witness j u).left)
    (fun j u=>(L.witness j u).right) σ hum
  have hb:=hu.2 idx grid hsel d threshold hd hd' hthreshold i k z hz him hneRows bin u hcell s
  have hpos : 0<Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hu.1) _
  change ‖originalPhysical D F Z d z u s‖ ≤ (Z^d)^
    ((D.length s/d)*(binValue Finset.univ ((2*bandLower D k-1)/2) D.t bin s+D.t))
  rw [Real.rpow_mul hpos.le]
  exact hb

#print axioms actual_buffered_cell_native_upper
end
end QRH.Cycle092.MixedOffsetCount
