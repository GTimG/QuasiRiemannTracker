/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original selected cells supply all physical uppers in the true bank. -/
import Candidate.C092.transport.MixedUpperFinalPartition
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- No phase-upper assumption remains on the actual selected cells.
The same original numerical upper is inherited by every common class and
every actual cutoff of the already constructed same-zero bank. -/
theorem actual_selected_cell_native_upper (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0<τ)
    (hheight : 4*τ<(1/200:ℝ)*D.cost) (hpad : padding+2*D.t ≤ 1/10000000000)
    (n : ℕ) (η : Character) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀i∈Finset.range (n+1),∀j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d:=sourceDyadConductor Z D.t k
    let a:ℝ:=51/100+D.e*j
    let rows:=cellRows D F padding Z idx grid k i j
    ∀ (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8),
    ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
    ∀ (t₀ γ : ℝ) (B : CellBank D F η Z d a rows z bin t₀ γ τ i),
    let L:=B.layout P hd hdhi
    ∀ (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
      (hσ : (L.common σ).Nonempty) (offsetIndex : Offset),
    let f:=L.fiber σ hσ offsetIndex
    ∀u∈L.common σ,∀s : Fin D.N,
      ‖physical F.modulus ⊤ (fun w : FreeRow=>w.val) f.profile f.upper f.widths f.external (Z^d) u s‖
        ≤ (Z^d)^(f.widths s*(f.bin s+f.binWidth)) := by
  filter_upwards [QRH.Cycle092.PacketJoin.actual_cell_e49_data D F P padding τ hτ hheight hpad n η]
    with Z hg
  refine ⟨hg.1,?_⟩
  intro idx grid hsel k hk i hi j hne
  dsimp only
  intro hd hdhi z hz him bin t₀ γ B σ hσ offsetIndex u hu s
  let d:=sourceDyadConductor Z D.t k
  let a:ℝ:=51/100+D.e*j
  let rows:=cellRows D F padding Z idx grid k i j
  let L:=B.layout P hd hdhi
  have hcell:=class_subset _ L.labels (fun j u=>(L.witness j u).left)
    (fun j u=>(L.witness j u).right) σ hu
  have hmem : u∈rows:=(Finset.mem_filter.mp hcell).1
  have hs:=(hg.2 idx grid hsel k hk i hi j hne).2.2.2.2 z hz him |>.1 u hmem s
  have hdpos : 0<d:=by dsimp [d];linarith
  have hZpos : 0<Z:=zero_lt_one.trans hg.1
  have hP : (Z^d)^(D.length s/d)=Z^(D.length s) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hQ:=originalPhysical_eq D F Z d hZpos hdpos (fun _=>z) u s
  have he:=(Finset.mem_filter.mp hcell).2
  have hbin : HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.length s/d)) ((2*a-1)/2) D.t
      (originalPhysical D F Z d (fun _=>z) u s)=binValue Finset.univ ((2*a-1)/2) D.t bin s := by
    have hv:=congrArg (fun b : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t=>
      (b ⟨s,Finset.mem_univ _⟩).val) he
    simpa only [amplitudeLabel,binValue,dif_pos (Finset.mem_univ s)] using hv
  change ‖originalPhysical D F Z d (fun _=>z) u s‖ ≤ (Z^d)^
    ((D.length s/d)*(binValue Finset.univ ((2*a-1)/2) D.t bin s+D.t))
  rw [Real.rpow_mul (Real.rpow_nonneg hZpos.le _),hP,hQ]
  rw [hP,hQ] at hbin
  rw [←hbin]
  exact hs

#print axioms actual_selected_cell_native_upper
end
end QRH.Cycle092.MixedUpperFinal
