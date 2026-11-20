/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Selected original cells discharge the paid-input analytic phase upper and
all original-row/nonprincipal gates internally. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceActual
import Candidate.C092.transport.MixedUpperFinalCellUpper
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Cycle092.MixedUpperFinal QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- A compact typed handoff preserves the actual carrier and original packet. -/
structure PaidActualResult (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (Z : ℝ)
    (h decrement epsilon xi ann loss massEps cap : ℝ)
    (common nativeRows : Finset FreeRow) (d a nativeHeight : ℝ) (x z : ℂ) (r : Row) (outerFee : ℝ) where
  reverse : Bool
  input : PaidSliceInput h decrement epsilon xi ann loss massEps cap (sourceWidthMin D) reverse D F J η Z
  common_eq : input.bank.common=common
  d_eq : input.bank.d=d
  a_eq : input.bank.a=a
  height_eq : input.bank.height=nativeHeight
  x_eq : input.x=x
  z_eq : input.z=z
  r_eq : input.r=r
  fee_eq : input.outerFee=outerFee
  rows_eq : input.bank.currentSlice.fiber.rows=nativeRows
  data_eq : input.data=(fun (u : input.bank.currentSlice.fiber.rows)=>Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime u.val
    (input.nonprincipal u.val u.property)))

/-- Actual selected-cell endpoint input: no Layout, Presented, reflection
family, native row estimate or physical slot-upper premise remains. Only
explicit raw admission, branch, early fineness and scalar fee guards remain. -/
theorem actual_selected_paid_inputs (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (cap : ℝ) (hcap : 0<cap) (hfine : ∀s,D.length s ≤ cap/200)
    (padding τ : ℝ) (hτ : 0<τ) (hheight : 4*τ<(1/200:ℝ)*D.cost)
    (hpad : padding+2*D.t ≤ 1/10000000000) (n : ℕ) (η : Character) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀i∈Finset.range (n+1),∀j0 : ℕ,
    (cellRows D F padding Z idx grid k i j0).Nonempty →
    let d:=sourceDyadConductor Z D.t k
    let a:ℝ:=51/100+D.e*j0
    let rows:=cellRows D F padding Z idx grid k i j0
    ∀ (hd : (1/100:ℝ) ≤ d) (hdhi : d ≤ 7/8) (ha : 51/100<a) (hahi : a ≤ 7/8),
    ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
    ∀ (t₀ γ : ℝ) (B : CellBank D F η Z d a rows z bin t₀ γ τ i),
    ∀ (r : Row),r∈TopData.rows →
    r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    t₀=Return.cutoffI (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    γ=(rowGamma r.box r.B:ℝ) → D.ε ≤ 3*witnessCollar →
    ∀ (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
      (hne : ((B.layoutCap P (by linarith) hdhi cap hcap hfine).common σ).Nonempty) (j : Offset),
    firstShort (inverseLength (Z^d) σ)=some j →
    centralLengths (inverseLength (Z^d) σ j) (ordinaryLength (Z^d) σ j) →
    widthLo ≤ ordinaryLength (Z^d) σ j ∧ ordinaryLength (Z^d) σ j ≤ widthHi →
    ∀ (h decrement epsilon xi ann loss massEps : ℝ) (J : Finset (Fin D.N)),
    MixedTicketTails.originalDlow r ≤ d → d ≤ h+rowPad →
    1+PacketJoin.nativeHeight Z d τ i ≤ Z^d →
    ∀ (x : ℂ),x.re=a+16*D.e →
    ∀ (outerFee : ℝ),
    d*((2*a-1)*(classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))*decrement+
      D.t*(Geometry.ell/d)+(2*a-1)*(min P.mesh cap)/2+D.ε+
      (countLoss D.ε (min P.mesh cap) D.t+epsilon+loss)/2+massEps)+outerFee
      ≤ paddingDebit+(1/100000000000000:ℝ) →
    Nonempty (PaidActualResult D F J η Z h decrement epsilon xi ann loss massEps cap
      ((B.layoutCap P (by linarith) hdhi cap hcap hfine).common σ)
      (((B.layoutCap P (by linarith) hdhi cap hcap hfine).fiber σ hne j).rows)
      d a (PacketJoin.nativeHeight Z d τ i) x z r outerFee) := by
  filter_upwards [PacketJoin.actual_cell_e49_data D F P padding τ hτ hheight hpad n η,
    actual_selected_cell_native_upper D F P padding τ hτ hheight hpad n η] with Z hc hu
  refine ⟨hc.1,?_⟩
  intro idx grid hsel k hk i hi j0 hneCell
  dsimp only
  intro hd hdhi ha hahi z hz him bin t₀ γ B r hr hp ht hg hs σ hne j first central narrow
    h decrement epsilon xi ann loss massEps J hdold hdmax height x hx outerFee fee
  let d:=sourceDyadConductor Z D.t k
  let a:ℝ:=51/100+D.e*j0
  let rows:=cellRows D F padding Z idx grid k i j0
  have hcell:=hc.2 idx grid hsel k hk i hi j0 hneCell
  have hlower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u:=fun u hu=>(hcell.2.2.2.1 u hu).1
  have hnp : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1:=fun u hu=>(hcell.2.2.2.1 u hu).2.2
  let hd' : (1/200:ℝ) ≤ d := by linarith
  have hne0 : ((B.layout P hd' hdhi).common σ).Nonempty := hne
  have upper:=hu.2 idx grid hsel k hk i hi j0 hneCell hd' hdhi z hz him bin t₀ γ B σ hne0 j
  have upper' : ∀u∈(B.layoutCap P hd' hdhi cap hcap hfine).common σ,∀s : Fin D.N,
      ‖originalPhysical D F Z d (fun _=>z) u s‖ ≤
      (Z^d)^((D.length s/d)*(binValue Finset.univ ((2*a-1)/2) D.t bin s+D.t)) := by
    intro u hu s
    exact upper u hu s
  let Q:=actual_paid_input B P cap hcap hfine hc.1 hd hdhi ha hahi hlower hnp hz him r hr hp ht hg hs
    σ hne j first central narrow h decrement epsilon xi ann loss massEps J hdold hdmax height x hx upper' outerFee fee
  exact ⟨{
    reverse:=_,input:=Q,common_eq:=rfl,d_eq:=rfl,a_eq:=rfl,height_eq:=rfl,
    x_eq:=rfl,z_eq:=rfl,r_eq:=rfl,fee_eq:=rfl,rows_eq:=rfl,data_eq:=rfl}⟩

#print axioms actual_selected_paid_inputs
end
end QRH.Cycle092.MixedMiddleReturn
