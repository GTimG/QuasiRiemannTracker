/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected common-class original small packet, with finite source
constants fixed before every transport and physical height exponent. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClass
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
open QRH.Cycle092.MixedUpperFinal QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Actual source bank construction precedes all later descriptors and
original masks. This corollary has no bank/source object premise. -/
theorem earlier_P1_selected_class_source
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hP1 : RawTicket.EarlierP1) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {decrement epsilon : ℝ} (hdec : 0<decrement ∧ decrement ≤ 1/1000) (hepsilon : 0<epsilon) :
    ∃mp : ℝ→ℝ,∃(cap : ℝ),∃(hcap : 0<cap),(∀t,0<t → 0 < mp t) ∧
    ∀(D : BaselineData) (F : BaselineSourceData D),
      (∀s,D.length s ≤ mp D.t/200) → (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
      2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa → D.ε ≤ 3*witnessCollar →
    ∀(massEps xi ann loss : ℝ),0 < massEps → 0<xi → 0 ≤ ann →
      2*xi+ann ≤ witnessCollar → 0<loss →
    ∀η : Character,∃(hfCap : ∀s,D.length s ≤ cap/200),∃m : ℕ,∃C : ℝ,0<C ∧
    ∀(P : TransportParameters D) (padding τ : ℝ),0<τ →
      4*τ<(1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 → ∀n : ℕ,
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
    (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
    ∀ (t₀ γ : ℝ),
    ∀ (r : Row),r∈TopData.rows →
    r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    t₀=Return.cutoffI (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    γ=(rowGamma r.box r.B:ℝ) → MixedTicketTails.originalDlow r ≤ d → d ≤ h+rowPad →
    ∃B : CellBank D F η Z d a rows z bin t₀ γ τ i,
    ∀ (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
      (hne : ((B.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ).Nonempty),
    remainingMiddle (Z^d) (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
      t₀ γ ((rowV r.box:ℝ)/(r.box.uHi:ℝ)) (rowBudget r.B:ℝ) σ →
    ∀ (J : Finset (Fin D.N)) (x : ℂ),x.re=a+16*D.e → ∀outerFee : ℝ,
    d*((2*a-1)*(classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))*decrement+
      D.t*(Geometry.ell/d)+(2*a-1)*(min P.mesh cap)/2+D.ε+
      (countLoss D.ε (min P.mesh cap) D.t+epsilon+loss)/2+massEps)+outerFee
      ≤ paddingDebit+(1/100000000000000:ℝ) →
    classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) r
      ((B.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ) ≤
    C*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
      (Z^d)^(finalPower a d sourceCost outerFee (theta-1/2500000000000)) := by
  obtain ⟨mp,cap,hcap,hmp,hclass⟩ := earlier_P1_selected_class h hh hh' hgeometry hP1 hβ hdec hepsilon
  refine ⟨mp,cap,hcap,hmp,?_⟩
  intro D F hf hs he ht hβD hsupport massEps xi ann loss hmass hxi hann hcollar hloss η
  obtain ⟨hfCap,m,C,hC,hclass⟩ := hclass D F hf hs he ht hβD hsupport massEps xi ann loss hmass hxi hann hcollar hloss η
  refine ⟨hfCap,m,C,hC,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hclass P padding τ hτ hheight hpad n,
    actual_selected_cell_banks D F P padding τ hτ hheight hpad n η] with Z hc hb
  refine ⟨hc.1,?_⟩
  intro idx grid hsel k hk i hii j0 hneCell
  dsimp only
  intro hd hdhi ha hahi z hz him bin hneAmplitude t₀ γ r hr hp hbase hgamma hdold hdmax
  have had:=original_bank_admission hr hp
  have hγ : 0 ≤ γ := by rw [hgamma];exact had.2.1
  have hlo : 1 ≤ t₀-γ := by rw [hbase,hgamma];exact had.2.2.2.1
  have hhi : t₀ ≤ 3/2 := by rw [hbase];exact had.2.2.2.2.1
  obtain ⟨B⟩ := (hb.2 idx grid hsel k hk i hii j0 hneCell).2.2.2.2.2 z hz him bin hneAmplitude t₀ γ hγ hlo hhi
  refine ⟨B,?_⟩
  intro σ hne hremaining J x hx outerFee hfee
  exact hc.2 idx grid hsel k hk i hii j0 hneCell hd hdhi ha hahi z hz him bin t₀ γ B r hr hp hbase hgamma
    hdold hdmax σ hne hremaining J x hx outerFee hfee

#print axioms earlier_P1_selected_class_source
end
end QRH.Cycle092.MixedMiddleReturn
