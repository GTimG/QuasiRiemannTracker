/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected common-class original small packet, with finite source
constants fixed before every transport and physical height exponent. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClassGeometry
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

/-- The source bank here is only genuine native witness metadata, constructed
by actual_selected_cell_banks. No source/moment/cardinality/upper or native
height estimate is an endpoint premise. All masks share the same early C,m. -/
theorem earlier_P1_selected_class
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
    ∀ (t₀ γ : ℝ) (B : CellBank D F η Z d a rows z bin t₀ γ τ i),
    ∀ (r : Row),r∈TopData.rows →
    r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    t₀=Return.cutoffI (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    γ=(rowGamma r.box r.B:ℝ) → MixedTicketTails.originalDlow r ≤ d → d ≤ h+rowPad →
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
  classical
  obtain ⟨mp,cap,hmp,hcap,hpacket⟩ := earlier_P1_paid_finite h hh hh' hgeometry hP1 hβ hdec hepsilon
  refine ⟨mp,cap,hcap,hmp,?_⟩
  intro D F hf hs he ht hβD hsupport massEps xi ann loss hmass hxi hann hcollar hloss η
  obtain ⟨m,C0,hC0,hfcap,hpacket⟩ := hpacket D F hf hs he ht hβD massEps xi ann loss hmass hxi hann hcollar hloss η
  let C:=C0*(2*Real.pi+2)^m
  refine ⟨hfcap,m,C,by dsimp [C];positivity,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpacket,actual_selected_paid_inputs D F P cap hcap hfcap padding τ hτ hheight hpad n η,
    PacketJoin.actual_cell_e49_data D F P padding τ hτ hheight hpad n η,class_native_height_event n]
    with Z hp hi hc hH
  refine ⟨hp.1,?_⟩
  intro idx grid hsel k hk i hii j0 hneCell
  dsimp only
  intro hd hdhi ha hahi z hz him bin t₀ γ B r hr hpoint hbase hgamma hdold hdmax σ hne hremaining J x hx outerFee hfee
  let d:=sourceDyadConductor Z D.t k
  let a:ℝ:=51/100+D.e*j0
  let rows:=cellRows D F padding Z idx grid k i j0
  have hlower : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u := fun u hu=>
    ((hc.2 idx grid hsel k hk i hii j0 hneCell).2.2.2.1 u hu).1
  obtain ⟨j,first,central,hscore⟩ := hremaining
  let hd' : (1/200:ℝ) ≤ d := by linarith
  let M:=B.middleCap P cap hcap hfcap hp.1 hd' hdhi ha hahi hlower hz him r hr hpoint hbase hgamma hsupport σ hne j first central
  have hinsuff : M.delta*M.centered<4*(rowBudget r.B:ℝ)/3 := hscore
  have narrow:=MixedInnerActualWidth.bank_width_of_insufficient hr M hp.1 hpoint hgamma.le
    (by change witnessCollar ≤ (1:ℝ)/10^(13:ℕ);norm_num [witnessCollar]) hinsuff
  have hheight0 : 1+PacketJoin.nativeHeight Z d τ i ≤ Z^d := hH.2 d τ i hd hdhi hτ.le
    (by have hh0:=witness_zero_height_from_budget D hheight;norm_num at hh0;exact hh0.le) (by exact Nat.le_of_lt_succ (Finset.mem_range.mp hii))
  obtain ⟨R⟩ := hi.2 idx grid hsel k hk i hii j0 hneCell hd hdhi ha hahi z hz him bin t₀ γ B r hr hpoint hbase hgamma
    hsupport σ hne j first central narrow h decrement epsilon xi ann loss massEps J hdold hdmax hheight0 x hx outerFee hfee
  have hb:=hp.2 J R.reverse R.input
  have heq:=class_common_exact D F J η Z h decrement epsilon xi ann loss massEps cap _ _ d a
    (PacketJoin.nativeHeight Z d τ i) x z r outerFee R
  rw [←heq] at hb
  have hb' : classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) r
      ((B.layoutCap P hd' hdhi cap hcap hfcap).common σ) ≤
    C0*(1+PacketJoin.nativeHeight Z d τ i)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
      (Z^d)^(finalPower a d sourceCost outerFee (theta-1/2500000000000)) := by
    simpa only [R.height_eq,R.d_eq,R.a_eq,R.fee_eq,MiddleBank.baseScale] using hb
  have hheightpow:=paid_native_height m i hp.1.le hdhi hτ.le
  apply hb'.trans
  have hcoef:=mul_le_mul_of_nonneg_left hheightpow hC0.le
  calc
    _ ≤ C0*((2*Real.pi+2)^m*(3+(3*i+1:ℕ)*Z^τ)^m)*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
      (Z^d)^(finalPower a d sourceCost outerFee (theta-1/2500000000000)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (by positivity [zero_lt_one.trans hp.1])) (by positivity [zero_lt_one.trans hp.1]))
          (by positivity [zero_lt_one.trans hp.1])
    _ = _ := by dsimp [C];ring

#print axioms earlier_P1_selected_class
end
end QRH.Cycle092.MixedMiddleReturn
