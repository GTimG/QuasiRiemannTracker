/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All actual remaining-bank small packets, with the complete response count paid. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClass
import Candidate.C092.transport.MixedUpperFinalReserve
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MixedMiddleReturn
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open QRH.Cycle092.MixedUpperFinal QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

theorem earlier_P1_selected_middle_sum
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
    ∀ (hd : (1/2:ℝ) ≤ d) (hdhi : d ≤ 7/8) (ha : 51/100<a) (hahi : a ≤ 7/8),
    ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
    ∀ (t₀ γ : ℝ) (B : CellBank D F η Z d a rows z bin t₀ γ τ i),
    ∀ (r : Row),r∈TopData.rows →
    r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    t₀=Return.cutoffI (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
    γ=(rowGamma r.box r.B:ℝ) → MixedTicketTails.originalDlow r ≤ d → d ≤ h+rowPad →
    ∀ (x : ℂ),x.re=a+16*D.e → ∀outerFee : ℝ,
    d*((2*a-1)*(classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))*decrement+
      D.t*(Geometry.ell/d)+(2*a-1)*(min P.mesh cap)/2+D.ε+
      (countLoss D.ε (min P.mesh cap) D.t+epsilon+loss)/2+massEps)+outerFee
      ≤ paddingDebit+(1/100000000000000:ℝ) →
    (∑σ∈Finset.univ.filter (fun σ=>remainingMiddle (Z^d) (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
      t₀ γ ((rowV r.box:ℝ)/(r.box.uHi:ℝ)) (rowBudget r.B:ℝ) σ),
      ∑J∈Finset.univ.powerset,classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) r
        ((B.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ)) ≤
    C*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
      (Z^d)^(finalPower a d sourceCost outerFee (theta-1/10000000000000)) := by
  classical
  obtain ⟨mp,cap,hcap,hmp,hsource⟩:=earlier_P1_selected_class h hh hh' hgeometry hP1 hβ hdec hepsilon
  refine ⟨mp,cap,hcap,hmp,?_⟩
  intro D F hf hs he ht hβD hsupport massEps xi ann loss hmass hxi hann hcollar hloss η
  obtain ⟨hfCap,m,C,hC,hsource⟩:=hsource D F hf hs he ht hβD hsupport massEps xi ann loss hmass hxi hann hcollar hloss η
  obtain ⟨Cd,hCd,hdesc⟩:=descriptor_power_absorbed
    (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (1/10000000000000) (by norm_num)
  let C0:=C*((Finset.univ : Finset (Fin D.N)).powerset.card:ℝ)*max 1 Cd
  have hmask : 0<((Finset.univ : Finset (Fin D.N)).powerset.card:ℝ):=by
    exact_mod_cast Finset.card_pos.mpr (show (Finset.univ : Finset (Fin D.N)).powerset.Nonempty from ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩)
  have hC0 : 0<C0:=by dsimp [C0];positivity
  refine ⟨hfCap,m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hsource P padding τ hτ hheight hpad n,hdesc] with Z hp hdsc
  refine ⟨hp.1,?_⟩
  intro idx grid hsel k hk i hi j hn
  dsimp only
  intro hd hdhi ha hahi z hz him bin t₀ γ B r hr hpoint hbase hgamma hdold hdmax x hx outerFee hfee
  let d:=sourceDyadConductor Z D.t k
  let a:ℝ:=51/100+D.e*j
  let X:=Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))
  let mid : X→Prop:=remainingMiddle (Z^d) (2*a-1)
    (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
    t₀ γ ((rowV r.box:ℝ)/(r.box.uHi:ℝ)) (rowBudget r.B:ℝ)
  let H:ℝ:=3+(3*i+1:ℕ)*Z^τ
  let V:ℝ:=(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)
  let powStrong:ℝ:=(Z^d)^(finalPower a d sourceCost outerFee (theta-1/2500000000000))
  have hZ0 : 0<Z:=zero_lt_one.trans hp.1
  have hbase0 : 0≤C*H^m*V*powStrong:=by dsimp [H,V,powStrong];positivity
  have hbound (σ : X) (hσ : mid σ) (J : Finset (Fin D.N)) :
      classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) r
        ((B.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ) ≤ C*H^m*V*powStrong:=by
    by_cases hne:((B.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ).Nonempty
    · have hb:=hp.2 idx grid hsel k hk i hi j hn (by linarith) hdhi ha hahi z hz him bin t₀ γ B r hr hpoint hbase hgamma hdold hdmax σ hne hσ J x hx outerFee hfee
      convert hb using 1 <;> dsimp [H,V,powStrong] <;> ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simpa only [classSmallNorm,Finset.sum_empty,mul_zero] using hbase0
  have hsum : (∑σ∈Finset.univ.filter mid,∑J∈Finset.univ.powerset,
      classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) r
        ((B.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ)) ≤
      (Fintype.card X:ℝ)*((Finset.univ : Finset (Fin D.N)).powerset.card:ℝ)*(C*H^m*V*powStrong):=by
    calc
      _ ≤ ∑σ : X,((Finset.univ : Finset (Fin D.N)).powerset.card:ℝ)*(C*H^m*V*powStrong) := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro σ _
        by_cases hm:mid σ
        · rw [if_pos hm]
          exact (Finset.sum_le_sum (fun J _=>hbound σ hm J)).trans_eq (by simp only [Finset.sum_const,nsmul_eq_mul])
        · rw [if_neg hm];positivity
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
  have hpow:=hdsc.2 d a sourceCost outerFee (theta-1/2500000000000) (theta-1/10000000000000)
    (by linarith : (1/2:ℝ) ≤ d) (by nlinarith only [hdhi])
  have hpow' : (Fintype.card X:ℝ)*powStrong ≤ max 1 Cd*(Z^d)^(finalPower a d sourceCost outerFee (theta-1/10000000000000)):=
    hpow.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  apply hsum.trans
  have hb:=mul_le_mul_of_nonneg_left hpow' (show 0≤((Finset.univ : Finset (Fin D.N)).powerset.card:ℝ)*C*H^m*V by dsimp [H,V];positivity)
  convert hb using 1 <;> dsimp [C0,H,V,powStrong] <;> ring

#print axioms earlier_P1_selected_middle_sum
end
end QRH.Cycle092.MixedUpperFinal
