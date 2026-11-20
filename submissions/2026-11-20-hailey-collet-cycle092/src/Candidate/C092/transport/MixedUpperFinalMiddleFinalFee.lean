/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal final early reserve pays all actual remaining middle classes. -/
import Candidate.C092.transport.MixedUpperFinalMiddleSum
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

theorem earlier_P1_selected_middle_final_fee
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hP1 : RawTicket.EarlierP1) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError loss : ℝ) (haff : 0<affineError) (hloss : 0<loss) :
    ∃mp : ℝ→ℝ,∃(cap : ℝ),∃(hcap : 0<cap),(∀t,0<t → 0 < mp t) ∧
    ∀(D : BaselineData) (F : BaselineSourceData D),
      (∀s,D.length s ≤ mp D.t/200) → (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
      2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa → D.ε ≤ 3*witnessCollar →
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
    ∀ (x : ℂ),x.re=a+16*D.e →
    159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*rowPad ≤ 1/100000000000000 →
    (∑σ∈Finset.univ.filter (fun σ=>remainingMiddle (Z^d) (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
      t₀ γ ((rowV r.box:ℝ)/(r.box.uHi:ℝ)) (rowBudget r.B:ℝ) σ),
      ∑J∈Finset.univ.powerset,classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) r
        ((B.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ)) ≤
    C*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
      (Z^d)^(finalPower a d sourceCost (16*D.e+2*P.eps*d+17*D.t/25) (theta-1/10000000000000)) := by
  classical
  let dec:=min (1/1000:ℝ) (affineError/1000)
  have hdec : 0<dec ∧ dec ≤ 1/1000:=⟨lt_min (by norm_num) (by positivity),min_le_left _ _⟩
  have heps : 0<affineError/1000:=by positivity
  obtain ⟨mp,cap,hcap,hmp,hsource⟩:=earlier_P1_selected_middle_sum h hh hh' hgeometry hP1 hβ hdec heps
  refine ⟨mp,cap,hcap,hmp,?_⟩
  intro D F hf hs he ht hβD hsupport η
  obtain ⟨hfCap,m,C,hC,hsource⟩:=hsource D F hf hs he ht hβD hsupport
    (affineError/1000) (witnessCollar/4) (witnessCollar/4) (loss/1000) heps
    (by norm_num [witnessCollar]) (by norm_num [witnessCollar]) (by norm_num [witnessCollar]) (by positivity) η
  refine ⟨hfCap,m,C,hC,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hsource P padding τ hτ hheight hpad n] with Z hp
  refine ⟨hp.1,?_⟩
  intro idx grid hsel k hk i hi j hn
  dsimp only
  intro hd hdhi ha hahi z hz him bin t₀ γ B r hr hpoint hbase hgamma hdold hdmax x hx hreserve
  have hpoint0:=Top.point_guards (Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)) hpoint
  have hfee:=middle_fee_paid_from_early_reserve D.ε D.t P.mesh (min P.mesh cap) D.e P.eps
    affineError loss rowPad Geometry.ell (sourceDyadConductor Z D.t k) (2*(51/100+D.e*j)-1)
    (classMean Finset.univ ((2*(51/100+D.e*j)-1)/2) D.t
      (fun s=>D.length s/sourceDyadConductor Z D.t k) bin/(2*(51/100+D.e*j)-1)) paddingDebit
    D.epsilon_pos.le D.t_pos.le (le_min P.mesh_pos.le hcap.le) (min_le_left _ _)
    D.e_pos.le P.eps_pos.le haff.le hloss.le (by unfold rowPad;positivity)
    (by linarith) (by linarith) (by linarith) (by linarith) hpoint0.2.2.1 hpoint0.2.2.2
    Geometry.ell_lt_fifth.le (by unfold paddingDebit QRH.Cycle090.sourceCost rowPad;positivity) hreserve
  exact hp.2 idx grid hsel k hk i hi j hn hd hdhi ha hahi z hz him bin t₀ γ B r hr hpoint
    hbase hgamma hdold hdmax x hx (16*D.e+2*P.eps*(sourceDyadConductor Z D.t k)+17*D.t/25) hfee

#print axioms earlier_P1_selected_middle_final_fee
end
end QRH.Cycle092.MixedUpperFinal
