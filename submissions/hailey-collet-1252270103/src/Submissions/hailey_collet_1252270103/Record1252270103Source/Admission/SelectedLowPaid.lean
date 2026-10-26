/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected original slots, positive Newton corners, and LOW erasure. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedLowErasure
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowPhysicalPrice
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowPaid
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst Cycle61Moment Cycle61InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentEnergyBands
open QRH.Record12518109Source QRH.Record1252270103Low QRH.Record1252270103Restoration
open SelectedHighCofactorFamily SelectedHighSlots High.GlobalPhysical
open ConcretePrimeRowBridge CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentSourceRectangleMask CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion Record1252270103Second Record1252270103Source
open QRH.Record1252270103KernelMass
open CenteredMomentCommonRadialData
local notation "O"=>HeckeFamily.O
local instance selectedLowDecidable {κ : Type*} : DecidableEq κ:=Classical.decEq _
open SelectedLowErasure High PhysicalLowReserve
open Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph RegularLowPhysicalPrice
open CenteredMomentAmplificationChildSourceCaps
open OAI.SevenEighths.Record1252270103Source.Collision

theorem actual_selected_low_price
    {α:Type}[Fintype α] (Kgraph:ℚ)(n low:Source)(b:ℝ)
    (hg:RealGeometry Kgraph n low b)(hn:ParentGood n)(hlow:ParentGood low)
    (ha:0≤(n.allowance:ℝ))(hq0:0≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (s:Input α)(Am₁ Am₂ Dm Km R seed:Ideal O)(Fm:Ideal O→ℂ)
    (H Z ξ:ℝ)(hH:0<H)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s
      (markedSourceModifier Am₁ Am₂ Dm Km Fm) R seed H Z ξ hH bin))
    (reflected second:Bool)(datum:SecondInputDatum α)(U:Finset (CommonIndex datum.C datum.D))
    (sel:Selection s reflected second
      (FirstFamily.firstLabel s (markedSourceModifier Am₁ Am₂ Dm Km Fm) R seed H Z ξ hH bin j)
      datum.C datum.D R)
    (T:Finset α)(hT:T⊆sel.full)(S A:Finset (Ideal O))(hdpair:GoodPair (newtonDivisorPair S A))
    (w:α→ℝ)(N:ℕ)(upper M reserve width err errv rho mesh plainUpper radialRound outer e:ℝ)
    (hupper:1≤upper)(hZ:1<Z)(hN:Fintype.card α≤N)(hu:s.upper≤upper)
    (hscale:∀i,s.P i=Z^w i)(ht:length Z s.X₁+length Z s.X₂≤plainBudget n b width)
    (hw:∀i,0≤w i)(htotal:(∑i,w i)≤b)(hmesh0:0≤mesh)(hwm:∀i∈T,w i≤mesh)
    (hwidth0:0≤width)(hwidth:width≤PhysicalLowGuard.step n)(he:0<e)
    (hrho0:0≤rho)(hrho:rho≤(n.allowance:ℝ)/4)
    (hmesh:mesh≤(n.allowance:ℝ)/4)(herr:err≤(n.allowance:ℝ)/4)
    (herrv:errv≤(n.allowance:ℝ)/4)(hround0:0≤radialRound)
    (hround:radialRound≤(n.allowance:ℝ)/4)(houter:outer≤4*(n.allowance:ℝ)):
    let l:=FirstFamily.firstLabel s (markedSourceModifier Am₁ Am₂ Dm Km Fm) R seed H Z ξ hH bin j
    let delta:=max (labelD reflected l Z-labelC reflected l Z) 0
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l datum.C datum.D U
      Z M (Real.logb Z (volume s)) (sourceAReal n low b) ξ reserve err) errv
    let loss:=3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*radialRound
    let Q:=sourceFReal n low b-delta-rho
    delta≤labelC reflected l Z →
    0≤loss → loss≤(n.allowance:ℝ)/4 →
    loss+(low.B:ℝ)*rho+2*e≤(low.B:ℝ)*sourceFReal n low b-plainBudget n b width-b →
    Q≤x 2+radialRound →
    ∃select:Finset α,select⊆T ∧
      ∀(corner:Bool)(A₁ A₂:Ideal O),A₁≠0→A₂≠0→A₁*A₂∣finalPuncture sel→
      (∀i∈T,∀I∈s.pools (Sum.inl i),IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))→
      ∀(η:Character)(height:ℝ)(z:O),
      positiveCorner sel T corner A₁ A₂ plainUpper S A η height z=0 ∨
      (2*e≤Q ∧ RoundedPairAdmission (globalFace (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ)) Z
        ((if corner then sel.finalInput.Y₁ else sel.finalInput.X₁)/(newtonDivisorPair S A).1.absNorm)
        ((if corner then sel.finalInput.Y₂ else sel.finalInput.X₂)/(newtonDivisorPair S A).2.absNorm)
        radialRound (∑i∈select,w i) Q ∧
       x 0+x 1+Q-balancedGeometrySide reflected (Real.logb Z (volume s))
        (CoupledFirst.geometryExponents s (markedSourceModifier Am₁ Am₂ Dm Km Fm) R seed H Z ξ j.1.val)+
        (n.q:ℝ)*(∑i∈T\select,w i)+outer≤-8*(n.allowance:ℝ)) := by
  intro l delta x loss Q hdc hloss0 hloss hguard hrad
  have hB0:0≤(low.B:ℝ):=by exact_mod_cast hlow.1.le
  have hB1:(low.B:ℝ)≤1:=by exact_mod_cast hlow.2.1
  have hL:0<(low.L:ℝ):=by exact_mod_cast (show (0:ℚ)<low.L by linarith [hlow.2.2.1])
  have hh:0≤(low.cap:ℝ):=by exact_mod_cast hlow.2.2.2.1
  have hdelta:0≤delta:=le_max_right _ _
  have hchoose:=selected_low_corner_erasure sel T hT S A hdpair w N upper Z
    (plainBudget n b width) b (sourceFReal n low b) delta rho (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ)
    plainUpper mesh radialRound e hupper hZ hN hu hscale ht hw htotal hmesh0 hwm hround0 he
    hB0 hB1 hL hdelta hdc hh hguard
  obtain ⟨E,hE,hselect,himage,hfull,hret,herase,hcost,hcorner⟩:=hchoose
  let emb:=SelectedHighSlots.finalEmbedding sel.B₁.val sel.B₂.val sel.Bf.val
  let pull:=originalPullback emb T
  let select:=(pull\E).map emb
  let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
    Real.logb Z ((if second then datum.D else datum.C).absNorm:ℝ)+Real.logb Z (sel.Cf.absNorm:ℝ)
  let f:=(∑i,w i)-∑i:liveIndices sel.Bf.val,w i.val.val.val
  have hc₂:0≤Real.logb Z ((if second then datum.D else datum.C).absNorm:ℝ):=
    Real.logb_nonneg hZ (norm_ge_one _ (allocation_ne sel.firstInput _ sel.B₂))
  have hcf:0≤Real.logb Z (sel.Cf.absNorm:ℝ):=Real.logb_nonneg hZ
    (norm_ge_one _ (allocation_ne _ _ sel.Bf))
  have hc:labelC reflected l Z≤c:=by dsimp only [c,labelC];linarith
  have hsum:=Record12518109Natural.CommonSupply.sum_originalSlots emb emb.injective w
  have hf:0≤f:=by
    have hb: (∑i∈sel.full,w i)≤∑i,w i:=Finset.sum_le_univ_sum_of_nonneg hw
    change (∑i:liveIndices sel.Bf.val,w i.val.val.val)=∑i∈sel.full,w i at hsum
    dsimp only [f];rw [hsum];linarith only [hb]
  have hd₁:0≤Real.logb Z ((newtonDivisorPair S A).1.absNorm:ℝ):=Real.logb_nonneg hZ (norm_ge_one _ hdpair.1)
  have hd₂:0≤Real.logb Z ((newtonDivisorPair S A).2.absNorm:ℝ):=Real.logb_nonneg hZ (norm_ge_one _ hdpair.2.1)
  have hcost':(∑i∈T\select,w i)≤max 0 (max
      (b-f-((low.B:ℝ)*Q-(plainBudget n b width-c+f+loss))/(low.L:ℝ))
      (b-f-(low.cap:ℝ)*Q))+mesh:=by
    have hd:=div_le_div_of_nonneg_right
      (show (low.B:ℝ)*Q-(plainBudget n b width-c+f+loss)≤
        (low.B:ℝ)*Q-(plainBudget n b width-c+f+loss-Real.logb Z ((newtonDivisorPair S A).1.absNorm:ℝ)-
          Real.logb Z ((newtonDivisorPair S A).2.absNorm:ℝ)) by linarith only [hd₁,hd₂]) hL.le
    have hdiff:b-f-((low.B:ℝ)*Q-(plainBudget n b width-c+f+loss-
        Real.logb Z ((newtonDivisorPair S A).1.absNorm:ℝ)-Real.logb Z ((newtonDivisorPair S A).2.absNorm:ℝ)))/(low.L:ℝ)≤
        b-f-((low.B:ℝ)*Q-(plainBudget n b width-c+f+loss))/(low.L:ℝ):=by linarith only [hd]
    exact hcost.trans (add_le_add (max_le_max le_rfl (max_le_max hdiff le_rfl)) le_rfl)

  have hp:=modified_node_price Kgraph n low b hg hn hlow ha hq0 hq1
    α s Am₁ Am₂ Dm Km R seed Fm H Z ξ hH bin j reflected second datum U
    M (Real.logb Z (volume s)) reserve width err errv c f loss rho mesh
    (∑i∈T\select,w i) Q radialRound outer hZ hwidth0 hwidth hloss0 hrho0 hrho hloss hmesh
    herr herrv hround houter hc hf hcost' hrad
  refine ⟨select,hselect,?_⟩
  intro corner A₁ A₂ hA₁ hA₂ hAR havoid η height z
  rcases hcorner corner A₁ A₂ hA₁ hA₂ hAR havoid η height z with hz|⟨hfloor,hadmit⟩
  · exact Or.inl hz
  · exact Or.inr ⟨hfloor,hadmit,hp⟩

end
end QRH.Record1252270103Source.Admission.SelectedLowPaid
#print axioms QRH.Record1252270103Source.Admission.SelectedLowPaid.actual_selected_low_price
