/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary ticket classes consume the genuine common source event. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOrdinaryActual
import Candidate.C092.transport.P2InverseTicketDispatchActual
import Candidate.C092.transport.RegularColoredTerminalLeafAggregate
import Candidate.C092.transport.StrongPairRegularTerminalReserve
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafMediumActual_d2f1445cac903bd7_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {kernel : ℝ→ℂ}

theorem terminal_actual_medium_source_at (L : LateBundle P G m0 gap kernel)
    {U V Cslot CLo mesh conductor : ℝ} {I : ℕ}
    (hAt : AtAll P G L.Bshort m0 gap L.sources I Cslot CLo U)
    (T : Finset Slot) (db : dBank)
    (D : TerminalTicketContext T M A G db n y mesh buffer price U V Cslot I table)
    (ht0 : 0 < (cell.threshold:ℝ))
    (hy0 : sourceY0  ≤  y) (hy1 : y  ≤  sourceY) (hyn : y  ≤  n) (hn : n  ≤  sourceRatio*y)
    (hdmin : 0  <  dmin) (hdb : dmin  ≤  db.val) (hdb' : db.val  ≤  dmax)
    (hV : (98/100:ℝ)  ≤  V) (hVd : V  ≤  db.val) (hdV : db.val  ≤  V+3*conductor)
    (hsupply : G.Mcap db+G.Bmask+G.margin  ≤  db.val)
    (hY : 1  ≤  D.Y) (hR : y/dmin  ≤  G.R)
    (hmesh : mesh  ≤  dmin*ordinaryMesh) (hmeshGap : mesh  ≤  gap)
    (hgap : 0  ≤  gap) (hgap1 : gap  ≤  1)
    (hm0 : ∀k,m0  ≤  ((table.cutoff k).ordinary:ℝ))
    (hCslot : L.CslotFloor  ≤  Cslot) (hb : 0  ≤  buffer)
    (hwidth : sourceWidth n y-(u:ℝ)  ≤  1)
    (heps : G.ε  ≤  1/7500) (hloss0 : 0  ≤  loss) (hloss : loss  ≤  (rho:ℝ)/64)
    (hprice : 0  ≤  price) (hpriceFee : price*dmax  ≤  loss/4)
    (hconductor : 3*conductor  ≤  (rho:ℝ)/128)
    (hcapFee : (responseUpper:ℝ)*(dmax*(2*gap)+dmax*gap+gap)  ≤  (rho:ℝ)/128)
    (hwitnessFee : (15/4:ℝ)*dmax*G.ε  ≤  (rho:ℝ)/128)
    (hsourceFee : dmax*εsource  ≤  (rho:ℝ)/128)
    (hbufferFee : buffer*(Fintype.card Slot:ℝ)  ≤  (rho:ℝ)/128)
    (hheightFee : G.τ*(P.degreeBound:ℝ)  ≤  (rho:ℝ)/128)
    (hmeshInverse : mesh≤dmin*B.mesh) (hconductorInverse : conductor≤loss/10)
    (hbufferInverse : buffer*(Fintype.card Slot:ℝ)≤B.feeFloor/1000)
    (hepsilonInverse : (dmax+1)*G.ε≤B.feeFloor/1000)
    (dyadLoss K : ℝ) (hK : 0≤K)
    (hcard : (Fintype.card D.Key:ℝ)≤K*U^dyadLoss)
    (hInvLoss : loss+heightLoss≤(rho:ℝ)/8) (hDyad : dyadLoss<(rho:ℝ)/8)
    (p : Profiles (1/4) (9/4)) :
    finiteEnergyOn Finset.univ D.rows A.ηLong D.state.character
      (p.profile 0) (p.profile 1) D.tLong D.tShort D.X D.Y D.physical≤
      K*L.normalizationConstant^4*(p.control L.controlsBound)^2*
        (terminalOrdinaryCost L T db I Cslot+∑k : WindowKey table,terminalInverseCost L T db k I Cslot)*
        U^(terminalFramePrice V) := by
  classical
  have hU0 : 0<U := zero_lt_one.trans hAt.one
  have hCslot0 : 0<Cslot := L.CslotFloor_pos.trans_le hCslot
  let Co := terminalOrdinaryCost L T db I Cslot
  let Ci := ∑k : WindowKey table,terminalInverseCost L T db k I Cslot
  let F := L.normalizationConstant^4*(p.control L.controlsBound)^2
  let common := terminalFramePrice V-dyadLoss
  have hCo : 0≤Co := by
    have hC4 := (L.sources.ordinary T db).C4_pos
    have hCs := (P.ordinary.positive T).1
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    dsimp [Co,terminalOrdinaryCost]
    positivity
  have hCi : 0≤Ci := Finset.sum_nonneg (fun k _=>(terminal_inverse_cost_bounds L T db k I hCslot0.le).1)
  have hF : 0≤F := by dsimp [F];positivity
  have hCost : 0≤F*(Co+Ci) := mul_nonneg hF (add_nonneg hCo hCi)
  have hres := terminal_branch_reserves (V:=V) hInvLoss hDyad
  have hbase : V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)≤common := by
    dsimp only [common]
    linarith [hres.1]
  have hinv : V+radialAllowance V+loss+heightLoss≤common := by
    dsimp only [common]
    linarith [hres.2]
  have hypos : 0≤y := by
    have h : (0:ℝ) ≤ sourceY0 := by norm_num [sourceY0]
    linarith
  have hnpos : 0≤n := hypos.trans hyn
  have hclass (tag : D.Key) : finiteEnergyOn Finset.univ (D.fiber tag) A.ηLong D.state.character
      (p.profile 0) (p.profile 1) D.tLong D.tShort D.X D.Y D.physical≤F*(Co+Ci)*U^common := by
    by_cases hoccupied : (D.fiber tag).Nonempty
    · by_cases hord : Real.logb (U^db.val) ((2:ℝ)^tag.2.2.2.2.1.val)<((table.cutoff tag.2.2.1).inverse:ℝ)
      · have h := terminal_actual_ordinary_source_at L hAt T db D tag hoccupied hord ht0.le
          hy0 hy1 hyn hn hdmin hdb hdb' hV hVd hdV hsupply hY hR hmesh hmeshGap hgap hgap1 hm0 hCslot hb
          hwidth heps hloss0 hloss hprice hpriceFee hconductor hcapFee hwitnessFee hsourceFee hbufferFee hheightFee p
        have hprof := (L.profile_payments p).2.2.2 T db
        apply h.trans
        calc
          _ ≤ F*Co*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprof hCo) (Real.rpow_nonneg hU0.le _)
          _ ≤ F*Co*U^common := by gcongr;exact hAt.one.le
          _ ≤ F*(Co+Ci)*U^common := by gcongr;exact le_add_of_nonneg_right hCi
      · have h := terminal_actual_inverse_source_at L hAt T db D tag hoccupied (le_of_not_gt hord)
          ht0 hypos hnpos hdmin hdb hdb' hV hVd
          (by have he:=mul_le_mul_of_nonneg_left hconductorInverse (by norm_num : (0:ℝ)≤3);linarith)
          hsupply hR hmeshInverse hCslot0 hb hwidth heps hloss0 hbufferInverse hepsilonInverse p
        have hprof := (L.profile_payments p).2.2.1
        have hCk := (terminal_inverse_cost_bounds L T db tag.2.2.1 I hCslot0.le).1
        have hCkCi : terminalInverseCost L T db tag.2.2.1 I Cslot≤Ci :=
          Finset.single_le_sum (fun k _=>(terminal_inverse_cost_bounds L T db k I hCslot0.le).1) (Finset.mem_univ _)
        apply h.trans
        calc
          _ ≤ F*terminalInverseCost L T db tag.2.2.1 I Cslot*U^(V+radialAllowance V+loss+heightLoss) := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprof hCk) (Real.rpow_nonneg hU0.le _)
          _ ≤ F*terminalInverseCost L T db tag.2.2.1 I Cslot*U^common := by gcongr;exact hAt.one.le
          _ ≤ F*(Co+Ci)*U^common := by
            gcongr
            exact hCkCi.trans (le_add_of_nonneg_left hCo)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hoccupied]
      simp only [finiteEnergyOn,Finset.sum_empty]
      exact mul_nonneg hCost (Real.rpow_nonneg hU0.le _)
  have hpart := terminal_class_energy_partition Finset.univ D.rows D.key A.ηLong D.state.character
    (p.profile 0) (p.profile 1) D.tLong D.tShort D.X D.Y D.physical
  rw [hpart]
  calc
    _ ≤ ∑tag : D.Key,F*(Co+Ci)*U^common := by
      apply Finset.sum_le_sum
      intro tag _
      exact hclass tag
    _ = (Fintype.card D.Key:ℝ)*(F*(Co+Ci)*U^common) := by simp
    _ ≤ (K*U^dyadLoss)*(F*(Co+Ci)*U^common) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hCost (Real.rpow_nonneg hU0.le _))
    _ = _ := by
      have he : dyadLoss+common=terminalFramePrice V := by dsimp only [common];ring
      rw [←mul_assoc,←mul_assoc]
      calc
        _ = K*F*(Co+Ci)*U^(dyadLoss+common) := by rw [Real.rpow_add hU0];ring
        _ = _ := by rw [he];dsimp only [F,Co,Ci];ring

#print axioms terminal_actual_medium_source_at
end
end QRH.Cycle092.RegularColoredForward
