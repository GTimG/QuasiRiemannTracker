/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary ticket classes consume the genuine common source event. -/
import Candidate.C092.transport.RegularColoredTerminalLeafMediumActual
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafMediumUniform_1ef20a545b4d244b_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {kernel : ℝ→ℂ}

/-- The finite genuine source coefficient envelope is fixed after I/Cslot,
before U, surviving subsets, cofactor radii, rows and profiles. -/
def terminalMediumEnvelope (L : LateBundle P G m0 gap kernel) (I : ℕ) (Cslot : ℝ) : ℝ :=
  1+∑q : Finset Slot×dBank,
    (terminalOrdinaryCost L q.1 q.2 I Cslot+∑k : WindowKey table,terminalInverseCost L q.1 q.2 k I Cslot)

theorem terminal_ordinary_cost_nonneg (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (I : ℕ) (Cslot : ℝ) : 0≤terminalOrdinaryCost L T db I Cslot := by
  have hC4 := (L.sources.ordinary T db).C4_pos
  have hCs := (P.ordinary.positive T).1
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  unfold terminalOrdinaryCost
  positivity

theorem terminal_medium_envelope_bounds (L : LateBundle P G m0 gap kernel) (I : ℕ)
    {Cslot : ℝ} (hCslot : 0≤Cslot) :
    0<terminalMediumEnvelope L I Cslot ∧ ∀(T : Finset Slot) (db : dBank),
      terminalOrdinaryCost L T db I Cslot+∑k : WindowKey table,terminalInverseCost L T db k I Cslot≤
        terminalMediumEnvelope L I Cslot := by
  have hn (q : Finset Slot×dBank) : 0≤terminalOrdinaryCost L q.1 q.2 I Cslot+
      ∑k : WindowKey table,terminalInverseCost L q.1 q.2 k I Cslot :=
    add_nonneg (terminal_ordinary_cost_nonneg L q.1 q.2 I Cslot)
      (Finset.sum_nonneg (fun k _=>(terminal_inverse_cost_bounds L q.1 q.2 k I hCslot).1))
  have hs := Finset.sum_nonneg (s:=Finset.univ) (fun q _=>hn q)
  refine ⟨by unfold terminalMediumEnvelope;linarith,?_⟩
  intro T db
  have h := Finset.single_le_sum (f:=fun q : Finset Slot×dBank=>terminalOrdinaryCost L q.1 q.2 I Cslot+
    ∑k : WindowKey table,terminalInverseCost L q.1 q.2 k I Cslot) (fun q _=>hn q) (Finset.mem_univ (T,db))
  unfold terminalMediumEnvelope
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem terminal_uniform_medium_source_at (L : LateBundle P G m0 gap kernel)
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
        terminalMediumEnvelope L I Cslot*
        U^(terminalFramePrice V) := by
  have h := terminal_actual_medium_source_at L hAt T db D ht0 hy0 hy1 hyn hn hdmin hdb hdb' hV hVd hdV
    hsupply hY hR hmesh hmeshGap hgap hgap1 hm0 hCslot hb hwidth heps hloss0 hloss hprice hpriceFee
    hconductor hcapFee hwitnessFee hsourceFee hbufferFee hheightFee hmeshInverse hconductorInverse hbufferInverse hepsilonInverse
    dyadLoss K hK hcard hInvLoss hDyad p
  apply h.trans
  have hc := (terminal_medium_envelope_bounds L I (L.CslotFloor_pos.trans_le hCslot).le).2 T db
  have hU0 : 0<U := zero_lt_one.trans hAt.one
  gcongr

#print axioms terminal_uniform_medium_source_at
#print axioms terminal_medium_envelope_bounds
end
end QRH.Cycle092.RegularColoredForward
