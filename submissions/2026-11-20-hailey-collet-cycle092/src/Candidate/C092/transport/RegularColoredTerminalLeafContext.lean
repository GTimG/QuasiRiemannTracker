/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.P2CommonSourceMetadataFinal
import Candidate.C092.transport.RegularColoredTerminalLeafOccupied
import Candidate.C092.transport.RegularColoredTerminalLeafLengths
import Candidate.C092.transport.RegularColoredTerminalLeafHomogeneous
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafContext_1e8e5615224a1ac5_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

structure TerminalTicketContext (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M)
    {dmin dmax : ℝ} {dBank : Finset ℝ} (G : LateGeometry dmin dmax dBank) (db : dBank)
    (n y mesh buffer price U V Cslot : ℝ) (I : ℕ) {step : ℝ} {cell : Cell}
    (table : TerminalResponseTable y step cell) where
  rows : Finset FreeRow
  state : NaturalState U G.Bmask A.bΦ
  width_bound : state.width  ≤  G.Mcap db
  character : state.character=A.ηShort
  puncture : state.puncture=1
  modulus_ray : state.fixedModulus ≤ M
  modulus_base : state.fixedModulus ≤ A.baseShort.modulus
  keep : ∀u∈rows,state.radial.keep u.val
  keep_equiv : ∀z : O,state.radial.keep z ↔ initialKeep state.character (internalQ A.QShort A.baseShort) z
  plateau : ∀u∈rows,state.radial.profile (‖eisEmbedding u.val‖^2/state.radial.scale)≠0
  row_norm : ∀u∈rows,rowNorm u ≤ U^V
  long_keep : ∀u∈rows,initialKeep A.ηLong (internalQ A.QLong A.baseLong) u.val
  theta : Slot→RayQuotient.Characters M A.Hr
  thetaLong : Slot→RayQuotient.Characters M A.Hr
  w : Slot→ℝ
  v : Slot→ℝ
  vLong : Slot→ℝ
  tShort : ℝ
  tLong : ℝ
  height : ℝ
  height_nonneg : 0 ≤ height
  pitch : ∀j,|v j| ≤ height
  pitchLong : ∀j,|vLong j| ≤ height
  native_height : |tShort|+|tLong|+2*height ≤ U^G.τ
  width_nonneg : ∀j,0 ≤ w j
  width_mesh : ∀j,w j ≤ mesh
  width_sum : (∑j,w j) ≤ sourceWidth n y-(u:ℝ)
  physical : Slot→FreeRow→ℂ
  short_presentation : ∀z∈rows,∀j,‖physical j z‖=
    ‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U theta w v tShort z j‖
  long_presentation : ∀z∈rows,∀j,
    ‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W U theta w v tShort z j‖=
    ‖descriptor M A.Hr A.hHr A.ηLong A.baseLong A.W U thetaLong w vLong tLong z j‖
  X : ℝ
  Y : ℝ
  long_positive : 0 < X
  short_positive : 0 < Y
  long_cap : X ≤ U^n
  short_cap : Y ≤ U^y
  ticket : ∀z : rows,RowTicket
    (family M A.Hr A.hHr state A.baseShort (naturalRow state.character z.val.val z.val.property.1))
    (family_nonprincipal M A.Hr A.hHr state A.baseShort modulus_ray modulus_base (keep z.val z.property)
      (naturalRow state.character z.val.val z.val.property.1))
    U db.val dmax G.τ G.ε G.ez price
    (measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) theta w v tShort z.val) I
  window : rows→Fin table.Je×Fin table.Jν
  witness : ∀z : rows,SupportedWitness
    (family M A.Hr A.hHr state A.baseShort (naturalRow state.character z.val.val z.val.property.1))
    (U^db.val) ((51/100:ℝ)+G.ez*(ticket z).level.val) G.ε
    (totalCutoff (table.cutoff (window z))) (U^G.τ) ((U^db.val)^(G.τ/(2*dmax))) (ticket z).band.val
  window_bound : ∀z : rows,
    table.egrid (window z).1 ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) theta w v tShort z.val ∧
    measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) theta w v tShort z.val < table.egrid (window z).1+step ∧
    max (table.egrid (window z).1) (table.νgrid (window z).2) ≤ 2*((51/100:ℝ)+G.ez*(ticket z).level.val)-1+price ∧
    2*((51/100:ℝ)+G.ez*(ticket z).level.val)-1 < max (table.egrid (window z).1) (table.νgrid (window z).2)+step

namespace TerminalTicketContext
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {dmin dmax : ℝ} {dBank : Finset ℝ} {G : LateGeometry dmin dmax dBank} {db : dBank}
variable {n y mesh buffer price U V Cslot : ℝ} {I : ℕ} {step : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y step cell}

abbrev Key (_ : TerminalTicketContext Slot M A G db n y mesh buffer price U V Cslot I table) :=
  Fin (I+1)×Fin (⌊(73/200:ℝ)/G.ez⌋₊+1)×(Fin table.Je×Fin table.Jν)×
    Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
    Fin (dyadicLength (U^db.val))×Fin (dyadicLength (U^db.val))

def key (D : TerminalTicketContext Slot M A G db n y mesh buffer price U V Cslot I table) : D.rows→D.Key :=
  terminalWitnessKey (fun z=>(D.ticket z).band) (fun z=>(D.ticket z).level) D.window
    (fun k=>totalCutoff (table.cutoff k)) D.witness

def fiber (D : TerminalTicketContext Slot M A G db n y mesh buffer price U V Cslot I table) (tag : D.Key) : Finset FreeRow :=
  classRows D.rows D.key tag

end TerminalTicketContext
end
end QRH.Cycle092.RegularColoredForward
