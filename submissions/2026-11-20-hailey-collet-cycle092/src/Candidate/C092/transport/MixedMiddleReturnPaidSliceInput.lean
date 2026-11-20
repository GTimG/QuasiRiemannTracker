/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original-mask/common-subclass middle guards; no count or moment field. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceFinite
import Candidate.C092.transport.MixedMiddleReturnPaidSliceEnvelope
import Candidate.C092.transport.MixedMiddleReturnPrimeFront
set_option autoImplicit false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor HeckeDetectorRawFiber HeckeDetectorPhysicalSelection
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.MixedOffsetCount QRH.Cycle090
attribute [local reducible] BaselineData.toMomentData
variable [Geometry.Parameters]

/-- The original OLD small packet, with all original coefficient labels and
all error-prime slots, before finite box reconstruction. -/
def paidOriginalSmall (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (Z : ℝ) (x z : ℂ)
    (Y U : ℝ) (r : TopData.Row) (u : FreeRow)
    (data : PhysicalReflectionData F.S F.exclusions.prime u) : ℂ :=
  MixedTicketTails.smallLabelPolynomialPacket F.S F.exclusions η u
    (fun k : J=>sourcePrimePool F Z k.val) (fun k=>source_prime_pool_outside F Z k.val)
    (fun _=>F.W) (fun k=>Z^(D.length k.val)) x z F.W Y data.combinedConductor
    (fixedConductorConstant F.S) U (MixedTicketTails.originalVcut r)

/-- These are physical/event guards on an actual native bank. In particular,
this record contains neither a row cardinality nor a source/moment estimate.
The source hull, tuple window, lower dilation and box count are derived. -/
structure PaidSliceInput (h decrement epsilon xi ann loss massEps sourceMesh wmin : ℝ)
    (reverse : Bool) (D : BaselineData) (F : BaselineSourceData D) (J : Finset (Fin D.N))
    (η : Character) (Z : ℝ) where
  bank : MiddleBank D.toMomentData F η Z
  r : TopData.Row
  row : r∈TopData.rows
  point : r.box.Contains (bank.delta,bank.p)
  d_min : (1/100:ℝ) ≤ bank.d
  d_old : MixedTicketTails.originalDlow r ≤ bank.d
  d_max : bank.d ≤ h+rowPad
  d_hi : bank.d ≤ 7/8
  gamma : bank.γ=(Mixed.rowGamma r.box r.B:ℝ)
  collar : bank.εa=witnessCollar
  factor : bank.factor=(Mixed.rowV r.box:ℝ)/(r.box.uHi:ℝ)
  offset_nonneg : 0 ≤ bank.xi
  offset_max : bank.xi ≤ (Mixed.rowGamma r.box r.B:ℝ)
  reverse_eq : bank.currentSlice.fiber.reverse=reverse
  T_nonneg : 0 ≤ bank.T
  allowance_nonneg : 0 ≤ bank.allowance
  height_bound : 1+bank.height ≤ bank.baseScale
  current_slots : bank.currentSlice.fiber.slots=Finset.univ
  base_slots : bank.base.batch.slots=Finset.univ
  base_bin : bank.base.batch.binWidth=D.t
  fine : bank.currentSlice.fiber.mesh ≤ sourceMesh
  widths : ∀s∈bank.currentSlice.fiber.slots,wmin ≤ bank.currentSlice.fiber.widths s
  row_lower : ∀u∈bank.currentSlice.fiber.rows,Z^(1/100:ℝ) ≤ rowNorm u
  row_upper : ∀u∈bank.currentSlice.fiber.rows,rowNorm u ≤ bank.baseScale
  ordinary_min : Mixed.widthLo ≤ bank.currentSlice.fiber.m
  ordinary_max : bank.currentSlice.fiber.m ≤ Mixed.widthHi
  x : ℂ
  z : ℂ
  x_re : x.re=bank.a+16*D.e
  z_re : z.re=17/50
  external_eq : bank.current.batch.external=(fun _=>z)
  data : ∀u : bank.currentSlice.fiber.rows,PhysicalReflectionData F.S F.exclusions.prime u.val
  nonprincipal : ∀u∈bank.currentSlice.fiber.rows,(rowCharacter F.S F.exclusions.prime u).residue≠1
  margin : 1+4*D.e ≤ x.re+1/2
  slot_upper : ∀u∈bank.common,∀s∈(Finset.univ\J),
    ‖physical F.modulus ⊤ (fun w : FreeRow=>w.val) bank.currentSlice.fiber.profile
      bank.currentSlice.fiber.upper bank.currentSlice.fiber.widths bank.currentSlice.fiber.external
      bank.baseScale u s‖ ≤ bank.baseScale^(bank.currentSlice.fiber.widths s*
        (bank.currentSlice.fiber.bin s+bank.currentSlice.fiber.binWidth))
  outerFee : ℝ
  fee_paid : bank.d*((2*bank.a-1)*bank.p*decrement+
    bank.currentSlice.fiber.binWidth*(∑s∈bank.currentSlice.fiber.slots,bank.currentSlice.fiber.widths s)+
    (2*bank.a-1)*bank.currentSlice.fiber.mesh/2+D.ε+(bank.loss+epsilon+loss)/2+massEps)+outerFee
      ≤ paddingDebit+(1/100000000000000:ℝ)

end
end QRH.Cycle092.MixedMiddleReturn
