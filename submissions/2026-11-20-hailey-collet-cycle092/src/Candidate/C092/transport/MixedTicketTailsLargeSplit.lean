/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original coefficient packet restricted by its actual max-one dilation. -/
import Candidate.C092.transport.MixedTicketTailsLargeLabel
import Candidate.C092.transport.SelectedNonfloorPacket
import Candidate.C092.transport.SelectedNonfloorFront
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open Cycle25.Numerator Cycle25.Weighted Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
namespace QRH.Cycle092.MixedTicketTails
local notation "O" => HeckeFamily.O
variable [Geometry.Parameters]

def smallLabelPolynomialPacket {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Yp : ι→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y Cu Ccond U vcut : ℝ) : ℂ :=
  let weight : ∀i,T i→ℂ := fun i P=>physicalSlotWeight P.val (W i) (Yp i) z
  (Y:ℂ)^(-(1/2:ℂ))*∑'e:LabelPacketIndex S u T,
    labelPacketCoefficient S hS η u T hT weight x z e*(labelPacketScale S u T e:ℂ)^(-(1/2:ℂ))*
    (if U^vcut ≤ max 1 ((Cu/(Ccond*rowNorm u))*(labelPacketScale S u T e:ℝ)) then 0 else
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W1
        (Y/(labelPacketScale S u T e:ℝ)) 0 0)

/-- The excluded large packet is an exact piece of the ORIGINAL error packet.
The actual unfiltered series proves absolute convergence of both pieces. -/
theorem actual_original_coefficient_split (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow)
    (data : PhysicalReflectionData F.S F.exclusions.prime u)
    (Z alpha : ℝ) (x z : ℂ) (Y U vcut : ℝ)
    (hrow : (rowCharacter F.S F.exclusions.prime u).residue≠1)
    (ha : 51/100≤alpha) (hx : x.re=alpha+16*D.e) (hz : z.re=17/50) (hY : 0<Y) :
    QRH.Cycle092.SelectedNonfloor.errorPacket D F J η u Z x z Y =
      smallLabelPolynomialPacket F.S F.exclusions η u
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W Y data.combinedConductor
        (ProbeRowRadicalConductor.fixedConductorConstant F.S) U vcut+
      largeLabelPolynomialPacket F.S F.exclusions η u
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W Y data.combinedConductor
        (ProbeRowRadicalConductor.fixedConductorConstant F.S) U vcut := by
  let T := fun k:J=>sourcePrimePool F Z k.val
  let weight : ∀k,T k→ℂ := fun k P=>physicalSlotWeight P.val F.W (Z^(D.length k.val)) z
  let A := labelPacketCoefficient F.S F.exclusions η u T
    (fun k=>source_prime_pool_outside F Z k.val) weight x z
  let N (e:LabelPacketIndex F.S u T) : ℝ := labelPacketScale F.S u T e
  let gate (e:LabelPacketIndex F.S u T) : Prop := U^vcut ≤ max 1
    ((data.combinedConductor/((ProbeRowRadicalConductor.fixedConductorConstant F.S:ℝ)*rowNorm u))*N e)
  let full (e:LabelPacketIndex F.S u T) := A e*(N e:ℂ)^(-(1/2:ℂ))*
    HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime u) false F.W (Y/N e) 0 0
  let small (e:LabelPacketIndex F.S u T) := A e*(N e:ℂ)^(-(1/2:ℂ))*
    (if gate e then 0 else HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime u) false F.W (Y/N e) 0 0)
  let large (e:LabelPacketIndex F.S u T) := A e*(N e:ℂ)^(-(1/2:ℂ))*
    (if gate e then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime u) false F.W (Y/N e) 0 0 else 0)
  have hsFull : Summable (fun e=>‖full e‖) :=
    actual_label_series_norm_summable F.S F.exclusions (4*D.e) F.first η u hrow T
      (fun k=>source_prime_pool_outside F Z k.val) weight x z
      (by linarith [D.e_pos]) hz.ge (by linarith [D.e_pos]) F.W 1 2
      (by norm_num) F.complex_support (F.W.smooth ⊤) Y hY
  have hsSmall : Summable (fun e=>‖small e‖) := by
    apply hsFull.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro e
    dsimp only [small]
    split_ifs
    · simp only [mul_zero,norm_zero];exact norm_nonneg _
    · exact le_rfl
  have hsLarge : Summable (fun e=>‖large e‖) := by
    apply hsFull.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro e
    dsimp only [large]
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero];exact norm_nonneg _
  have he (e:LabelPacketIndex F.S u T) : full e=small e+large e := by
    dsimp only [full,small,large]
    split_ifs <;> simp only [mul_zero,zero_add,add_zero]
  have hsum : (∑'e,full e)=(∑'e,small e)+(∑'e,large e) := by
    simp_rw [he]
    exact hsSmall.of_norm.tsum_add hsLarge.of_norm
  unfold QRH.Cycle092.SelectedNonfloor.errorPacket labelPolynomialPacket smallLabelPolynomialPacket largeLabelPolynomialPacket
  rw [←mul_add]
  congr 1
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.actual_original_coefficient_split
