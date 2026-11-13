/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Source-specific physical label-packet bound at variable positive source cost.
Adapted from PR137 SelectedBin (Sil and predecessor authors, Apache-2.0).
The selected moment is supplied by the actual active-box fourth moment. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveActive
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveLabelPacket
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.SelectedBin

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical
open HeckeFamily HeckeInverseAmplification ProbeRowRadicalConductor Cycle25DetectorRowCount
local notation "O" => HeckeFamily.O
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- The literal source packet is bounded with its selected moment fully
supplied; only its physical row count and selected whole-slot amplitudes are
inputs to this local dyad estimate. -/
theorem selected_source_packet_with_cost (A : ChosenData) {cost : ℝ}
    (hcost : 0 ≤ cost) (hcostmax : cost ≤ 1/1000000000)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ A.D.momentKappa)
    (bPhi error : ℝ) (haff : 0 < error)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop,
      affineAtFace (PositiveSource.physicalFace cost) A bPhi error U di control Ci)
    (J : Finset (Fin A.D.N)) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ Z d : ℝ, 1 < Z → (3/4:ℝ) ≤ d → d ≤ 2*Geometry.y → U = Z^d →
      ∀ (η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ) ≤ a → a ≤ 7/8 →
      x.re = a+16*A.D.e → z.re = 17/50 → 0 ≤ height → |z.im| ≤ height →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      (∀ u ∈ rows, (rowCharacter A.F.S A.F.exclusions.prime u).residue ≠ 1) →
      (∀ P : ∀ i : J, sourcePrimePool A.F Z i.val, Function.Injective (fun i => (P i).val)) →
      (∀ i P, P ∈ sourcePrimePool A.F Z i → IsCoprime P.val η.modulus) →
      (∀ i : J, sourcePrimePool A.F Z i.val) →
      ∀ (selected : ℕ → Finset (Fin A.D.N)) (P : rows → ℂ) (q R selLoss Ccount : ℝ),
      0 ≤ q → q ≤ (2*a-1)/2 → 1 ≤ Ccount → (rows.card : ℝ) ≤ Ccount*U^R →
      (∀ i, ‖P i‖ ≤ U^(q*(Geometry.ell/d))) →
      (∀ j ∈ Finset.range (coefficientBoxCount A.D.t+1),
        (∑ k ∈ selected j, A.D.length k/d) ≤
          Selection.scheduledCapacity cost d (2*((j:ℝ)*A.D.t+A.D.t+A.D.t))) →
      (∀ j ∈ Finset.range (coefficientBoxCount A.D.t+1), ∀ i : rows,
        U^(q*Selection.scheduledCapacity cost d (2*((j:ℝ)*A.D.t+A.D.t+A.D.t))-selLoss) ≤
          ‖∏ k ∈ selected j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
            A.F.W 2 (Z^(A.D.length k)) z‖) →
      (∀ j ∈ Finset.range (coefficientBoxCount A.D.t+1), ∀ i : rows,
        ‖∏ k ∈ selected j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
          A.F.W 2 (Z^(A.D.length k)) z‖ ≤ U) →
      (∑ i : rows, ‖labelPolynomialPacket A.F.S A.F.exclusions η i.val
        (fun k : J => sourcePrimePool A.F Z k.val) (fun k => source_prime_pool_outside A.F Z k.val)
        (fun _ => A.F.W) (fun k => Z^(A.D.length k.val)) x z A.F.W (U^(Geometry.y/d))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*
          (∏ k : J, (Z^(A.D.length k.val))^(-(4/25:ℝ)))*
          U^(A.D.t+q*(Geometry.ell/d)-q*Selection.zeroCapacity cost d/2+
            (3*R+1+A.D.t+error+A.D.t)/4+selLoss/2+(2*a-1)*(A.D.t+A.D.t)/2) := by
  obtain ⟨Cm,hCm,hpacket⟩ := label_packet_bin_bound (ι := J) A.D.t 1 2 1 A.D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*A.D.t+A.D.t ≤ (1/2:ℝ) := by linarith [A.D.t_small]
  obtain ⟨degree,Cr,hCr,hmoment⟩ := active_box_fourth_with_cost A hcost hcostmax A.D.momentKappa
    A.D.momentKappa_lo A.D.momentKappa_hi hkbeta hbeta bPhi error haff hsPhi di control Ci hCi hinput
    A.F.W A.D.t A.D.t A.D.t 2 A.D.t_pos A.D.t_pos A.D.t_pos (by norm_num) hsmall
  let Cr' := max 1 Cr
  have hCr' : 1 ≤ Cr' := le_max_left _ _
  let C := ((coefficientBoxCount A.D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C]; have hh := zero_lt_one.trans_le hCr'; positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := by linarith
  have hdhalf : (1/2:ℝ) ≤ d := by linarith
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hmom.1
  have hscale (k : Fin A.D.N) : U^(A.D.length k/d) = Z^(A.D.length k) := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  let data (i : rows) : PhysicalReflectionData A.F.S A.F.exclusions.prime i.val :=
    Classical.choice (physical_reflection_data_exists A.F.S A.F.exclusions.prime i.val (hrow i.val i.property))
  let Cu (i : rows) := (data i).combinedConductor
  let Ccond : ℝ := fixedConductorConstant A.F.S
  have hCcond : 0 < Ccond := by
    dsimp only [Ccond]
    exact_mod_cast fixedConductorConstant_pos A.F.S A.F.exclusions.prime
  let Ts (k : J) := sourcePrimePool A.F Z k.val
  let hTs := fun k : J => source_prime_pool_outside A.F Z k.val
  let Q (j : ℕ) (i : rows) := ∏ k ∈ selected j,
    HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W 2 (Z^(A.D.length k)) z
  have hQprod (j : ℕ) (i : rows) :
      (∏ k : selected j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W
        2 (U^(A.D.length k.val/d)) z) = Q j i := by
    calc
      _ = ∏ k : selected j, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val
          A.F.W 2 (Z^(A.D.length k.val)) z := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [hscale k.val]
      _ = _ := Finset.prod_coe_sort (selected j)
        (fun k => HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ i.val.val A.F.W 2 (Z^(A.D.length k)) z)
  have hwpos (k : Fin A.D.N) : 0 < A.D.length k/d := div_pos (A.D.slots_pos k) hd0
  have hwmax (k : Fin A.D.N) : A.D.length k/d ≤ Cycle25.sourceMesh A.D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := Cycle25.sourceMesh_pos A.D.t_pos
    have hh := A.fine k
    nlinarith
  have hYp (k : J) : 1 ≤ Z^(A.D.length k.val) := Real.one_le_rpow hZ.le (A.D.slots_pos k.val).le
  have hY : 0 < U^(Geometry.y/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(Geometry.y/d) ≤ U^((coefficientBoxCount A.D.t:ℝ)*A.D.t) := by
    apply (hcutU.2 d hd).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le
      (coefficientBoxCount_extent A.D.t A.D.t_pos).1
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := source_packet_lines A.D a ha hatop
  have hmomentInput (j : ℕ) (hj : j ∈ Finset.range (coefficientBoxCount A.D.t+1))
      (e : ∀ i : rows, LabelPacketIndex A.F.S i.val Ts) :
      (∑ i : rows, ‖if (labelPacketScale A.F.S i.val Ts (e i):ℝ) ≤ 2*U^(Geometry.y/d) ∧
        dilationBox U A.D.t (coefficientBoxCount A.D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale A.F.S i.val Ts (e i):ℝ))) = j
        then HeckeDyadic.polynomial (rowCharacter A.F.S A.F.exclusions.prime i.val) false A.F.W
          (U^(Geometry.y/d)/(labelPacketScale A.F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+A.D.t+error+A.D.t) := by
    have hh := hmom.2 rows hrows data (fun i => (labelPacketScale A.F.S i.val Ts (e i):ℝ))
      (fun i => zero_lt_one.trans_le (by exact_mod_cast labelPacketScale_one_le A.F.S i.val Ts (e i)))
      d hd hdmax j hj (selected j) (fun k => A.D.length k.val/d) (fun _ => z) height
      (fun k => hwpos k.val)
      (fun k => rescaled_slot_mesh A.D.length A.sourceMesh d (by linarith only [hdhalf])
        (by have hpos := A.D.slots_pos k.val; have hlen := A.source_fine k.val; linarith)
        A.source_fine k.val)
      (fun k => hwmax k.val) (fun _ => hz) hheight (fun _ => hzim)
      ((Finset.sum_coe_sort (selected j) (fun k => A.D.length k/d)).le.trans (hcap j hj))
      (by intro i; rw [hQprod]; exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+A.D.t+error+A.D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale A.F.S i.val Ts (e i):ℝ) ≤ 2*U^(Geometry.y/d) ∧
      dilationBox U A.D.t (coefficientBoxCount A.D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale A.F.S i.val Ts (e i):ℝ))) = j
      then HeckeDyadic.polynomial (rowCharacter A.F.S A.F.exclusions.prime i.val) false A.F.W
        (U^(Geometry.y/d)/(labelPacketScale A.F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm
  have hCM : 1 ≤ Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket A.F.S A.F.exclusions (4*A.D.e) A.F.first η Ts hTs hdis
    (fun k Q hQ => hη k.val Q hQ) Pbase (fun _ => A.F.W) (fun k => Z^(A.D.length k.val)) hYp
    (fun _ => A.F.complex_support) (fun _ y => source_complex_profile_norm A.D A.F y)
    x z a A.D.e ha (by linarith) A.D.e_pos A.D.e_small.le hx hz rows Subtype.val A.F.W 1 2
    (U^(Geometry.y/d)) (by norm_num) A.F.complex_support (A.F.W.smooth ⊤) hY
    cost d U A.D.t A.D.t (coefficientBoxCount A.D.t) Cu Ccond Q P R q (Geometry.ell/d) (2*a-1)
    selLoss (A.D.t+error+A.D.t) Ccount (Cr'*(1+height)^degree) hcost hmom.1.le
    A.D.t_pos.le A.D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i => (data i).combined_pos.le)
    (fun i => (data i).combined_le_radical) (fun i => (hrows i.val i.property).2)
    (fun i => hrow i.val i.property) hcut (by simpa using hcard) hselected hfull
    (by simpa only [add_assoc] using hmomentInput)
  apply hb.trans_eq
  dsimp only [C]
  have hpow : U^(A.D.t+q*(Geometry.ell/d)-q*Selection.zeroCapacity cost d/2+
      (3*R+1+A.D.t+error+A.D.t)/4+selLoss/2+(2*a-1)*(A.D.t+A.D.t)/2) =
      U^A.D.t*U^(q*(Geometry.ell/d)-q*Selection.zeroCapacity cost d/2+
      (3*R+1+A.D.t+error+A.D.t)/4+selLoss/2+(2*a-1)*(A.D.t+A.D.t)/2) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hpow]
  ring

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.selected_source_packet_with_cost
