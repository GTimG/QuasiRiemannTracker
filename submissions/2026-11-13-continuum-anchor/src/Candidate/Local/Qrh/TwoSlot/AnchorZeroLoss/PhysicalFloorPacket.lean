/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Physical empty-selection floor packets from Hailey Collet's existing
unmarked fourth moment. Original coefficient packets and zeros are retained. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FloorPacket
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.UnmarkedFourth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorZeroLoss
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor ProbePhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth
local notation "O" => HeckeFamily.O

/-- The actual inclusive-floor packet with its unmarked moment discharged.
The only zero-free input is the existing contrary-hypothesis range for the
incumbent supremum, as in the original numerator theorem. No affine source,
large-value selection, endpoint geometry or old floor-margin instance occurs.
The arbitrary bounded multiplier retains the normalized physical main slots. -/
theorem physical_floor_packet {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap : ℝ) (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*HeckeZeroSupremum.beta-1 ≤ kap)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (he : D.e ≤ 1/1000) {ι : Type} [Fintype ι] [DecidableEq ι]
    (cp bp Bp : ℝ) (hcp : 0 < cp) (hbp : 0 < bp) (hBp : 0 ≤ Bp) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧ ∀
      (η : Character) (T : ι → Finset ProbePhysical.PrimeIdeal)
      (hT : ∀ i P, P ∈ T i → P.val ∉ F.S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (Pbase : ∀ i, T i) (W : ι → ℝ → ℂ) (Yp : ι → ℝ),
      (∀ i, 1 ≤ Yp i) → (∀ i, Function.support (W i) ⊆ Set.Icc cp bp) →
      (∀ i y, ‖W i y‖ ≤ Bp) → ∀ (x z : ℂ),
      x.re = 51/100 + 16*D.e → z.re = 17/50 →
      ∀ rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue ≠ 1) →
      ∀ (P : rows → ℂ), (∀ i, ‖P i‖ ≤ 1) → ∀ v : ℝ, 0 < v → v ≤ 99 →
      (∑ i:rows, ‖labelPolynomialPacket F.S F.exclusions η i.val T hT W Yp
        x z F.W (U^v) * P i‖) ≤
      C*(U^v)^(-(1/2:ℝ))*(∏ i, (Yp i)^(-(4/25:ℝ)))*
        U^(1+(38/25:ℝ)*D.t) := by
  obtain ⟨Cm,hCm,hpacket⟩ := floor_packet_bound (ι:=ι) D.t cp bp Bp
    D.t_pos hcp hbp hBp
  obtain ⟨Cr,hCr,hmoment⟩ := floor_active_fourth F kap hkaplo hkaphi hkapbeta hbeta
    F.W D.t D.t D.t 2 D.t_pos D.t_pos D.t_pos (by norm_num)
    (by linarith [D.t_small])
  let Cmoment : ℝ := max 1 Cr
  let n := coefficientBoxCount100 D.t
  let C : ℝ := ((n+1:ℕ):ℝ)*Cm*128*Cmoment
  have hCmoment : 1 ≤ Cmoment := le_max_left _ _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hmoment,eventually_ge_atTop (2:ℝ)] with U hmom hU2
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro η T hT hdis hη Pbase W Yp hYp hWS hWB x z hx hz rows hrows hrow P hP v hv hvhi
  let data (i:rows) : PhysicalReflectionData F.S F.exclusions.prime i.val :=
    Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime i.val
      (hrow i.val i.property))
  let Cu (i:rows) := (data i).combinedConductor
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0 < Ccond := by
    dsimp only [Ccond]
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hcut : 2*U^v ≤ U^((n:ℝ)*D.t) := by
    calc
      _ ≤ U*U^(99:ℝ) := mul_le_mul hU2
        (Real.rpow_le_rpow_of_exponent_le hU.le hvhi) (by positivity) (by positivity)
      _ = U^(100:ℝ) := by
        have hh := Real.rpow_add hUp (1:ℝ) (99:ℝ)
        norm_num only [Real.rpow_one, show (1+99:ℝ)=100 by norm_num] at hh
        exact hh.symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU.le (by
        have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (100/D.t)) D.t_pos.le
        simpa only [n,coefficientBoxCount100,div_mul_cancel₀ _ D.t_pos.ne'] using hh)
  have hfourth (j : ℕ) (hj : j ∈ Finset.range (n+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val T) :
      (∑i:rows, ‖if (labelPacketScale F.S i.val T (e i):ℝ) ≤ 2*U^v ∧
        dilationBox U D.t n
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val T (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val)
          false F.W (U^v/(labelPacketScale F.S i.val T (e i):ℝ)) 0 0 else 0‖^4) ≤
        Cmoment*U^(1+(D.t+D.t)) := by
    have hh := hmom.2 rows hrows data (fun i => (labelPacketScale F.S i.val T (e i):ℝ))
      (fun i => lt_of_lt_of_le zero_lt_one
        (by exact_mod_cast labelPacketScale_one_le F.S i.val T (e i))) v hv hvhi j hj
    have hCrle : Cr ≤ Cmoment := le_max_right 1 Cr
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hCrle
      (Real.rpow_nonneg hUp.le (1+D.t+D.t)))
    convert hh' using 1
    · apply Finset.sum_congr rfl
      intro i _
      rfl
    · congr 2
      ring
  have hh := hpacket F.S F.exclusions (4*D.e) F.first η T hT hdis hη Pbase
    W Yp hYp hWS hWB x z D.e D.e_pos he hx hz rows Subtype.val F.W 1 2 (U^v)
    (by norm_num) F.complex_support (F.W.smooth ⊤) (by positivity)
    U D.t n Cu Ccond P (D.t+D.t) Cmoment hU.le D.t_pos.le hCmoment
    (by linarith [D.e_pos]) hCcond (fun i => (data i).combined_pos.le)
    (fun i => (data i).combined_le_radical) (fun i => (hrows i.val i.property).2)
    (fun i => hrow i.val i.property) hcut
    (floor_row_count rows U hU.le (fun u hu => (hrows u hu).2)) hP hfourth
  apply hh.trans
  have hE : 1+(D.t+D.t)/4+D.t/100+D.t ≤ 1+(38/25:ℝ)*D.t := by
    linarith [D.t_pos]
  calc
    _ = C*(U^v)^(-(1/2:ℝ))*(∏ i,(Yp i)^(-(4/25:ℝ)))*
        U^(1+(D.t+D.t)/4+D.t/100+D.t) := by
      dsimp only [C]
      rw [Real.rpow_add hUp (1+(D.t+D.t)/4+D.t/100) D.t]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU.le hE)
      (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
        (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (zero_le_one.trans (hYp i)) _)))

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.physical_floor_packet
