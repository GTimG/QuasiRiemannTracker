/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All four actual first-short outside-anchor exits on the same retained rows. -/
import Candidate.C092.transport.MixedOutsidePaidLow
import Candidate.C092.transport.MixedOutsidePaidConductor
import Candidate.C092.transport.MixedOffsetCountBranchData
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace QRH.Cycle092.MixedOutsidePaid
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Record1252270103Return QRH.Cycle092.PacketJoinE49 QRH.Cycle092.MixedOffsetCount
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters]

/-- Authentic native counts and the original ticket payment, with all constants
fixed before every bank cutoff, source fiber, retained subset and source fee.
There is no centrality premise or assumed analytic count. -/
theorem actual_outside_count_paid (hβ:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ:2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃mesh:ℝ→ℝ,(∀t,0<t → 0 < mesh t) ∧
    ∀(D:Cycle25.Weighted.MomentData)(S:WeightedSourceData D),
      (∀s,D.ell s ≤ mesh D.t/200) → (∀s,D.ell s≤ Cycle25.sourceMesh D.t/200) →
    ∀η:Character,∃J:ℕ,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(d a tstar T allowance height ξ:ℝ)(i:ℕ),
      (1/200:ℝ)≤ d → 51/100<a → 2*a-1≤ 3/4 → D.t≤ 1/10000000 → D.ε≤ 1/10000000 →
      0≤ height → 2*Real.pi*allowance+(3*i:ℕ)*T≤ height → ξ≤ gammaMax →
    ∀(P:Presented D S η Z d a tstar T allowance i)(F:Slice P),
      (∀s,|(P.batch.external s).im|≤ height) → F.fiber.r<1 →
      tstar=Return.cutoffI (2*a-1) (F.fiber.q/(2*a-1))-ξ →
      ¬centralLengths F.fiber.r F.fiber.m →
    ∀common:Finset FreeRow,common⊆F.fiber.rows →
    ∀ticket:Row,ticket∈rows → ticket.box.Contains (2*a-1,F.fiber.q/(2*a-1)) →
      hLower≤ Geometry.h → Geometry.h≤ hUpper → Geometry.ell=Physical.ell →
      originalDlow ticket≤ d → d≤ Geometry.h+rowPad →
    ∀moment mass fee:ℝ,
      d*(3*countLoss D.ε P.batch.mesh D.t/4+moment/4+mass)+fee+2*rowPad≤ 7*oldFee →
    ∃R:ℝ,(common.card:ℝ)≤ 192*(1+height)*(C*(1+height)^J)*(Z^d)^(R+countLoss D.ε P.batch.mesh D.t) ∧
      rowPrice (2*a-1) (F.fiber.q/(2*a-1)) (R+countLoss D.ε P.batch.mesh D.t) d sourceCost+
        d*(moment/4+mass)+fee≤ theta-oldFee := by
  obtain ⟨mo,hmo,hOrd⟩:=actual_ordinary_high_count hβ hκβ
  obtain ⟨mt,hmt,hTan⟩:=actual_inverse_tangent_count hβ
  let mesh:ℝ→ℝ:=fun t=>min (mo t) (mt t)
  refine ⟨mesh,fun t ht=>lt_min (hmo t ht) (hmt t ht),?_⟩
  intro D S hfine hstandard η
  have hfo:∀s,D.ell s≤ mo D.t/200:=fun s=>(hfine s).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hft:∀s,D.ell s≤ mt D.t/200:=fun s=>(hfine s).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  obtain ⟨Ji,hInv⟩:=actual_inverse_high_count D S
  obtain ⟨Ci,hCi,hInv⟩:=hInv η
  obtain ⟨Jo,Co,hCo,hOrd⟩:=hOrd D S hfo hstandard η
  obtain ⟨Jt,Ct,hCt,hTan⟩:=hTan D S hft η
  let J:=Ji+Jo+Jt
  let C:=Ci+Co+Ct+1
  have hC:0<C:=by dsimp [C];positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hInv,hOrd,hTan] with Z hi ho ht
  refine ⟨hi.1,?_⟩
  intro d a tstar T allowance height ξ i hd ha hδhi hts hεs hh hf hξ P F him hr1 hstar hout
    common hsub ticket hticket hpbox hhlo hhhi hell hdlo hdh moment mass fee hbudget
  have hH:1≤ 1+height:=by linarith
  have hU:1<Z^d:=Real.one_lt_rpow hi.1 (by linarith)
  have hgeo:=F.fiber.lengths hU
  have promote (c:ℝ)(j:ℕ)(hc:0≤ c)(hcC:c≤ C)(hj:j≤ J)(R L:ℝ)(hL:0≤ L)(hLhi:L≤ 192)
      (hb:(common.card:ℝ)≤ L*(1+height)*(c*(1+height)^j)*(Z^d)^(R+countLoss D.ε P.batch.mesh D.t)) :
      (common.card:ℝ)≤ 192*(1+height)*(C*(1+height)^J)*(Z^d)^(R+countLoss D.ε P.batch.mesh D.t):=by
    have hp:=pow_le_pow_right₀ hH hj
    have hm:=mul_le_mul hcC hp (by positivity) hC.le
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hLhi (by positivity)) hm (by positivity) (by positivity)
  have finish (R:ℝ)
      (hc:(common.card:ℝ)≤ 192*(1+height)*(C*(1+height)^J)*(Z^d)^(R+countLoss D.ε P.batch.mesh D.t))
      (hp:rowPrice (2*a-1) (F.fiber.q/(2*a-1)) R d sourceCost<theta-8*oldFee+2*rowPad) :
      ∃R:ℝ,(common.card:ℝ)≤ 192*(1+height)*(C*(1+height)^J)*(Z^d)^(R+countLoss D.ε P.batch.mesh D.t) ∧
        rowPrice (2*a-1) (F.fiber.q/(2*a-1)) (R+countLoss D.ε P.batch.mesh D.t) d sourceCost+d*(moment/4+mass)+fee≤ theta-oldFee:=by
    refine ⟨R,hc,?_⟩
    unfold rowPrice at hp ⊢
    nlinarith only [hp,hbudget]
  by_cases hrhigh:anchorTop≤ F.fiber.r
  · apply finish (inverseHighR (2*a-1) (F.fiber.q/(2*a-1)))
    · exact promote Ci Ji hCi.le (by dsimp [C];linarith) (by dsimp [J];omega) _ 12 (by norm_num) (by norm_num)
        (hi.2 d a tstar T allowance height i hd ha hδhi hts hh hf P F hrhigh hr1 common hsub)
    · exact original_inverse_high_price_paid hticket hpbox hhlo hhhi hell hdlo hdh
  · by_cases hmhigh:anchorTop≤ 2*F.fiber.m
    · apply finish (ordinaryHighR (2*a-1) (F.fiber.q/(2*a-1)))
      · exact promote Co Jo hCo.le (by dsimp [C];linarith) (by dsimp [J];omega) _ 192 (by norm_num) le_rfl
          (ho.2 d a tstar T allowance height i hd ha hδhi hts hh hf P F him hmhigh common hsub)
      · exact original_ordinary_high_price_paid hticket hpbox hhlo hhhi hell hdlo hdh
    · have hav:=original_e49_available hticket hpbox
      have hcut:=actual_crossing_bounds hticket hpbox actual_contact_root
      rw [←actual_contact_width,←actual_contact_intercept,←actual_contact_slope,
        ←actual_cutoff_eq (2*a-1) (F.fiber.q/(2*a-1)) (Return.hJ hav.1 hav.2).ne'] at hcut
      have hrlo:anchorLeft≤ F.fiber.r:=by
        by_contra h
        have hmhi:=inverse_low_forces_ordinary_high hgeo.1 hstar hcut.1 hξ hεs (le_of_lt (lt_of_not_ge h))
        exact hmhigh hmhi
      have hrhi:F.fiber.r≤ anchorTop:=le_of_lt (lt_of_not_ge hrhigh)
      have hmlow:2*F.fiber.m≤ anchorLeft:=by
        by_contra h
        exact hout ⟨hrlo,hrhi,le_of_lt (lt_of_not_ge h),le_of_lt (lt_of_not_ge hmhigh)⟩
      apply finish (inverseTangentR (2*a-1) (F.fiber.q/(2*a-1)) F.fiber.r)
      · exact promote Ct Jt hCt.le (by dsimp [C];linarith) (by dsimp [J];omega) _ 12 (by norm_num) (by norm_num)
          (ht.2 d a tstar T allowance height i hd ha hδhi hts hh hf P F him hrlo hrhi common hsub)
      · exact original_ordinary_low_price_paid hticket hpbox hhlo hhhi hell hdlo hdh hgeo.1 hstar hξ hεs hmlow
end QRH.Cycle092.MixedOutsidePaid
#print axioms QRH.Cycle092.MixedOutsidePaid.actual_outside_count_paid
