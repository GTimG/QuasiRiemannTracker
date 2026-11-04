import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedCentralExponent

/- The actual retuned row-count exponent and the physical central exponent.
   The analytic moment estimates are still separate obligations. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.CentralExtension
noncomputable section
open RowCountExtension PrincipalExtension

def rationalRowExponent (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ≤5/6 then countR δ (1/2-q/δ)+Δ/4+159*ε+εm+slotMesh+7*ν
  else 1-δ+78*ε+εm

theorem rational_envelope_bounds (δ y : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hy : 0≤y) (hy1 : y≤1/2) :
    1-δ≤countR δ y ∧ countR δ y≤17/12 := by
  have hs := adaptive_split_range cRat δ y
    (by norm_num [cRat,kappaRat]) (by norm_num [cRat,kappaRat]) hδ hδ1 hy hy1
  have hid := long_at_adaptive_split cRat δ y
  rw [rational_envelope_identity] at hid
  have hmul0 := mul_nonneg (show 0≤5/6-δ by linarith)
    (show 0≤adaptiveSplit cRat δ y-1 by linarith)
  have hmul1 := mul_le_mul_of_nonneg_left
    (show adaptiveSplit cRat δ y-1≤1/2 by linarith) (show 0≤5/6-δ by linarith)
  constructor <;> linarith

theorem rational_row_exponent_bounds (δ q Δ ε εm slotMesh ν : ℝ)
    (hδ : 0<δ) (hδ1 : δ≤1) (hq : 0≤q) (hq1 : q≤δ/2)
    (hΔ : 0≤Δ) (hΔ1 : Δ≤1/6) (hε : 0≤ε) (hεm : 0≤εm)
    (hslot : 0≤slotMesh) (hν : 0≤ν)
    (hcount : 159*ε+εm+slotMesh+7*ν≤1/32) :
    1-δ≤rationalRowExponent δ q Δ ε εm slotMesh ν ∧
    rationalRowExponent δ q Δ ε εm slotMesh ν≤3/2 := by
  by_cases hb : δ≤5/6
  · have hqdiv : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
    have hy : 0≤1/2-q/δ := by linarith
    have hy1 : 1/2-q/δ≤1/2 := by linarith [div_nonneg hq hδ.le]
    have hr := rational_envelope_bounds δ (1/2-q/δ) hδ.le hb hy hy1
    simp only [rationalRowExponent,if_pos hb]
    constructor <;> linarith
  · simp only [rationalRowExponent,if_neg hb]
    constructor <;> linarith

theorem rational_adaptive_mixed_saving (N : ℕ)
    (a q β ε εm slotMesh ν ζ μ v d e eps heightLoss mesh extra saving : ℝ)
    (ha : 1/2<a) (ha1 : a≤1) (hq : 0≤q) (hq1 : q≤(2*a-1)/2)
    (hβ : sigmaRat≤β) (hβ1 : β≤1)
    (hε : 0≤ε) (hεm : 0≤εm) (hslot : 0≤slotMesh) (hν : 0≤ν)
    (hcount : 159*ε+εm+slotMesh+7*ν≤1/32)
    (hζ : 0≤ζ) (hζ1 : hRat+ζ≤1) (hv : v≤hRat+ζ)
    (hμ : 0≤μ) (hd : d-v≤μ) (he : 0≤e) (heps : 0≤eps) (hmesh : 0≤mesh)
    (hbudget : hRat*(159*ε+εm+slotMesh+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+heightLoss+mesh/5)+extra+saving≤1/1000000000000000) :
    sourceExponent lxRat lyRat ellRat a v d
        (rationalRowExponent (2*a-1) q (β-sigmaRat) ε εm slotMesh ν) q+
      realLoss lyRat ellRat N v e eps heightLoss mesh+extra≤
      β+sourceShift lxRat ellRat-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hδ1 : 2*a-1≤1 := by linarith
  have hΔ : 0≤β-sigmaRat := by linarith
  have hΔ1 : β-sigmaRat≤1/6 := by norm_num [sigmaRat] at hβ ⊢;linarith
  have hr := rational_row_exponent_bounds (2*a-1) q (β-sigmaRat) ε εm slotMesh ν
    hδ hδ1 hq hq1 hΔ hΔ1 hε hεm hslot hν hcount
  have hreal := realLoss_bound lyRat ellRat N v e eps heightLoss mesh
    (by norm_num [lyRat,ellRat,bRat]) (by norm_num [ellRat])
    (by linarith) he heps hmesh
  have haid : (1+(2*a-1))/2=a := by ring
  by_cases hb : 2*a-1≤5/6
  · have hqdiv : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
    have hy : 0≤1/2-q/(2*a-1) := by linarith
    have hy1 : 1/2-q/(2*a-1)≤1/2 := by linarith [div_nonneg hq hδ.le]
    have hqy : q≤(2*a-1)*(1/2-(1/2-q/(2*a-1))) := by
      have hid : (2*a-1)*(1/2-(1/2-q/(2*a-1)))=q := by field_simp;ring
      rw [hid]
    have hs := rational_balanced_source_margin (2*a-1) (1/2-q/(2*a-1)) v d
      (rationalRowExponent (2*a-1) q (β-sigmaRat) ε εm slotMesh ν) q β ζ μ
      (159*ε+εm+slotMesh+7*ν) hδ.le hb hy hy1 hβ hr.1 hr.2 hζ hv hμ hd hqy (by
        simp only [rationalRowExponent,if_pos hb];ring_nf;exact le_rfl)
    rw [haid] at hs
    linarith
  · have hs := rational_high_source_margin (2*a-1) v d
      (rationalRowExponent (2*a-1) q (β-sigmaRat) ε εm slotMesh ν) q β ζ μ
      (78*ε+εm) (by linarith) hδ1 hr.1 hr.2 hζ hv hμ hd hq1 (by
        simp only [rationalRowExponent,if_neg hb];linarith)
    rw [haid] at hs
    have hcost : 78*ε+εm≤159*ε+εm+slotMesh+7*ν := by linarith
    have hcost' := mul_le_mul_of_nonneg_left hcost
      (show 0≤hRat by norm_num [hRat,ellRat,bRat])
    linarith

theorem rational_class_exponent_identity (N : ℕ)
    (a v d R q e eps heightLoss mesh extra : ℝ) :
    sourceExponent lxRat lyRat ellRat a v d R q+
      realLoss lyRat ellRat N v e eps heightLoss mesh+extra=
      ((1-lyRat)*a+4*lxRat/25-33/50+(16-6*lyRat)*e)+
      (extra+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+heightLoss+
        ellRat*(-4/25+q+mesh)) := by
  unfold sourceExponent realLoss
  ring

#print axioms rational_envelope_bounds
#print axioms rational_row_exponent_bounds
#print axioms rational_adaptive_mixed_saving
#print axioms rational_class_exponent_identity
end
end BelowSevenEighthsTight.CentralExtension
