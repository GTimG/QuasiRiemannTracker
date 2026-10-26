/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0.
The coordinates below are obtained from the literal daughter capacity;
an upper capacity is never silently changed into an equality. -/
import Candidate.Research.RecursiveAffine.PhysicalDaughterSource

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open Filter CenteredMomentSectorLocalization

/-- The own common puncture increment is exactly the sum of the width
loss and common reduction. The paired first common ideal and the selected
frequency cancel, rather than being discarded. -/
theorem common_puncture_coordinate_identity (c d e freq inactive : ℝ) :
    (max (c - d) 0 + freq - inactive) +
      (min c d + e - freq + inactive) = c + e := by
  rcases le_total c d with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

/-- Exact actual-to-model coordinates at one continuing LOW source.

`dactual` is the attaining whole-slot deletion, `ell0` the actual loss of
slots through common/residual allocations, and `F` the residual reduction
of that same source. `pad` is the support/clipping cost in the checked
literal physical capacity. The native widened unit is retained exactly:
`t` is the frequency loss left after subtracting its width slack.

Thus model `A` and slot/width equations are equalities, but the model's
nonnegative reduction and slot-loss constraints acquire explicitly paid
finite errors. No remaining energy or desired regional return is assumed. -/
theorem actual_low_coordinate_lift
    (A Achild z zchild U Uchild a D dactual mesh v commonRed F ell0 t pad : ℝ)
    (hv : 0 ≤ v) (hr : 0 ≤ commonRed) (hF : 0 ≤ F) (ht : 0 ≤ t)
    (hell0 : 0 ≤ ell0)
    (hdel : D ≤ dactual) (hdelmesh : dactual ≤ D + mesh)
    (hslots : ell0 ≤ v + commonRed + F)
    (hz : zchild = z - dactual - ell0)
    (hU : Uchild = U - 6 * a - v - t)
    (hcapacity : Achild ≤ A - dactual - v - commonRed - F + pad) :
    let V := v + t
    let Red := A - D - V - Achild
    let ell := ell0 + (dactual - D)
    0 ≤ V ∧
    0 ≤ ell ∧
    ell ≤ ell0 + mesh ∧
    Uchild = U - 6 * a - V ∧
    zchild = z - D - ell ∧
    Achild = A - D - V - Red ∧
    -(t + pad) ≤ Red ∧
    commonRed + F + (dactual - D) ≤ Red + t + pad ∧
    ell ≤ V + Red + pad ∧
    v + commonRed ≤ V + Red + pad := by
  dsimp only
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith only [hU]
  constructor
  · linarith only [hz]
  constructor
  · ring
  constructor
  · linarith
  constructor
  · linarith only [hcapacity]
  constructor
  · linarith only [hslots, hcapacity]
  · linarith only [hcapacity, hdel, hF]

/-- Upward grid/plane rounding displaces the actual amplifier by `da`.
Absorbing exactly six times that displacement into V retains all frozen
model recurrences without changing the physical daughter's chosen unit. -/
theorem actual_low_coordinate_lift_with_amplifier_displacement
    (A Achild z zchild U Uchild aModel aActual da D dactual mesh v commonRed F ell0 t pad : ℝ)
    (hv : 0 ≤ v) (hr : 0 ≤ commonRed) (hF : 0 ≤ F) (ht : 0 ≤ t) (hda : 0 ≤ da)
    (hell0 : 0 ≤ ell0) (ha : aActual = aModel + da)
    (hdel : D ≤ dactual) (hdelmesh : dactual ≤ D + mesh)
    (hslots : ell0 ≤ v + commonRed + F)
    (hz : zchild = z - dactual - ell0)
    (hU : Uchild = U - 6 * aActual - v - t)
    (hcapacity : Achild ≤ A - dactual - v - commonRed - F + pad) :
    let V := v + (t + 6 * da)
    let Red := A - D - V - Achild
    let ell := ell0 + (dactual - D)
    0 ≤ V ∧ 0 ≤ ell ∧ ell ≤ ell0 + mesh ∧
    Uchild = U - 6 * aModel - V ∧
    zchild = z - D - ell ∧ Achild = A - D - V - Red ∧
    -(t + 6 * da + pad) ≤ Red ∧
    commonRed + F + (dactual - D) ≤ Red + (t + 6 * da) + pad ∧
    ell ≤ V + Red + pad ∧ v + commonRed ≤ V + Red + pad := by
  apply actual_low_coordinate_lift A Achild z zchild U Uchild aModel D dactual mesh
    v commonRed F ell0 (t + 6 * da) pad hv hr hF (by linarith only [ht, hda])
    hell0 hdel hdelmesh hslots hz
  · linarith only [hU, ha]
  · exact hcapacity

/-- The source port also accepts the actual common reduction with a finite
negative error, as required by the literal frequency/support padding. Its
full error is charged in the model's reduction constraint. -/
theorem actual_low_coordinate_lift_with_common_error
    (A Achild z zchild U Uchild aModel aActual da D dactual mesh v commonRed
      F ell0 t pad commonError : ℝ)
    (hv : 0 ≤ v) (hr : -commonError ≤ commonRed) (hF : 0 ≤ F)
    (ht : 0 ≤ t) (hda : 0 ≤ da) (hell0 : 0 ≤ ell0)
    (ha : aActual = aModel + da)
    (hdel : D ≤ dactual) (hdelmesh : dactual ≤ D + mesh)
    (hslots : ell0 ≤ v + commonRed + F)
    (hz : zchild = z - dactual - ell0)
    (hU : Uchild = U - 6 * aActual - v - t)
    (hcapacity : Achild ≤ A - dactual - v - commonRed - F + pad) :
    let V := v + (t + 6 * da)
    let Red := A - D - V - Achild
    let ell := ell0 + (dactual-D)
    0 ≤ V ∧ 0 ≤ ell ∧ ell ≤ ell0+mesh ∧
    Uchild = U-6*aModel-V ∧ zchild = z-D-ell ∧ Achild = A-D-V-Red ∧
    -(commonError+t+6*da+pad) ≤ Red ∧
    commonRed+F+(dactual-D) ≤ Red+(t+6*da)+pad ∧
    ell ≤ V+Red+pad ∧ v+commonRed ≤ V+Red+pad := by
  dsimp only
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hU, ha]
  · linarith only [hz]
  · ring
  · linarith only [hcapacity, hdel, hr, hF]
  · linarith only [hcapacity]
  · linarith only [hslots, hcapacity]
  · linarith only [hcapacity, hdel, hF]

/-- The actual regional deletion is monotone in the regional gap and
amplifier. This refers to the desired regional gap, not the native old-gap
quantity `AffineLedger.g`. The checked LOW detector accepts this deletion
as its explicit argument. -/
theorem regional_deletion_monotone (k I gapModel gapActual aModel aActual : ℝ)
    (hk : 0 < k) (hI : 0 ≤ I) (hgap : gapModel ≤ gapActual) (ha : aModel ≤ aActual) :
    (gapModel + 6 * I * aModel) / (6 * k) ≤
      (gapActual + 6 * I * aActual) / (6 * k) := by
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 6 * k)
  have hmul := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 6 * I)
  linarith only [hgap, hmul]

/-- Regional amplifier and deletion retain the exact native LOW reserve;
neither a rounded mesh nor a physical width error is hidden in this identity. -/
theorem regional_low_reserve_identity (k I q gap alpha U : ℝ)
    (hk : k ≠ 0) (hden : k - q * I ≠ 0) :
    let a := q / (6 * (k - q * I)) * gap + alpha * U
    let D := (gap + 6 * I * a) / (6 * k)
    a - q * D = alpha * (1 - q * I / k) * U := by
  dsimp only
  field_simp [hk, hden]
  ring

/-- Literal native widening leaves only the constant frequency loss in
the width coordinate; its reserve and bin-half-width cancel exactly. -/
theorem native_width_error_identity (freq reserve widthSlack binHalf constant : ℝ)
    (hfreq : freq = binHalf + constant)
    (hreserve : reserve = widthSlack) :
    (freq + reserve) - (widthSlack + binHalf) = constant := by
  rw [hfreq, hreserve]
  ring

/-- Specialization to the actual native frequency radius and matching
native width reserve, with an arbitrary (possibly rebased) unit. -/
theorem actual_native_width_error (Z ξ widthReserve : ℝ) :
    (frequencyLoss Z 32 ξ + widthReserve) - (widthReserve + ξ / 2) =
      Real.logb Z 128 := by
  unfold frequencyLoss
  norm_num
  ring

/-- The complete finite error used in the exact coordinate lift. All
profile support constants are fixed before the moving physical state. -/
def sourceCoordinateError (Z b b₁ b₂ : ℝ) (N : ℕ) : ℝ :=
  Real.logb Z 128 + 2 * (N : ℝ) * Real.logb Z b +
    Real.logb Z (max 1 b₁ * max 1 b₂)

theorem sourceCoordinateError_nonneg {Z b b₁ b₂ : ℝ} (N : ℕ)
    (hZ : 1 < Z) (hb : 1 ≤ b) : 0 ≤ sourceCoordinateError Z b b₁ b₂ N := by
  have h₁ : 0 ≤ Real.logb Z 128 := Real.logb_nonneg hZ (by norm_num)
  have h₂ : 0 ≤ Real.logb Z b := Real.logb_nonneg hZ hb
  have h₃ : 0 ≤ Real.logb Z (max 1 b₁ * max 1 b₂) := Real.logb_nonneg hZ
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
  unfold sourceCoordinateError
  positivity

/-- One threshold, independent of all moving daughter states, makes the
literal finite coordinate error smaller than any prescribed fraction of
every actual unit above a fixed positive floor. In particular this does
not alter the unit to force a regional window. -/
theorem eventual_sourceCoordinateError_small (N : ℕ) (b minUnit η : ℝ)
    (hb : 1 ≤ b) (hmin : 0 < minUnit) (hη : 0 < η) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (b₁ b₂ U : ℝ), b₁ ≤ b → b₂ ≤ b → minUnit ≤ U →
        0 ≤ sourceCoordinateError Z b b₁ b₂ N ∧
        sourceCoordinateError Z b b₁ b₂ N ≤ η * U := by
  let c : ℝ := η * minUnit / (2 * (N : ℝ) + 3)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hlog128 : ∀ᶠ Z : ℝ in atTop, Real.logb Z 128 ≤ c := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_rpow_atTop hc).eventually_ge_atTop (128 : ℝ)] with Z hZ hpower
    exact (Real.logb_le_iff_le_rpow hZ (by norm_num)).mpr hpower
  have hlogb : ∀ᶠ Z : ℝ in atTop, Real.logb Z b ≤ c := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_rpow_atTop hc).eventually_ge_atTop b] with Z hZ hpower
    exact (Real.logb_le_iff_le_rpow hZ hbpos).mpr hpower
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlog128, hlogb] with Z hZ h128 hbZ
  refine ⟨hZ, ?_⟩
  intro b₁ b₂ U hb₁ hb₂ hU
  refine ⟨sourceCoordinateError_nonneg N hZ hb, ?_⟩
  have hprodpos : 0 < max 1 b₁ * max 1 b₂ := mul_pos
    (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _))
  have hprod : max 1 b₁ * max 1 b₂ ≤ b * b :=
    mul_le_mul (max_le hb hb₁) (max_le hb hb₂)
      (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans hb)
  have hlogprod := Real.logb_le_logb_of_le hZ hprodpos hprod
  rw [Real.logb_mul hbpos.ne' hbpos.ne'] at hlogprod
  have hn : 0 ≤ 2 * (N : ℝ) := by positivity
  have hN := mul_le_mul_of_nonneg_left hbZ hn
  have hscale : (2 * (N : ℝ) + 3) * c = η * minUnit := by
    dsimp only [c]
    field_simp
  have hunit := mul_le_mul_of_nonneg_left hU hη.le
  unfold sourceCoordinateError
  nlinarith only [h128, hbZ, hlogprod, hN, hscale, hunit]

/-- The affine-plane error caused by the actual finite support padding.
This is an algebraic propagation identity for the real daughter, not an
assumption that the daughter already lies in the next regional plane. -/
theorem actual_regional_plane_error
    (A Achild capA z zchild U Uchild a D V Red ell k I error : ℝ)
    (hD : 6 * k * D = capA + (6 * k - 1) * z - I * U + 6 * I * a)
    (hU : Uchild = U - 6 * a - V)
    (hz : zchild = z - D - ell)
    (hA : Achild = A - D - V - Red)
    (hV : 0 ≤ V) (hell : 0 ≤ ell)
    (hk : (1 / 6 : ℝ) ≤ k) (hI : I ≤ 1)
    (hRed : -error ≤ Red) :
    Achild + (6 * k - 1) * zchild - I * Uchild ≤ A - capA + error := by
  have hiden : Achild + (6 * k - 1) * zchild - I * Uchild =
      A - capA + (I - 1) * V - Red - (6 * k - 1) * ell := by
    rw [hU, hz, hA]
    nlinarith only [hD]
  rw [hiden]
  have hv : (I - 1) * V ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hV
  have he : 0 ≤ (6 * k - 1) * ell := mul_nonneg (by linarith) hell
  linarith only [hv, he, hRed]

/-- The corrected common-rate price is paid by literal native outside-row
saving plus literal daughter volume loss. This is the crucial distinction
from assigning the full terminal delta to the common reduction.

S is the sum of the actual two own common norm logs. Gamma is the native
outside-coordinate saving. The extra actual volume reduction e may include
the same residual F and unused capacity slack; only its lower bound -pad is
needed. Model V+Red equals S+e exactly, so no missing-radical term is replaced
by V and no common reduction is priced at delta without payment. -/
theorem corrected_common_credit_from_actual_source
    (A Achild D V Red S F pad delta h Gamma : ℝ)
    (hh : 0 ≤ h) (hF : 0 ≤ F)
    (hA : Achild = A - D - V - Red)
    (hcapacity : Achild ≤ A - D - S - F + pad)
    (hGamma : (delta - h) * S ≤ Gamma) :
    let e := A - D - Achild - S
    (delta - h) * (V + Red) ≤ Gamma + delta * e + h * pad := by
  dsimp only
  have he : 0 ≤ A - D - Achild - S + pad := by
    linarith only [hcapacity, hF]
  have hp := mul_nonneg hh he
  have hid : Gamma + delta * (A - D - Achild - S) + h * pad -
      (delta - h) * (V + Red) =
    Gamma - (delta - h) * S + h * (A - D - Achild - S + pad) := by
    rw [hA]
    ring
  linarith only [hGamma, hp, hid]

/-- The same physical credit with the actual/model deletion displacement
shown explicitly. The first bound prices it at the common rate; the second
uses the actual terminal deletion's delta credit. Any preceding LOW cost
q*(dactual-Dmodel) remains a separate source term unless cancelled with its
matching actual amplifier by `regional_low_reserve_identity`. -/
theorem corrected_common_credit_with_deletion_displacement
    (A Achild Dmodel dactual V Red S F pad delta h Gamma : ℝ)
    (hh : 0 ≤ h) (hF : 0 ≤ F) (hdel : Dmodel ≤ dactual)
    (hA : Achild = A - Dmodel - V - Red)
    (hcapacity : Achild ≤ A - dactual - S - F + pad)
    (hGamma : (delta - h) * S ≤ Gamma) :
    let e := A - dactual - Achild - S
    let deltaD := dactual - Dmodel
    (delta - h) * (V + Red) ≤ Gamma + delta * e + (delta - h) * deltaD + h * pad ∧
    (delta - h) * (V + Red) ≤ Gamma + delta * e + delta * deltaD + h * pad := by
  dsimp only
  have he : 0 ≤ A - dactual - Achild - S + pad := by
    linarith only [hcapacity, hF]
  have hp := mul_nonneg hh he
  have hid : Gamma + delta * (A - dactual - Achild - S) +
      (delta - h) * (dactual - Dmodel) + h * pad - (delta - h) * (V + Red) =
    Gamma - (delta - h) * S + h * (A - dactual - Achild - S + pad) := by
    rw [hA]
    ring
  have hfirst : (delta - h) * (V + Red) ≤ Gamma + delta * (A - dactual - Achild - S) +
      (delta - h) * (dactual - Dmodel) + h * pad := by
    linarith only [hGamma, hp, hid]
  refine ⟨hfirst, ?_⟩
  have hdisp := mul_nonneg hh (sub_nonneg.mpr hdel)
  linarith only [hfirst, hdisp]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_low_coordinate_lift
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_regional_plane_error
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_sourceCoordinateError_small
#print axioms OAI.SevenEighths.Cycle153RegionalLow.corrected_common_credit_from_actual_source
#print axioms OAI.SevenEighths.Cycle153RegionalLow.corrected_common_credit_with_deletion_displacement

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_low_coordinate_lift_with_common_error
