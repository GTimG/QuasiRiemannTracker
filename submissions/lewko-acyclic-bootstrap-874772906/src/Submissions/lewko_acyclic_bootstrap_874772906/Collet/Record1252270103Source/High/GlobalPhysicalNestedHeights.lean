/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal two-stage Mellin shifts fit one buffered source-height gate.
The LOW polynomial remains a product of the four integration heights. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPaidBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open Filter

def mellinShift (origin:ℝ)(reflected:Bool)(t u:ℝ) : ℝ :=
  origin+2*Real.pi*(u-(if reflected then -t else t))
def mellinPairHeight (t u:ℝ) : ℝ := (1+‖t‖)*(1+‖u‖)
def mellinShiftConstant : ℝ := 1+2*Real.pi

theorem mellin_pair_height_one (t u:ℝ) : 1≤mellinPairHeight t u := by
  dsimp only [mellinPairHeight]
  nlinarith [norm_nonneg t,norm_nonneg u,mul_nonneg (norm_nonneg t) (norm_nonneg u)]

theorem literal_mellin_shift_height (origin height t u:ℝ)(reflected:Bool)(hh:0≤height) :
    1+|mellinShift origin reflected t u|+height≤
      mellinShiftConstant*mellinPairHeight t u*(1+|origin|+height) := by
  have hsign:|if reflected then -t else t|=|t|:=by cases reflected <;> simp
  have hs : |u-(if reflected then -t else t)|≤|u|+|t| := by
    simpa only [sub_eq_add_neg,abs_neg,hsign] using abs_add_le u (-(if reflected then -t else t))
  have hmul:=mul_le_mul_of_nonneg_left hs (show 0≤2*Real.pi by positivity)
  have he:=abs_add_le origin (2*Real.pi*(u-(if reflected then -t else t)))
  rw [abs_mul,abs_of_nonneg (show 0≤2*Real.pi by positivity)] at he
  have hs':|mellinShift origin reflected t u|≤|origin|+2*Real.pi*(|u|+|t|):=by
    dsimp only [mellinShift]
    linarith
  let V:=mellinPairHeight t u
  let H:=1+|origin|+height
  have hV:1≤V:=mellin_pair_height_one t u
  have hH:1≤H:=by dsimp only [H];linarith [abs_nonneg origin]
  have hp:|u|+|t|≤V:=by
    dsimp only [V,mellinPairHeight]
    simp only [Real.norm_eq_abs]
    nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg u)]
  have hHV:H≤V*H:=by nlinarith [mul_nonneg (sub_nonneg.mpr hV) (zero_le_one.trans hH)]
  have hVH:V≤V*H:=by nlinarith [mul_nonneg (zero_le_one.trans hV) (sub_nonneg.mpr hH)]
  have hscaled:=mul_le_mul_of_nonneg_left (hp.trans hVH) (show 0≤2*Real.pi by positivity)
  change 1+|mellinShift origin reflected t u|+height≤mellinShiftConstant*V*H
  dsimp only [mellinShiftConstant]
  dsimp only [H] at hHV hscaled
  nlinarith

theorem nested_mellin_shift_height (origin height t₁ u₁ t₂ u₂:ℝ)
    (first second:Bool)(hh:0≤height) :
    1+|mellinShift (mellinShift origin first t₁ u₁) second t₂ u₂|+height≤
      mellinShiftConstant^2*(mellinPairHeight t₁ u₁*(1+|origin|+height))*mellinPairHeight t₂ u₂ := by
  have h₁:=literal_mellin_shift_height origin height t₁ u₁ first hh
  have h₂:=literal_mellin_shift_height (mellinShift origin first t₁ u₁) height t₂ u₂ second hh
  have hc:0≤mellinShiftConstant:=by unfold mellinShiftConstant;positivity
  have hp:0≤mellinPairHeight t₂ u₂:=(zero_le_one.trans (mellin_pair_height_one t₂ u₂))
  exact h₂.trans ((mul_le_mul_of_nonneg_left h₁ (mul_nonneg hc hp)).trans_eq (by ring))

/-- The source cutoff is fixed before all external and integration heights. -/
theorem eventually_nested_source_height (τ:ℝ)(hτ:0<τ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(origin height t₁ u₁ t₂ u₂:ℝ)(first second:Bool),
      0≤height→mellinPairHeight t₁ u₁*(1+|origin|+height)≤Z^(τ/4)→
      mellinPairHeight t₂ u₂≤Z^(τ/4)→
      1+|mellinShift (mellinShift origin first t₁ u₁) second t₂ u₂|+height≤Z^τ := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<τ/2 by positivity)).eventually
      (eventually_ge_atTop (mellinShiftConstant^2))] with Z hZ hconst
  refine ⟨hZ,?_⟩
  intro origin height t₁ u₁ t₂ u₂ first second hh h₁ h₂
  have hz:=zero_lt_one.trans hZ
  have hp:=mul_le_mul h₁ h₂ (zero_le_one.trans (mellin_pair_height_one t₂ u₂))
    (Real.rpow_nonneg hz.le _)
  have hbase:0≤(mellinPairHeight t₁ u₁*(1+|origin|+height))*mellinPairHeight t₂ u₂:=by
    have hP:=mellin_pair_height_one t₁ u₁
    have hQ:=mellin_pair_height_one t₂ u₂
    positivity
  have hbound:=mul_le_mul hconst hp hbase (Real.rpow_nonneg hz.le _)
  apply (nested_mellin_shift_height origin height t₁ u₁ t₂ u₂ first second hh).trans
  calc
    _=mellinShiftConstant^2*((mellinPairHeight t₁ u₁*(1+|origin|+height))*mellinPairHeight t₂ u₂):=by ring
    _≤Z^(τ/2)*(Z^(τ/4)*Z^(τ/4)):=hbound
    _=Z^τ:=by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

/-- Every physical slot frequency fits the same literal buffered interval. -/
theorem buffered_slot_height (Z τ t height v:ℝ)(i:ℕ)(hZ:0≤Z)
    (hh:0≤height)(hv:|v|≤height)(ht:1+|t|+height≤Z^τ) :
    |t+v|+Z^τ/2≤(3*i+2:ℕ)*Z^τ ∧ |t|+Z^τ/2≤(3*i+2:ℕ)*Z^τ := by
  have hsum:=abs_add_le t v
  have hpow:=Real.rpow_nonneg hZ τ
  have hi:0≤(i:ℝ):=Nat.cast_nonneg i
  push_cast
  constructor <;> nlinarith [mul_nonneg hi hpow]

/-- LOW source growth is retained as an integrable polynomial; it need not
be charged to the density reserve. -/
theorem nested_low_height_power (origin height t₁ u₁ t₂ u₂:ℝ)
    (first second:Bool)(hh:0≤height)(J:ℕ) :
    (1+|mellinShift (mellinShift origin first t₁ u₁) second t₂ u₂|+height)^J≤
      mellinShiftConstant^(2*J)*(mellinPairHeight t₁ u₁*(1+|origin|+height))^J*
        (mellinPairHeight t₂ u₂)^J := by
  have h:=pow_le_pow_left₀ (show 0≤1+|mellinShift (mellinShift origin first t₁ u₁) second t₂ u₂|+height by positivity)
    (nested_mellin_shift_height origin height t₁ u₁ t₂ u₂ first second hh) J
  simpa only [mul_pow,←pow_mul] using h
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.literal_mellin_shift_height
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.nested_mellin_shift_height
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.eventually_nested_source_height
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.buffered_slot_height
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.nested_low_height_power
