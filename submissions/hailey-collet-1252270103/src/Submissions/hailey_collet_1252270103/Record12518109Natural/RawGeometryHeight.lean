/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Mathlib.Tactic
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryZeroPartition

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Filter
/-- A common polynomial height for all selected buffered rows. -/
def rawGeometryHeight (Z τ : ℝ) (I : ℕ) : ℝ :=
  (2*Real.pi+6*(I+1:ℕ))*Z^τ

lemma raw_geometry_height_nonneg {Z τ : ℝ} (hZ : 0 ≤ Z) (I : ℕ) :
    0 ≤ rawGeometryHeight Z τ I := by
  unfold rawGeometryHeight
  positivity

lemma raw_geometry_height_zero {Z τ : ℝ} (hZ : 1 ≤ Z) (hτ : 0 ≤ τ)
    (i I : ℕ) (hi : i ≤ I) :
    2*Real.pi*Z^(τ/2)+(3*i:ℕ)*Z^τ ≤ rawGeometryHeight Z τ I := by
  have hr := Real.rpow_le_rpow_of_exponent_le hZ (show τ/2 ≤ τ by linarith)
  have hz := Real.rpow_nonneg (zero_le_one.trans hZ) τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Real.pi by positivity)
  unfold rawGeometryHeight
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz]

lemma raw_geometry_height_time {Z τ t : ℝ} (hZ : 0 ≤ Z)
    (i I : ℕ) (hi : i ≤ I)
    (ht : |t|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ) : |t| ≤ rawGeometryHeight Z τ I := by
  have hz := Real.rpow_nonneg hZ τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  unfold rawGeometryHeight
  push_cast at ht ⊢
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz,
    mul_nonneg Real.pi_pos.le hz]

lemma raw_geometry_height_frequency {Z τ t v : ℝ} (hZ : 0 ≤ Z)
    (i I : ℕ) (hi : i ≤ I)
    (ht : |t|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ)
    (hv : |t+v|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ) : |v| ≤ rawGeometryHeight Z τ I := by
  have hz := Real.rpow_nonneg hZ τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  have habs : |v| ≤ |t+v|+|t| := by
    calc
      |v| = |t+v+-t| := congrArg abs (by ring)
      _ ≤ |t+v|+|t| := by simpa only [abs_neg] using abs_add_le (t+v) (-t)
  unfold rawGeometryHeight
  push_cast at ht hv ⊢
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz,
    mul_nonneg Real.pi_pos.le hz]

/-- The fixed buffered index contributes exactly Jτ to the scale exponent. -/
lemma raw_geometry_height_power {Z τ : ℝ} (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (I J : ℕ) :
    (1+rawGeometryHeight Z τ I)^J ≤
      (1+2*Real.pi+6*(I+1:ℕ))^J*Z^(τ*(J:ℝ)) := by
  have hz := Real.one_le_rpow hZ hτ
  have hp : 0 < Z := zero_lt_one.trans_le hZ
  have h : 1+rawGeometryHeight Z τ I ≤ (1+2*Real.pi+6*(I+1:ℕ))*Z^τ := by
    unfold rawGeometryHeight
    nlinarith
  calc
    _ ≤ ((1+2*Real.pi+6*(I+1:ℕ))*Z^τ)^J :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (raw_geometry_height_nonneg (τ:=τ) hp.le I)) h J
    _ = _ := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]


lemma normalized_slot_width {w wmin mesh dmin dmax d : ℝ}
    (hdmin : 0<dmin) (hdlo : dmin≤d) (hdhi : d≤dmax)
    (hwmin : 0≤wmin) (hwlo : wmin≤w) (hwhi : w≤mesh*dmin) :
    wmin/dmax≤w/d ∧ w/d≤mesh := by
  have hd : 0<d:=hdmin.trans_le hdlo
  have hdm : 0<dmax:=hd.trans_le hdhi
  have hm : 0≤mesh:=by nlinarith
  constructor
  · exact (div_le_div_of_nonneg_left hwmin hd hdhi).trans
      (div_le_div_of_nonneg_right hwlo hd.le)
  · exact (div_le_iff₀ hd).mpr (hwhi.trans (mul_le_mul_of_nonneg_left hdlo hm))

lemma raw_geometry_height_residual {Z τ d dmax : ℝ} (hZ : 1≤Z)
    (hτ : 0≤τ) (hdmax : 0<dmax) (hd : d≤dmax) (i I : ℕ) (hi : i≤I) :
    2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤rawGeometryHeight Z τ I := by
  have hmul:=mul_le_mul_of_nonneg_right hd (div_nonneg hτ (by positivity : 0≤2*dmax))
  have hid : dmax*(τ/(2*dmax))=τ/2 := by field_simp
  rw [hid] at hmul
  have hp : (Z^d)^(τ/(2*dmax))≤Z^(τ/2) := by
    rw [←Real.rpow_mul (zero_le_one.trans hZ)]
    exact Real.rpow_le_rpow_of_exponent_le hZ hmul
  have hm:=mul_le_mul_of_nonneg_left hp (show 0≤2*Real.pi by positivity)
  have hh:=raw_geometry_height_zero hZ hτ i I hi
  linarith

lemma eventually_buffer_height_power (dmin τ ηslot : ℝ) (I : ℕ)
    (hτ : 0≤τ) (hηslot : 0≤ηslot) (hgap : 2*τ<dmin*ηslot) :
    ∀ᶠZ : ℝ in atTop,1≤Z ∧∀d : ℝ,dmin≤d→∀i : ℕ,i≤I→
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^ηslot := by
  have hg : 0<dmin*ηslot-2*τ:=by linarith
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hg).eventually (eventually_ge_atTop (((3*I+5:ℕ):ℝ)^2))]
    with Z hZ hconstant
  refine ⟨hZ,?_⟩
  intro d hd i hi
  have hZp : 0<Z:=zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ:=Real.one_le_rpow hZ hτ
  have hic : (i:ℝ)≤I:=by exact_mod_cast hi
  have hsmall : 3+(3*i+2:ℕ)*Z^τ≤((3*I+5:ℕ):ℝ)*Z^τ := by
    push_cast
    nlinarith [mul_nonneg (show 0≤(I:ℝ)-i by linarith) (Real.rpow_nonneg hZp.le τ)]
  calc
    _≤(((3*I+5:ℕ):ℝ)*Z^τ)^2 := pow_le_pow_left₀ (by positivity) hsmall 2
    _=((3*I+5:ℕ):ℝ)^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _≤Z^(dmin*ηslot-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hZp.le _)
    _=Z^(dmin*ηslot) := by rw [←Real.rpow_add hZp];congr 1;ring
    _≤Z^(d*ηslot) := Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul_of_nonneg_right hd hηslot)
    _=_ := Real.rpow_mul hZp.le d ηslot

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.normalized_slot_width
#print axioms OAI.SevenEighths.Record12518109Natural.raw_geometry_height_residual
#print axioms OAI.SevenEighths.Record12518109Natural.eventually_buffer_height_power
