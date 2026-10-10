import Cycle25.Arithmetic.Endpoint

/-! Rational formulas and geometry certificates for B0.45--B0.49.
This module is elementary real arithmetic and is independent of the analytic route. -/

namespace Cycle25.Arithmetic

noncomputable def delta0 : ℝ :=
  (25-60*ell0+27*ell0^2)/(6*(5+4*ell0-3*ell0^2))
noncomputable def count0 : ℝ := (6*kappa0-1)/(15*kappa0-2)
noncomputable def v0 : ℝ := 5/6-delta0
noncomputable def rprime0 : ℝ :=
  -1+count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2)
noncomputable def h0 : ℝ :=
  -((1+ell0)/2+ell0/(6*kappa0))/(3*rprime0/4-1/(24*kappa0))
noncomputable def x0 : ℝ := 1+ell0-h0
noncomputable def y0 : ℝ := h0-2*ell0

theorem ell0_short_interval : (16712:ℝ)/100000 < ell0 ∧ ell0 < 167121/1000000 := by
  have hl := ell0_lo
  have hu := ell0_hi
  norm_num [rootLo, rootHi] at hl hu
  constructor <;> linarith

theorem delta0_den_pos : 0 < 6*(5+4*ell0-3*ell0^2) := by
  have h := ell0_coarse
  have hsq : ell0^2 ≤ (1:ℝ)/25 := by nlinarith [h.1, h.2]
  nlinarith [h.1]

theorem delta0_interval : (46934:ℝ)/100000 < delta0 ∧ delta0 < 46935/100000 := by
  have h := ell0_short_interval
  unfold delta0
  constructor
  · apply (lt_div_iff₀ delta0_den_pos).2
    nlinarith [sq_nonneg (ell0 - 16712/100000), sq_nonneg (ell0 - 167121/1000000)]
  · apply (div_lt_iff₀ delta0_den_pos).2
    nlinarith [sq_nonneg (ell0 - 16712/100000), sq_nonneg (ell0 - 167121/1000000)]

theorem count0_den_pos : 0 < 15*kappa0-2 := by linarith [kappa0_range.1]

theorem count0_interval : (37837:ℝ)/100000 < count0 ∧ count0 < 37838/100000 := by
  have h := ell0_short_interval
  unfold count0
  constructor
  · apply (lt_div_iff₀ count0_den_pos).2
    unfold kappa0
    linarith
  · apply (div_lt_iff₀ count0_den_pos).2
    unfold kappa0
    linarith

theorem v0_interval : (36398:ℝ)/100000 < v0 ∧ v0 < 364/1000 := by
  unfold v0
  constructor <;> linarith [delta0_interval.1, delta0_interval.2]

theorem binding_second :
    delta0*(6*kappa0+(6*kappa0+2)*ell0) = kappa0*(5-9*ell0) := by
  unfold delta0 kappa0
  have hd : 5+4*ell0-3*ell0^2 ≠ 0 := by
    have := delta0_den_pos
    intro he
    rw [he] at this
    norm_num at this
  ring_nf at hd
  field_simp [hd]
  ring

theorem binding_first :
    (324*kappa0^2-3)*delta0^2+(-756*kappa0^2+54*kappa0+5)*delta0+
      300*kappa0^2-40*kappa0 = 0 := by
  have hd : 5+4*ell0-3*ell0^2 ≠ 0 := by
    have := delta0_den_pos
    intro he
    rw [he] at this
    norm_num at this
  have hd2 : 25+40*ell0-14*ell0^2-24*ell0^3+9*ell0^4 ≠ 0 := by
    convert pow_ne_zero 2 hd using 1
    ring
  ring_nf at hd hd2
  have hid :
      (324*kappa0^2-3)*delta0^2+(-756*kappa0^2+54*kappa0+5)*delta0+
        300*kappa0^2-40*kappa0 =
      (600-675*ell0+189*ell0^2)*quartic ell0/(6*(5+4*ell0-3*ell0^2))^2 := by
    unfold kappa0 delta0 quartic
    field_simp [hd, hd2]
    ring_nf
    field_simp [hd, hd2]
    ring
  rw [hid, ell0_quartic]
  simp

private theorem product_interval {a b la ua lb ub : ℝ}
    (ha : la ≤ a ∧ a ≤ ua) (hb : lb ≤ b ∧ b ≤ ub)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) : la*lb ≤ a*b ∧ a*b ≤ ua*ub := by
  have ha0 : 0 ≤ a := hla.trans ha.1
  have hb0 : 0 ≤ b := hlb.trans hb.1
  exact ⟨mul_le_mul ha.1 hb.1 hlb ha0, mul_le_mul ha.2 hb.2 hb0 (ha0.trans ha.2)⟩

theorem rprime0_den_pos : 0 < 2*(v0+delta0*count0)^2 := by
  have hc : 0 < count0 := by linarith [count0_interval.1]
  have hd : 0 < delta0 := by linarith [delta0_interval.1]
  have hv : 0 < v0 := by linarith [v0_interval.1]
  positivity

theorem rprime0_interval : (-969:ℝ)/1000 < rprime0 ∧ rprime0 < -968/1000 := by
  have hd := delta0_interval
  have hc := count0_interval
  have hv := v0_interval
  have hd2 : (46934/100000:ℝ)^2 ≤ delta0^2 ∧ delta0^2 ≤ (46935/100000:ℝ)^2 := by
    constructor <;> nlinarith
  have hv2 : (36398/100000:ℝ)^2 ≤ v0^2 ∧ v0^2 ≤ (364/1000:ℝ)^2 := by
    constructor <;> nlinarith
  have hdc := product_interval ⟨le_of_lt hd.1, le_of_lt hd.2⟩
    ⟨le_of_lt hc.1, le_of_lt hc.2⟩ (by norm_num) (by norm_num)
  have hd2c := product_interval hd2 ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    (by norm_num) (by norm_num)
  have hdif : (49:ℝ)/1000 ≤ v0^2-delta0^2*count0 ∧
      v0^2-delta0^2*count0 ≤ 493/10000 := by
    constructor <;> norm_num at * <;> linarith
  have hn := product_interval ⟨le_of_lt hc.1, le_of_lt hc.2⟩ hdif
    (by norm_num) (by norm_num)
  have hs : (541:ℝ)/1000 ≤ v0+delta0*count0 ∧ v0+delta0*count0 ≤ 542/1000 := by
    constructor <;> norm_num at * <;> linarith
  have hs2 : (541/1000:ℝ)^2 ≤ (v0+delta0*count0)^2 ∧
      (v0+delta0*count0)^2 ≤ (542/1000:ℝ)^2 := by
    constructor <;> nlinarith
  unfold rprime0
  constructor
  · have he : (31:ℝ)/1000 < count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2) := by
      apply (lt_div_iff₀ rprime0_den_pos).2
      norm_num at hn hs2
      linarith
    linarith
  · have he : count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2) < (32:ℝ)/1000 := by
      apply (div_lt_iff₀ rprime0_den_pos).2
      norm_num at hn hs2
      linarith
    linarith

theorem kappa0_short_interval : (74977:ℝ)/100000 < kappa0 ∧ kappa0 < 74978/100000 := by
  have h := ell0_short_interval
  unfold kappa0
  constructor <;> linarith

theorem h0_den_neg : 3*rprime0/4-1/(24*kappa0) < 0 := by
  have hi : 0 < 1/(24*kappa0) := by positivity [kappa0_range.1]
  linarith [rprime0_interval.2]

theorem h0_interval : (793:ℝ)/1000 < h0 ∧ h0 < 795/1000 := by
  have he := ell0_short_interval
  have hk := kappa0_short_interval
  have hr := rprime0_interval
  have hk0 : 0 < kappa0 := by linarith [kappa0_range.1]
  have hnsmall : (37:ℝ)/1000 < ell0/(6*kappa0) ∧ ell0/(6*kappa0) < 372/10000 := by
    constructor
    · apply (lt_div_iff₀ (by positivity : 0 < 6*kappa0)).2
      linarith
    · apply (div_lt_iff₀ (by positivity : 0 < 6*kappa0)).2
      linarith
  have hn : (6205:ℝ)/10000 < (1+ell0)/2+ell0/(6*kappa0) ∧
      (1+ell0)/2+ell0/(6*kappa0) < 6208/10000 := by
    constructor <;> linarith
  have hinv : (555:ℝ)/10000 < 1/(24*kappa0) ∧ 1/(24*kappa0) < 556/10000 := by
    constructor
    · apply (lt_div_iff₀ (by positivity : 0 < 24*kappa0)).2
      linarith
    · apply (div_lt_iff₀ (by positivity : 0 < 24*kappa0)).2
      linarith
  have hden : (7815:ℝ)/10000 < 1/(24*kappa0)-3*rprime0/4 ∧
      1/(24*kappa0)-3*rprime0/4 < 7824/10000 := by
    constructor <;> linarith
  have hdenpos : 0 < 1/(24*kappa0)-3*rprime0/4 := by linarith
  have hrewrite : h0 = ((1+ell0)/2+ell0/(6*kappa0))/(1/(24*kappa0)-3*rprime0/4) := by
    unfold h0
    rw [show 1/(24*kappa0)-3*rprime0/4 = -(3*rprime0/4-1/(24*kappa0)) by ring]
    rw [div_neg, neg_div]
  rw [hrewrite]
  constructor
  · apply (lt_div_iff₀ hdenpos).2
    linarith
  · apply (div_lt_iff₀ hdenpos).2
    linarith

theorem physical_geometry : ell0 < x0 ∧ x0 < y0 ∧ y0 < 2*x0 ∧
    y0 < 1/2 ∧ 1/2 < h0 ∧ h0 < 2*y0 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold x0 y0
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem derivative_geometry : h0 < (4:ℝ)/5 ∧ 0 < h0-4*ell0 ∧ h0-4*ell0 < 13/100 := by
  have he := ell0_short_interval
  have hh := h0_interval
  constructor
  · linarith
  constructor <;> linarith

theorem supply_geometry : (1:ℝ)/5 < ell0/h0 ∧ (4:ℝ)/21 < ell0/h0 ∧ y0 < 4*ell0 := by
  have he := ell0_short_interval
  have hh := h0_interval
  have hh0 : 0 < h0 := by linarith
  have hmain : (1:ℝ)/5 < ell0/h0 := (lt_div_iff₀ hh0).2 (by linarith)
  refine ⟨hmain, ?_, ?_⟩
  · linarith
  · unfold y0; linarith

theorem positive_part_branch : 5*ell0 < 1 := by linarith [ell0_short_interval.2]

theorem other_endpoint_margin :
    11/12-49*h0/150+11*ell0/12 < b0-6/100 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold b0
  linarith

theorem floor_margin : (51:ℝ)/100+h0/3+51*ell0/100 < b0-1/100 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold b0
  linarith

theorem small_row_margin : h0*(17/50-1/6)-y0/2+(63:ℝ)/50*(1/200) < -1/20 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold y0
  linarith

theorem positive_A1_minorant (d : ℝ) : 0 < 36-174*d+347*d^2 := by
  nlinarith [sq_nonneg (d - (87:ℝ)/347)]

theorem comparison_margin {κ : ℝ} (hκ : 7/10 ≤ κ) :
    1/16 ≤ (2*κ-1)/(2*(6*κ-1)) := by
  apply (le_div_iff₀ (by linarith : 0 < 2*(6*κ-1))).2
  linarith

theorem counting_derivative_minorant :
    ((8:ℝ)/9)/(((15:ℝ)/2*(7/10)-1)^2) < 1/18 := by norm_num

theorem uniform_derivative_minorant :
    (3:ℝ)/4*(4/5)*(5/12)*(1/18)+(5/12)*(13/100)/(12*(7/10)^2) < 1/10 := by
  norm_num

end Cycle25.Arithmetic
