/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B047
import Submissions.cycle61_c0125139.Bundles.B053
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

/- BEGIN ORIGINAL Cycle25.Arithmetic.Endpoint; sha256 51dadfc13d1cc0d7d28b6e685f0be2c2503b9e011cd6866e2bc53abc00942fb9 -/
section
                                                
                                          
                                               
                     

/-! Exact arithmetic for T1 of the selected Cycle25 proof packet.
The endpoint is an algebraic real, specified by its polynomial and isolating interval.
These declarations make no assertion about Hecke or Dirichlet L-functions. -/

namespace Cycle25.Arithmetic

def quartic (x : ℝ) : ℝ := 927*x^4 - 3135*x^3 + 2433*x^2 + 275*x - 100
noncomputable def rootLo : ℝ := 16712007850680 / 100000000000000
noncomputable def rootHi : ℝ := 16712007850682 / 100000000000000

theorem rootLo_lt_rootHi : rootLo < rootHi := by norm_num [rootLo, rootHi]
theorem rootLo_coarse : (1:ℝ)/6 < rootLo := by norm_num [rootLo]
theorem rootHi_coarse : rootHi < (1:ℝ)/5 := by norm_num [rootHi]
theorem quartic_rootLo_neg : quartic rootLo < 0 := by norm_num [quartic, rootLo]
theorem quartic_rootHi_pos : 0 < quartic rootHi := by norm_num [quartic, rootHi]

theorem quartic_continuous : Continuous quartic := by unfold quartic; fun_prop

theorem quartic_hasDerivAt (x : ℝ) :
    HasDerivAt quartic (3708*x^3 - 9405*x^2 + 4866*x + 275) x := by
  unfold quartic
  convert ((((((hasDerivAt_id x).pow 4).const_mul 927).sub
    (((hasDerivAt_id x).pow 3).const_mul 3135)).add
    (((hasDerivAt_id x).pow 2).const_mul 2433)).add
    ((hasDerivAt_id x).const_mul 275)).sub_const 100 using 1
  · ext y; simp
  · simp; ring

theorem quartic_derivative_lower {x : ℝ} (hx : x ∈ Set.Icc (1/6:ℝ) (1/5)) :
    (3549:ℝ)/5 ≤ 3708*x^3 - 9405*x^2 + 4866*x + 275 := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2 : x^2 ≤ (1:ℝ)/25 := by nlinarith [hx.2]
  have hx3 : 0 ≤ x^3 := pow_nonneg hx0 _
  nlinarith [hx.1]

theorem quartic_strictMonoOn : StrictMonoOn quartic (Set.Icc (1/6:ℝ) (1/5)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) quartic_continuous.continuousOn
  intro x hx
  rw [(quartic_hasDerivAt x).deriv]
  have hxc : x ∈ Set.Icc (1/6:ℝ) (1/5) := interior_subset hx
  linarith [quartic_derivative_lower hxc]

theorem exists_isolated_root : ∃ x : ℝ, rootLo < x ∧ x < rootHi ∧ quartic x = 0 := by
  have h := intermediate_value_Icc (le_of_lt rootLo_lt_rootHi)
    quartic_continuous.continuousOn
  obtain ⟨x, hx, hpx⟩ := h (show (0:ℝ) ∈ Set.Icc (quartic rootLo) (quartic rootHi) from
    ⟨le_of_lt quartic_rootLo_neg, le_of_lt quartic_rootHi_pos⟩)
  refine ⟨x, ?_, ?_, hpx⟩
  · exact lt_of_le_of_ne hx.1 (by intro he; subst x; linarith [quartic_rootLo_neg])
  · exact lt_of_le_of_ne hx.2 (by intro he; subst x; linarith [quartic_rootHi_pos])

noncomputable def ell0 : ℝ := Classical.choose exists_isolated_root
theorem ell0_lo : rootLo < ell0 := (Classical.choose_spec exists_isolated_root).1
theorem ell0_hi : ell0 < rootHi := (Classical.choose_spec exists_isolated_root).2.1
theorem ell0_quartic : quartic ell0 = 0 := (Classical.choose_spec exists_isolated_root).2.2
theorem ell0_coarse : ell0 ∈ Set.Icc (1/6:ℝ) (1/5) :=
  ⟨le_of_lt (rootLo_coarse.trans ell0_lo), le_of_lt (ell0_hi.trans rootHi_coarse)⟩

theorem quartic_root_unique {x : ℝ} (hx : x ∈ Set.Icc (1/6:ℝ) (1/5))
    (hp : quartic x = 0) : x = ell0 :=
  quartic_strictMonoOn.injOn hx ell0_coarse (hp.trans ell0_quartic.symm)

noncomputable def b0 : ℝ := 11/12 - ell0/4
noncomputable def kappa0 : ℝ := (5-3*ell0)/6
noncomputable def theta : ℝ := 683505193/781250000

theorem kappa0_eq : kappa0 = 2*b0-1 := by unfold kappa0 b0; ring
theorem b0_lt_theta : b0 < theta := by
  have h := ell0_lo
  norm_num [rootLo] at h
  unfold b0 theta
  linarith

theorem theta_gap : 0 < theta-b0 ∧ theta-b0 < (4:ℝ)/100000000000000 := by
  constructor
  · linarith [b0_lt_theta]
  · have h := ell0_hi
    norm_num [rootHi] at h
    unfold theta b0
    linarith

theorem kappa0_range : (7:ℝ)/10 < kappa0 ∧ kappa0 < (3:ℝ)/4 := by
  have h := ell0_lo
  have h' := ell0_hi
  norm_num [rootLo, rootHi] at h h'
  unfold kappa0
  constructor <;> linarith

theorem theta_catalogue_chain : theta < (10499:ℝ)/12000 ∧
    (10499:ℝ)/12000 < 874957019420098946128604623/1000000000000000000000000000 ∧
    (874957019420098946128604623:ℝ)/1000000000000000000000000000 < 7/8 := by
  norm_num [theta]

end Cycle25.Arithmetic

end
/- END ORIGINAL Cycle25.Arithmetic.Endpoint -/

/- BEGIN ORIGINAL Cycle25.Arithmetic.Geometry; sha256 c0145ee4ec60383eaad9011778e34009b311e96fbb831bae5676620911966140 -/
section
                                  

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

end
/- END ORIGINAL Cycle25.Arithmetic.Geometry -/

/- BEGIN ORIGINAL Cycle25.Assembly.Parameters; sha256 c4237d0be578f95a5fa606684dd3b66a1eddf8d8ac48afd45e19d59c856b11b7 -/
section
                                  

/-! Physical geometry at the exact Cycle25 algebraic boundary. -/
noncomputable section
namespace Cycle25

def theta : ℝ := Arithmetic.b0
def ell : ℝ := Arithmetic.ell0
def lx : ℝ := Arithmetic.x0
def ly : ℝ := Arithmetic.y0
def h : ℝ := Arithmetic.h0
def b : ℝ := ly-lx
def rowExtension : ℝ := 1/1000000
def signal (s : ℝ) : ℝ := s-(4+b)/6

theorem ell_interval : (16712:ℝ)/100000 < ell ∧ ell < 167121/1000000 :=
  Arithmetic.ell0_short_interval
theorem h_interval : (793:ℝ)/1000 < h ∧ h < 795/1000 := Arithmetic.h0_interval
theorem theta_eq : theta = 11/12-ell/4 := rfl
theorem theta_pos : 0 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_gt_half : (1:ℝ)/2 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_lt_seven_eighths : theta < (7:ℝ)/8 := by rw [theta_eq]; linarith [ell_interval.1]
theorem theta_lt_one : theta < 1 := theta_lt_seven_eighths.trans (by norm_num)
theorem length_sum : lx+ly = 1-ell := by unfold lx ly ell Arithmetic.x0 Arithmetic.y0; ring
theorem length_difference : ly-lx=b := rfl
theorem row_endpoint : h=1-lx+ell := by unfold h lx ell Arithmetic.x0; ring
theorem y_endpoint : ly=h-2*ell := rfl
theorem signal_low : signal theta=lx/2+b/12 := by
  rw [signal,theta_eq]
  have := length_sum
  unfold b
  linarith
theorem signal_slope (s t : ℝ) : signal s-signal t=s-t := by unfold signal; ring
theorem ell_pos : 0 < ell := by linarith [ell_interval.1]
theorem ell_lt_one_fifth : ell < (1:ℝ)/5 := by linarith [ell_interval.2]
theorem x_rescaled_pos : 0 < lx-ell := sub_pos.mpr Arithmetic.physical_geometry.1
theorem b_pos : 0 < b := sub_pos.mpr Arithmetic.physical_geometry.2.1
theorem ly_lt_half : ly < (1:ℝ)/2 := Arithmetic.physical_geometry.2.2.2.1
theorem ly_coarse : (458:ℝ)/1000 < ly ∧ ly < 461/1000 := by
  rw [y_endpoint]
  constructor <;> linarith [h_interval.1,h_interval.2,ell_interval.1,ell_interval.2]
theorem y_rescaled_pos : 0 < ly-ell := by linarith [ly_coarse.1,ell_interval.2]
theorem row_rescaled_pos : 0 < 1-3*ell := by linarith [ell_interval.2]
theorem gram_domination : 0 < ly-ell-(11:ℝ)/6*b := by
  have := length_sum
  unfold b
  linarith [ly_coarse.2,ell_interval.2]
theorem h_pos : 0 < h := by linarith [h_interval.1]
theorem h_gt_half : (1:ℝ)/2 < h := by linarith [h_interval.1]
theorem h_lt_one : h < 1 := by linarith [h_interval.2]
theorem rowExtension_pos : 0 < rowExtension := by norm_num [rowExtension]
theorem extended_row_count_supply : (7:ℝ)/37 < ell/(h+rowExtension) := by
  apply (lt_div_iff₀ (add_pos h_pos rowExtension_pos)).2
  norm_num [rowExtension]
  linarith [ell_interval.1,h_interval.2]
theorem row_count_supply : (7:ℝ)/37 < ell/h := by
  apply (lt_div_iff₀ h_pos).2
  linarith [ell_interval.1,h_interval.2]
theorem row_extension_supply : h < 5*ell := by linarith [h_interval.2,ell_interval.1]
theorem numerator_short : h < 2*ly := Arithmetic.physical_geometry.2.2.2.2.2
theorem extended_numerator_short : h+rowExtension < 2*ly := by
  rw [y_endpoint]
  norm_num [rowExtension]
  linarith [h_interval.1,ell_interval.2]
theorem extended_h_lt_one : h+rowExtension < 1 := by
  norm_num [rowExtension]
  linarith [h_interval.2]
theorem extended_row_supply : h+rowExtension < 5*ell := by
  norm_num [rowExtension]
  linarith [h_interval.2,ell_interval.1]
theorem numerator_supply_all {kap d : ℝ} (hk : 7/10 ≤ kap) (hd : (1:ℝ)/2 ≤ d) :
    (2*ly-d)/(6*kap) < ell := by
  apply (div_lt_iff₀ (by linarith : 0 < 6*kap)).2
  have hprod := mul_le_mul_of_nonneg_left hk ell_pos.le
  nlinarith [ly_coarse.2,ell_interval.1]
theorem low_rescaled_tuple {v : ℝ} (hv : 0 ≤ v) :
    -v+max 0 (5*ell-1+v)/8 ≤ 0 := by
  have hm : max 0 (5*ell-1+v) ≤ 8*v := max_le (by linarith) (by linarith [ell_lt_one_fifth])
  linarith
theorem low_rescaled_identity (v : ℝ) :
    (1-ell-2*v)+(ell-v)-1 = -3*v := by ring
theorem small_row_margin : h*(17/50-1/6)-ly/2+(63:ℝ)/5000 < 0 := by
  dsimp only [h,ly]
  linarith [Arithmetic.small_row_margin]
theorem principal_w_margin : 0 < ly/20 := by linarith [ly_coarse.1]
theorem principal_z_margin : 0 < h/600 := by linarith [h_pos]

end Cycle25

end
/- END ORIGINAL Cycle25.Assembly.Parameters -/

/- BEGIN ORIGINAL Cycle25.Numerator.BoxGeometry; sha256 83b0af1bb645fd02f94e7f3e84d68f66a4b6d866f9797bbbb75a09868da528b7 -/
section
                                
                                      
                                  

/-! Exact scale and capacity bookkeeping for finite coefficient-dilation boxes. -/
noncomputable section
open scoped BigOperators Classical
open Filter
namespace Cycle25.Numerator

lemma physical_y_range (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension) :
    (1/2:ℝ) < Cycle25.ly/d ∧ Cycle25.ly/d < 1 := by
  have hdp : 0 < d := by linarith
  constructor
  · apply (lt_div_iff₀ hdp).mpr
    have hh := Cycle25.extended_numerator_short
    linarith
  · apply (div_lt_one hdp).mpr
    exact Cycle25.ly_lt_half.trans_le hd

/-- The coarse finite box range suffices: the maximum reflected length remains
below the fixed L=2 empty-slot endpoint, uniformly in all actual high dyads. -/
theorem reflected_box_geometry (d v boxWidth annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hv:0 ≤ v) (hvmax:v ≤ 1+boxWidth) (hbox:0 ≤ boxWidth)
    (hann:0 ≤ annulusSlack) (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    0 ≤ 1-Cycle25.ly/d+v+boxWidth ∧
      (1-Cycle25.ly/d+v+boxWidth)+annulusSlack ≤ 2 := by
  obtain ⟨hylo,hyhi⟩ := physical_y_range d hd hdmax
  constructor <;> linarith

/-- A dilation-box upper edge bounds the combined primitive-plus-redundant
conductor relative to the actual original scale Y/N. -/
theorem combined_scale_of_dilation_box (U C Cu rowSize N y v boxWidth:ℝ)
    (hU:0 < U) (hC:0 < C) (hrow:0 < rowSize) (hrowU:rowSize ≤ U) (hN:0 < N)
    (hbox:max 1 (Cu*N/(C*rowSize)) ≤ U^(v+boxWidth)) :
    Cu ≤ C*U^(1-y+v+boxWidth)*(U^y/N) := by
  have hb : Cu*N ≤ U^(v+boxWidth)*(C*rowSize) :=
    (div_le_iff₀ (mul_pos hC hrow)).mp ((le_max_right _ _).trans hbox)
  have hprod : Cu*N ≤ C*(U^(v+boxWidth)*U) := by
    calc
      _ ≤ U^(v+boxWidth)*(C*rowSize) := hb
      _ ≤ U^(v+boxWidth)*(C*U) := by gcongr
      _ = _ := by ring
  have hpow : U^(1-y+v+boxWidth)*U^y = U^(v+boxWidth)*U := by
    rw [←Real.rpow_add hU]
    calc
      _ = U^(v+boxWidth+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hU,Real.rpow_one]
  have he : C*U^(1-y+v+boxWidth)*(U^y/N) =
      (C*(U^(v+boxWidth)*U))/N := by
    calc
      _ = (C*(U^(1-y+v+boxWidth)*U^y))/N := by ring
      _ = _ := by rw [hpow]
  rw [he]
  exact (le_div_iff₀ hN).mpr hprod

lemma capacity_shift_exact (kap y v boxWidth annulusSlack:ℝ) :
    selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) =
      selectedCapacity kap ((2*y-1)/(6*kap)) (v+boxWidth+annulusSlack) := by
  unfold selectedCapacity
  congr 1
  ring

/-- A positive selected family fits the reflected two-plain capacity. If the
capacity has saturated to zero, positivity forces the selected family empty. -/
theorem physical_reflected_capacity_or_empty {ι:Type*} (T:Finset ι)
    (width:ι→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0<kap)
    (hw:∀i∈T,0 < width i)
    (hselected:(∑i∈T,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i∈T,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw :=
      max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 :=
      max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun j hj=>(hw j hj).le) hi
    linarith [hw i hi]

/-- The annular tolerance changes the selected-slot exponent by exactly its
linear capacity cost; it can be included in the final small loss budget. -/
lemma annular_capacity_saving_loss (kap q y annulusSlack:ℝ) :
    -q*((2*y-1)/(6*kap)-annulusSlack/(3*kap))/2 =
      -q*((2*y-1)/(6*kap))/2+q*annulusSlack/(6*kap) := by ring


/-- A convenient uniform positive margin for the selected base capacity. -/
lemma physical_y_strong_lower (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension) :
    (11/20:ℝ) < Cycle25.ly/d := by
  have hdp : 0 < d := by linarith
  apply (lt_div_iff₀ hdp).mpr
  have hh := Cycle25.h_interval
  have hy := Cycle25.ly_coarse
  norm_num [Cycle25.rowExtension] at *
  linarith

lemma shifted_base_capacity_pos (kap d annulusSlack:ℝ)
    (hkap:0<kap) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hann:annulusSlack ≤ 1/100) :
    0 < (2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) := by
  have hh := physical_y_strong_lower d hd hdmax
  have hid : (2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) =
      (2*(Cycle25.ly/d)-1-2*annulusSlack)/(6*kap) := by ring
  rw [hid]
  exact div_pos (by linarith) (by positivity)

def coefficientBoxCount (xi:ℝ) : ℕ := ⌈1/xi⌉₊

lemma coefficientBoxCount_extent (xi:ℝ) (hxi:0 < xi) :
    1 ≤ (coefficientBoxCount xi:ℝ)*xi ∧
      (coefficientBoxCount xi:ℝ)*xi < 1+xi := by
  have hlo := Nat.le_ceil (1/xi)
  have hhi := Nat.ceil_lt_add_one (by positivity:(0:ℝ) ≤ 1/xi)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlo hxi.le
    simpa only [coefficientBoxCount,div_mul_cancel₀ _ hxi.ne'] using hh
  · have hh := mul_lt_mul_of_pos_right hhi hxi
    dsimp [coefficientBoxCount]
    simpa only [add_mul,div_mul_cancel₀ _ hxi.ne',one_mul] using hh

lemma coefficient_box_index_range (xi:ℝ) (hxi:0 < xi) (j:ℕ)
    (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ (j:ℝ)*xi ∧ (j:ℝ)*xi ≤ 1+xi := by
  have hjn : j ≤ coefficientBoxCount xi := by have := Finset.mem_range.mp hj; omega
  have hjr : (j:ℝ) ≤ (coefficientBoxCount xi:ℝ) := by exact_mod_cast hjn
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hxi.le,
    (mul_le_mul_of_nonneg_right hjr hxi.le).trans (coefficientBoxCount_extent xi hxi).2.le⟩

/-- A fixed source cutoff fits below U uniformly in every weighted high dyad. -/
theorem eventually_physical_cutoff_le_base (b:ℝ) (hb:0 ≤ b) :
    ∀ᶠU:ℝ in Filter.atTop, 1 < U ∧ ∀d:ℝ,(1/2:ℝ) ≤ d →
      b*U^(Cycle25.ly/d) ≤ U := by
  have he : ∀ᶠU:ℝ in Filter.atTop, b ≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/20)).eventually (Filter.eventually_ge_atTop _)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0 < d := by linarith
  have hy : Cycle25.ly/d ≤ 19/20 := by
    apply (div_le_iff₀ hdp).mpr
    linarith [Cycle25.ly_coarse.2]
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := by
      exact mul_le_mul he (Real.rpow_le_rpow_of_exponent_le hU.le hy)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by
      rw [←Real.rpow_add (zero_lt_one.trans hU)]
      norm_num

/-- The finite box range and the reflected scale range use the same actual
parameters; no unbounded coefficient tail remains after the source cutoff. -/
theorem physical_coefficient_box_geometry (d xi annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hxi:0 < xi) (hann:0 ≤ annulusSlack) (hsmall:2*xi+annulusSlack ≤ 1/2)
    (j:ℕ) (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ 1-Cycle25.ly/d+(j:ℝ)*xi+xi ∧
      (1-Cycle25.ly/d+(j:ℝ)*xi+xi)+annulusSlack ≤ 2 := by
  obtain ⟨hv,hvmax⟩ := coefficient_box_index_range xi hxi j hj
  exact reflected_box_geometry d ((j:ℝ)*xi) xi annulusSlack hd hdmax hv hvmax hxi.le hann hsmall


lemma physical_reflected_capacity_or_empty_subtype {ι:Type*} (T:Finset ι)
    (width:T→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0<kap)
    (hw:∀i,0 < width i)
    (hselected:(∑i,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw := max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 := max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
    linarith [hw ⟨i,hi⟩]

end Cycle25.Numerator

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.BoxGeometry -/
