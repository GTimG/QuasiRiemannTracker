/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B002
import Submissions.certb_local_20261013.Bundles.B030
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersDetectorScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales

/- BEGIN ORIGINAL MODULE Global.HighData ; sha256 5fab891167db300ab407c23b6042d10c1a1633701acf562a840f0105775cb875 -/
section





noncomputable section
open scoped BigOperators
namespace Submission20261012.Global.HighParameters

structure HighData (Δ : ℝ) where
  momentKappa : ℝ
  momentKappa_lo : 7/10 ≤ momentKappa
  momentKappa_hi : momentKappa ≤ 3/4
  momentKappa_beta : 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1 ≤ momentKappa
  momentKappa_exact : momentKappa = 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t<Δ/4
  t_gap : t ≤ Δ/100000
  t_small : t≤1/100000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=Submission20261012.Global.ell
  slots_bounds : ∀j,0 < ell j ∧ (7/8)*rmin ≤ ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps≤1
  sigma_pos : 0 < sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  central_budget : (159*ε+t+t+7*t)+(12*e+eps*(N+8))+
    (t+t+t+t+t*Submission20261012.Global.ell+(13243/1000)*e)+2*t ≤ Δ/100
  geometric_budget : sigma+8*e+t/8 ≤ 1/20
  principal_budget : sigma+t/8 ≤ 1/4000
  window_budget : sigma+e ≤ Submission20261012.Global.theta*((7/8)*rmin)
  floor_budget : 26*e+(N+8)*eps+t+t*Submission20261012.Global.ell+t/8+sigma ≤ 1/100
  high_saving : sigma+t/8+t/8 ≤ Δ/100
  weighted_top : 3*t ≤ Submission20261012.Global.rowExtension
  height_choice : ∀J : ℝ,0 ≤ J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ < t ∧ 2*τ*(1+J) ≤ t ∧ τ*(2+4*eps) < t

def HighData.toMomentData {Δ : ℝ} (D : HighData Δ) : Cycle25.Weighted.MomentData where
  N := D.N
  ell := D.ell
  t := D.t
  ε := D.ε
  e := D.e
  t_pos := D.t_pos
  t_small := D.t_small
  slots_injective := D.slots_injective
  slots_bounds := fun j=>⟨(D.slots_bounds j).1,by
    have hh := (D.slots_bounds j).2.2
    linarith only [hh,D.t_small]⟩
  epsilon_pos := D.epsilon_pos
  epsilon_small := D.epsilon_small
  e_pos := D.e_pos

/-- The new row extension imposes the stronger absolute loss bound. -/
theorem HighData.t_le_extension {Δ : ℝ} (D : HighData Δ) :
    D.t ≤ Submission20261012.Global.rowExtension/3 := by
  linarith [D.weighted_top]

/-- The old generic moment interface retains the new parameter values exactly. -/
@[simp] theorem HighData.toMomentData_t {Δ : ℝ} (D : HighData Δ) :
    D.toMomentData.t = D.t := rfl

@[simp] theorem HighData.toMomentData_ell {Δ : ℝ} (D : HighData Δ) :
    D.toMomentData.ell = D.ell := rfl

end Submission20261012.Global.HighParameters

end


/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
This submission uses the actual moment parameter and the new endpoint and row-extension budgets. -/

#print axioms Submission20261012.Global.HighParameters.HighData.toMomentData
#print axioms Submission20261012.Global.HighParameters.HighData.t_le_extension
end
/- END ORIGINAL MODULE Global.HighData -/

/- BEGIN ORIGINAL MODULE Global.Low.Geometry ; sha256 296c5818147e3104cef284b6aa62efae3894538adc07871f21dc696d24b018db -/
section


namespace Submission20261012.Global.LowGeometry

theorem theta_coarse : (874:ℝ)/1000 < Submission20261012.Global.theta := by
  rw [Submission20261012.Global.theta_eq]
  linarith [Submission20261012.Global.ell_interval.2]

theorem x_pos : 0 < Submission20261012.Global.lx := by
  linarith [Submission20261012.Global.x_rescaled_pos,Submission20261012.Global.ell_pos]

theorem signal_pos : 0 < Submission20261012.Global.signal Submission20261012.Global.theta := by
  rw [Submission20261012.Global.signal_low]
  linarith [x_pos,Submission20261012.Global.b_pos]

theorem scale_square : (2*Submission20261012.Global.lx-Submission20261012.Global.ly)+Submission20261012.Global.ly=2*Submission20261012.Global.lx := by ring

theorem gram_power (δ : ℝ) :
    Submission20261012.Global.lx+Submission20261012.Global.b*(1/6)+Submission20261012.Global.ly*δ =
      2*Submission20261012.Global.signal Submission20261012.Global.theta+Submission20261012.Global.ly*δ := by
  rw [Submission20261012.Global.signal_low]
  ring

theorem gram_sqrt_power (δ : ℝ) :
    (2*Submission20261012.Global.signal Submission20261012.Global.theta+Submission20261012.Global.ly*δ)*(1/2) =
      Submission20261012.Global.signal Submission20261012.Global.theta+(Submission20261012.Global.ly/2)*δ := by ring

theorem dilation_gap : 0 < 2*Submission20261012.Global.lx-Submission20261012.Global.ly-Submission20261012.Global.ell := by
  linarith [Submission20261012.Global.length_sum,Submission20261012.Global.ly_coarse.2,Submission20261012.Global.ell_interval.2]

theorem dilation_le_y : 2*Submission20261012.Global.lx-Submission20261012.Global.ly ≤ Submission20261012.Global.ly := by
  linarith [Submission20261012.Global.b_pos,Submission20261012.Global.length_difference]

end Submission20261012.Global.LowGeometry
end
/- END ORIGINAL MODULE Global.Low.Geometry -/

/- BEGIN ORIGINAL MODULE Global.SlotLengths ; sha256 ecfd372b6e52c572cf41719c7889c110715eadba45c40af71ff0f244249493f5 -/
section



/-! Distinct positive slot lengths with the new endpoint's prescribed sum.
The mesh is an arbitrary positive input, independent of the later slot type. -/
namespace Submission20261012.Global.HighParameters
noncomputable section
open scoped BigOperators

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0 < L) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0 < ell j ∧ ell j < L) ∧ (∑j,ell j)=Submission20261012.Global.ell := by
  have hscale : 0 < 6*Submission20261012.Global.ell := mul_pos (by norm_num) ell_pos
  obtain ⟨N,hN,old,hi,hb,hs⟩ := OAI.SevenEighths.Parameters.exists_distinct_slot_lengths
    (L/(6*Submission20261012.Global.ell)) (by positivity)
  refine ⟨N,hN,(fun j=>(6*Submission20261012.Global.ell:ℝ)*old j),?_,?_,?_⟩
  · intro j k he
    apply hi
    exact (mul_left_cancel₀ hscale.ne' he)
  · intro j
    constructor
    · exact mul_pos hscale (hb j).1
    · have hh := (hb j).2
      have hc := (lt_div_iff₀ hscale).mp hh
      nlinarith only [hc]
  · rw [←Finset.mul_sum,hs]
    ring

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ dmax) (hm : 0 < mesh) (hR : 0 < R) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0 < rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=Submission20261012.Global.ell ∧
      (∀j,0 < ell j ∧ dmax*rmin ≤ ell j ∧ ell j ≤ dmin*mesh ∧ ell j ≤ dmin*R) ∧
      (∀d : ℝ,dmin ≤ d → d ≤ dmax → ∀j,rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0 < dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0 < rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin ≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k ≤ dmin*mesh ∧ ell k ≤ dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0 < d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d ≤ dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end
end Submission20261012.Global.HighParameters

#print axioms Submission20261012.Global.HighParameters.exists_physical_slot_lengths

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Global.SlotLengths -/

/- BEGIN ORIGINAL MODULE Global.Transport.CentralErrorSaving ; sha256 1bb98bd008f7cb13d0c28d5d830d2289b605c48c5a626fdab243717fe07e5fd4 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/



open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤ Z) (ha : 0≤ a) (he : 0≤ e) :
    (Z^(Submission20261012.Global.lx:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(Submission20261012.Global.ly:ℝ))^((1-a-6*e)-1)≤ Z^(2:ℝ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith [Submission20261012.Global.length_sum, Submission20261012.Global.ly_coarse, Submission20261012.Global.ell_pos, mul_nonneg (by linarith [Submission20261012.Global.ly_coarse] : 0 ≤ Submission20261012.Global.ly) ha, mul_nonneg (by linarith [Submission20261012.Global.ly_coarse] : 0 ≤ Submission20261012.Global.ly) he])

lemma central_prime_product_bound {K : ℕ} (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0 < Z) (_hb : 0≤ b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(Submission20261012.Global.ell:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤ b^K*Z^(Submission20261012.Global.ell:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤ Z) (hb : 0≤ b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((Submission20261012.Global.h:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(Submission20261012.Global.ell:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Submission20261012.Global.ell) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (Submission20261012.Global.h:ℝ)+ζ≤1 by linarith [Submission20261012.Global.h_interval]))
  have hp := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=> Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(Submission20261012.Global.ell:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((Submission20261012.Global.ell:ℝ)*(3:ℕ))=Z^(6+3*Submission20261012.Global.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CentralErrorSaving -/

/- BEGIN ORIGINAL MODULE Global.Transport.GeometryFacts ; sha256 81a22db23d4715d2e96d2211941fe743f0f6af1096853df2ae34f76d76524b62 -/
section

namespace Submission20261012.Global.Transport
lemma theta_lower : (874:ℝ)/1000 < Submission20261012.Global.theta := by
  rw [Submission20261012.Global.theta_eq]
  linarith [Submission20261012.Global.ell_interval]
lemma theta_bounds : (874:ℝ)/1000 < Submission20261012.Global.theta ∧ Submission20261012.Global.theta < 7/8 :=
  ⟨theta_lower, Submission20261012.Global.theta_lt_seven_eighths⟩
lemma small_saving : (7/100:ℝ) < Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50 := by
  linarith [Submission20261012.Global.ly_coarse, Submission20261012.Global.h_interval]
end Submission20261012.Global.Transport
end
/- END ORIGINAL MODULE Global.Transport.GeometryFacts -/

/- BEGIN ORIGINAL MODULE Global.Transport.TailScales ; sha256 e7ffacb2dafd227b07addc40ccf95451a022ae6d1bbb814c8f263748bd2b378b -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/



open OAI OAI.SevenEighths

noncomputable section
open scoped BigOperators
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Submission20261012.Global.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(Submission20261012.Global.lx:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(Submission20261012.Global.ly:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Submission20261012.Global.row_endpoint, Submission20261012.Global.b]
  linarith [Submission20261012.Global.length_sum]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Submission20261012.Global.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(Submission20261012.Global.lx:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(Submission20261012.Global.ly:ℝ))^((2:ℝ)-1))=
      Z^((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+(Submission20261012.Global.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Submission20261012.Global.row_endpoint]
  ring

end Submission20261012.Global.HighRowFamily
end


end
/- END ORIGINAL MODULE Global.Transport.TailScales -/
