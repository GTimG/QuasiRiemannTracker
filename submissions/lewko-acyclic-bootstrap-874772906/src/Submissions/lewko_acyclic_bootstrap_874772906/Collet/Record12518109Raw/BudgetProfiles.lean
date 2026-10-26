/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.HeightProfiles
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.SourceMoment

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentFiniteProfileExceptional

private theorem branch_profile_bound (c diag D x C p h r : ℝ)(j d dmax : ℕ)
    (hc : 0≤c)(hd : 0≤diag)(hD : 0≤D)(hx : 0≤x)(hC : 0≤C)(hp : 0≤p)
    (hh : 1≤h)(hr : 0≤r)(hprofile : x≤C*p*h^j)(hdegree : d≤dmax) :
    c*diag*(D*x)^2*h^d*r≤C^2*c*D^2*diag*p^2*h^(j*2+dmax)*r := by
  have he:=pow_le_pow_left₀ (mul_nonneg hD hx) (mul_le_mul_of_nonneg_left hprofile hD) 2
  have hs:=mul_le_mul he (pow_le_pow_right₀ hh hdegree) (pow_nonneg (by linarith) _)
    (sq_nonneg (D*(C*p*h^j)))
  calc
    _=(c*diag)*((D*x)^2*h^d)*r:=by ring
    _≤(c*diag)*((D*(C*p*h^j))^2*h^dmax)*r:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (mul_nonneg hc hd)) hr
    _=_:=by rw [pow_add,pow_mul];ring

/-- One original profile control and one height degree bound both genuine
prior/natural derivative budgets. Constants precede all profiles, heights,
source coefficients and root scales. -/
theorem raw_source_budget_profile_control (a b : ℝ)(ha : 0<a)
    (TP TN : Finset (ℕ×ℕ)) :
    ∃j : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀(CP CN DP DN : ℝ),0≤CP → 0≤CN → 0≤DP → 0≤DN →
    ∀(degreeP degreeN : ℕ)(Φ : 𝓢(ℝ,ℂ))(p : Profiles a b)(v height Z M ε : ℝ),
      0≤height → 0≤Z →
      rawSourceBudget CP CN DP DN TP TN degreeP degreeN Φ
        (rawHeightProfile ha p 0 v) (rawHeightProfile ha p 1 v) v height Z M ε≤
      C*(CP*DP^2+CN*DN^2)*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|v|+height)^(j+max degreeP degreeN)*Z^(M+ε) := by
  obtain ⟨j,S,C,hC,hprofile⟩:=raw_height_profile_control a b ha (TP∪TN)
  refine ⟨j*2,S,C^2,sq_pos_of_pos hC,?_⟩
  intro CP CN DP DN hCP hCN hDP hDN degreeP degreeN Φ p v height Z M ε hh hZ
  have hctrl (T : Finset (ℕ×ℕ))(hT : T⊆TP∪TN) :
      sourceControl T (rawHeightProfile ha p 0 v)*sourceControl T (rawHeightProfile ha p 1 v)≤
      C*p.control S*(1+|v|+height)^j := by
    apply le_trans _ ((hprofile p v).trans _)
    · exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hT) _)
        (Seminorm.le_def.mp (Finset.sup_mono hT) _)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) j)
        (mul_nonneg hC.le (p.control_nonneg S))
  have hd:=QuadraticInitialBound.diagonalControl_nonneg Φ
  have hheight : 1≤1+|v|+height:=by linarith [abs_nonneg v]
  have hp:=branch_profile_bound CP (QuadraticInitialBound.diagonalControl Φ) DP
    (sourceControl TP (rawHeightProfile ha p 0 v)*sourceControl TP (rawHeightProfile ha p 1 v))
    C (p.control S) (1+|v|+height) (Z^(M+ε)) j degreeP (max degreeP degreeN)
    hCP hd hDP (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    hC.le (p.control_nonneg S) hheight (Real.rpow_nonneg hZ _)
    (hctrl TP Finset.subset_union_left) (le_max_left _ _)
  have hn:=branch_profile_bound CN (QuadraticInitialBound.diagonalControl Φ) DN
    (sourceControl TN (rawHeightProfile ha p 0 v)*sourceControl TN (rawHeightProfile ha p 1 v))
    C (p.control S) (1+|v|+height) (Z^(M+ε)) j degreeN (max degreeP degreeN)
    hCN hd hDN (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    hC.le (p.control_nonneg S) hheight (Real.rpow_nonneg hZ _)
    (hctrl TN Finset.subset_union_right) (le_max_right _ _)
  exact (add_le_add hp hn).trans_eq (by ring)

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.raw_source_budget_profile_control
