import Candidate.Target836.SourceProvider.NamedBounds
set_option autoImplicit false
namespace Target874836.SourceProvider.Named
noncomputable section
/-- Error deletion retains the accepted three-quarter incumbent. -/
def errorGap (b : ℝ) : ℝ := B-1+(9/2-lam)*b

theorem errorGap_pos {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) : 0 < errorGap b := by
  norm_num [errorGap,B,lam] at *
  linarith [hb.1]

theorem first_error_reserve {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    1/1000 ≤ amp b/4-errorGap b/6 := by
  norm_num [amp,K,extra,gap,errorGap,B,lam,q,kappa,incumbentKappa,lowReserve] at *
  linarith [hb.1,hb.2]

theorem sixth_error_reserve {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    11360006033/482529600000 ≤ 13*amp b/4-errorGap b/6 := by
  norm_num [amp,K,extra,gap,errorGap,B,lam,q,kappa,incumbentKappa,lowReserve] at *
  linarith [hb.1,hb.2]

theorem seventh_error_reserve {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    3516816899/120632400000 ≤ 4*amp b-errorGap b/6 := by
  norm_num [amp,K,extra,gap,errorGap,B,lam,q,kappa,incumbentKappa,lowReserve] at *
  linarith [hb.1,hb.2]
end
end Target874836.SourceProvider.Named
#print axioms Target874836.SourceProvider.Named.first_error_reserve
#print axioms Target874836.SourceProvider.Named.sixth_error_reserve
#print axioms Target874836.SourceProvider.Named.seventh_error_reserve
