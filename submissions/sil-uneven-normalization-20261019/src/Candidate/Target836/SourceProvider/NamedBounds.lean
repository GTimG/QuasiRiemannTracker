import Candidate.Target836.SourceProvider.NamedSource
set_option autoImplicit false
namespace Target874836.SourceProvider.Named
noncomputable section

theorem gap_pos {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) : 0 < gap b := by
  norm_num [gap, B, lam, kappa, incumbentKappa] at *
  linarith [hb.1]

theorem amp_bounds {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    902420521/120632400000 ≤ amp b ∧ amp b ≤ 226566043/17233200000 := by
  norm_num [amp, K, extra, gap, B, lam, q, kappa, incumbentKappa, lowReserve] at *
  constructor <;> linarith [hb.1,hb.2]

theorem amp_pos {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) : 0 < amp b := by
  linarith [(amp_bounds hb).1]

theorem main_fixed_reserve {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    1/50 ≤ 1-total b-4*amp b := by
  norm_num [amp, K, extra, gap, B, lam, q, kappa, incumbentKappa, lowReserve,total,mesh] at *
  linarith [hb.1,hb.2]

theorem error_fixed_reserve {b : ℝ} (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    1/50 ≤ 1-total b-(9/2)*amp b := by
  norm_num [amp, K, extra, gap, B, lam, q, kappa, incumbentKappa, lowReserve,total,mesh] at *
  linarith [hb.1,hb.2]
end
end Target874836.SourceProvider.Named
#print axioms Target874836.SourceProvider.Named.amp_bounds
#print axioms Target874836.SourceProvider.Named.amp_pos
#print axioms Target874836.SourceProvider.Named.main_fixed_reserve
#print axioms Target874836.SourceProvider.Named.error_fixed_reserve
