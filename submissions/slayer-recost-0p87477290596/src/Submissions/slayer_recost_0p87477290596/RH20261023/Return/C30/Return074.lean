/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row074_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4091673928441068894631849/1049350051657766390625:ℝ), (1359101496923874256561484207/131168756457220798828125:ℝ), (1199738596860154931284190839/131168756457220798828125:ℝ), (351812964453803746926687757/131168756457220798828125:ℝ)],
![(831419517531319742916259546/131168756457220798828125:ℝ), (416905240718568365116765814/26233751291444159765625:ℝ), (1713480083228887050864093002/131168756457220798828125:ℝ), (459664955823338619134023478/131168756457220798828125:ℝ)],
![(462571110162349742778013271/131168756457220798828125:ℝ), (1137212875453022482471182563/131168756457220798828125:ℝ), (1820411268125250376679166251/262337512914441597656250:ℝ), (470242185863871960964702667/262337512914441597656250:ℝ)]]
theorem row074_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (229832477911669309567011739/61129071098171891712000000000:ℝ) row074_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row074_coefficients,Fin.sum_univ_succ]
 ring
theorem row074_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row074_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row074_coefficients]
#print axioms row074_identity
#print axioms row074_pos
end
end RH20261023Return.C30
