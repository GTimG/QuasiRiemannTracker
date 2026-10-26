/- Generated 2026-10-23 by exact rational Bernstein conversion.
Candidate c=3130677351/25000000000, h=400051/500000.
Compilation status is recorded separately; no new axioms are introduced.
Original mathematical/formal interface: Hailey Collet and Mark Lewko.
Original source released under Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def row037_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(53408332126508564321021463510137353/416632075721848508981308593750000:ℝ),(47502966331865943888779636034197917/138877358573949502993769531250000:ℝ),(252453976963065774465162610713886711/833264151443697017962617187500000:ℝ),(61042765033340026891751339735781/685814116414565446882812500000:ℝ)],
  ![(34235030464848057489460182102764617/208316037860924254490654296875000:ℝ),(28167819076964649931355582929666153/69438679286974751496884765625000:ℝ),(22855587509378865117262202719143089/69438679286974751496884765625000:ℝ),(728498082108463837845207908847817/8332641514436970179626171875000:ℝ)],
  ![(28393955226286702945300775695391881/416632075721848508981308593750000:ℝ),(21639112252196711217676539215048089/138877358573949502993769531250000:ℝ),(47975818198439963946420017026346041/416632075721848508981308593750000:ℝ),(2256133849875663807318297515318731/83326415144369701796261718750000:ℝ)]
]
theorem row037_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2256133849875663807318297515318731/37922777381259810950832000000000000:ℝ) row037_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row037_coefficients,Fin.sum_univ_succ] <;> ring
theorem row037_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row037_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_coefficients]
#print axioms row037_identity
#print axioms row037_pos
end
end RH20261023Finite
