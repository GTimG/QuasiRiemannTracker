/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row119_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1447537741172983798684929792059710707496/37318998047758674969568359375:ℝ), (4300123586292160250847695414016751375736/37318998047758674969568359375:ℝ), (4257811816099754557956889698002668843384/37318998047758674969568359375:ℝ), (468408602434096660648812225348542725048/12439666015919558323189453125:ℝ)],
![(2862977459685187381552510950595938710096/37318998047758674969568359375:ℝ), (8503521352968221170421070736768691942128/37318998047758674969568359375:ℝ), (8418468214785282284474378293894033373168/37318998047758674969568359375:ℝ), (925974663997336854023447519240426713712/12439666015919558323189453125:ℝ)],
![(2266229417723547575688949204431165544/59710396876413879951309375:ℝ), (4206254764787205018794304527974347385592/37318998047758674969568359375:ℝ), (4163509398684207688781026490390699972584/37318998047758674969568359375:ℝ), (457882618045061893888087724853610350664/12439666015919558323189453125:ℝ)]]
theorem row119_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (57235327255632736736010965606701293833/24315657653606226313608897232896000000000:ℝ) row119_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row119_coefficients,Fin.sum_univ_succ]
 ring
theorem row119_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row119_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row119_coefficients]
#print axioms row119_identity
#print axioms row119_pos
end
end LewkoStage1Return.C30
