/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row124_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2786565237877977913789638220451630771636/600080871373666668502435546875:ℝ),(73665343810415959504945883776544940132692/5400727842363000016521919921875:ℝ),(72106757744375585288451937169997208410112/5400727842363000016521919921875:ℝ),(23520476044946684223901810736891945222144/5400727842363000016521919921875:ℝ)],
![(5521990754941798105037269604071816353824/600080871373666668502435546875:ℝ),(145933478440799340314020194193928585660704/5400727842363000016521919921875:ℝ),(2196923520855245843087896421467077197824/83088120651738461792644921875:ℝ),(46564416826471695022236062013077779382272/5400727842363000016521919921875:ℝ)],
![(101382473002454656914205198014671978432/22225217458283950685275390625:ℝ),(72319323319376777100154487284488570807104/5400727842363000016521919921875:ℝ),(70744315103748448062204544239386126024704/5400727842363000016521919921875:ℝ),(23060907370044940089209596622462845976576/5400727842363000016521919921875:ℝ)]]
theorem row124_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (43985190143670921495837395901609127/20135372793008444818931515392000000000:ℝ) row124_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row124_coefficients,Fin.sum_univ_succ]
 ring
theorem row124_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row124_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row124_coefficients]
#print axioms row124_identity
#print axioms row124_pos
end
end LewkoStage2Finite
