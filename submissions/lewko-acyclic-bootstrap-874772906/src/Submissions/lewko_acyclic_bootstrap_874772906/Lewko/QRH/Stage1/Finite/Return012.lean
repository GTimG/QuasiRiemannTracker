/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row012_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4611693746356413946932790574489227213163/1866415745721910063787947265625:ℝ),(135657342035338623839880119408958830477/18479363819028812512751953125:ℝ),(2713644031066467765149659430458089306901/373283149144382012757589453125:ℝ),(497613531571673178666065087941647985499/207379527302434451531994140625:ℝ)],
![(8904289183224249428125342250629249462966/1866415745721910063787947265625:ℝ),(5289625762599390078449945641248879788698/373283149144382012757589453125:ℝ),(1378128070278903925510201132763040787438/98232407669574213883576171875:ℝ),(960065836830396290487330354653625053422/207379527302434451531994140625:ℝ)],
![(4295280568904862929330647758989195615603/1866415745721910063787947265625:ℝ),(12754794528940150916302598045360994528433/1866415745721910063787947265625:ℝ),(12624272123009296148026192582971966737267/1866415745721910063787947265625:ℝ),(462750840055498899121297341983351980493/207379527302434451531994140625:ℝ)]]
theorem row012_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (462750840055498899121297341983351980493/3166891689329404695159509090304000000000:ℝ) row012_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row012_coefficients,Fin.sum_univ_succ]
 ring
theorem row012_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row012_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_coefficients]
#print axioms row012_identity
#print axioms row012_pos
end
end LewkoStage1Finite
