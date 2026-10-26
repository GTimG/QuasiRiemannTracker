/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row035_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10034080381738291525365731722610963/17776309841410594989515625000000:ℝ), (2806207846470224349750007430880883/1975145537934510554390625000000:ℝ), (4324459448763903241103938877953/3657676922100945471093750000:ℝ), (1442829117903434504813748822883649/4444077460352648747378906250000:ℝ)],
![(188942019866975577791047359847573/246893192241813819298828125000:ℝ), (80639510091929394341720361808141/44440774603526487473789062500:ℝ), (3129424923631099214122269903971279/2222038730176324373689453125000:ℝ), (131667587812618054518956758698731/370339788362720728948242187500:ℝ)],
![(268978944230954702986456714782823/1111019365088162186844726562500:ℝ), (583880783902335924676580098174633/1111019365088162186844726562500:ℝ), (202305582852325884057387819079361/555509682544081093422363281250:ℝ), (21767158928175855769334938691728/277754841272040546711181640625:ℝ)]]
theorem row035_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1360447433010990985583433668233/31602328606952168870250000000000:ℝ) row035_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row035_coefficients,Fin.sum_univ_succ]
 ring
theorem row035_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_coefficients]
#print axioms row035_identity
#print axioms row035_pos
end
end Record1252270103Finite
