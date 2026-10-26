/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![![(37454597916135263189457509/5925528642127921875000:ℝ), (62745091011949767031906601/3555317185276753125000:ℝ), (291278437749085391963744629/17776585926383765625000:ℝ), (29968738110130464374194717/5925528642127921875000:ℝ)],
![(80637873901340166544758287/8888292963191882812500:ℝ), (73420146398800465269060487/2962764321063960937500:ℝ), (199701268216489982013093361/8888292963191882812500:ℝ), (20020953253467440958556729/2962764321063960937500:ℝ)],
![(54783360224131253021345047/17776585926383765625000:ℝ), (144971254904728925147053517/17776585926383765625000:ℝ), (126806918751875708042046343/17776585926383765625000:ℝ), (51039413291127463185269/24793006870828125000:ℝ)]]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (51039413291127463185269/361074332952576000000000:ℝ) row003_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row003_coefficients,Fin.sum_univ_succ]
 ring
theorem row003_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row003_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]
#print axioms row003_identity
#print axioms row003_pos
end
end RH20261023Return.C30
