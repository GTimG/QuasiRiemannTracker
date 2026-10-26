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
def row039_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(26987733345150725824662491358909628699/416632075721848508981308593750000:ℝ),(2868708559122882096202889524856013187/15430817619327722554863281250000:ℝ),(74026482862704090977647327065154572401/416632075721848508981308593750000:ℝ),(7852799347287322449341134167650615017/138877358573949502993769531250000:ℝ)],
  ![(22334333726333727027717245493896581627/208316037860924254490654296875000:ℝ),(21201603834072150869170163461228624219/69438679286974751496884765625000:ℝ),(20098747586290396918271756381876559811/69438679286974751496884765625000:ℝ),(19024906145894674104011525818340388403/208316037860924254490654296875000:ℝ)],
  ![(3681245725792869365540545673829457511/83326415144369701796261718750000:ℝ),(3460760753564971312586052339483736111/27775471714789900598753906250000:ℝ),(9740818840255754572655574820494525383/83326415144369701796261718750000:ℝ),(3039567596080262232685338866497774561/83326415144369701796261718750000:ℝ)]
]
theorem row039_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3039567596080262232685338866497774561/38832924038410046413651968000000000000:ℝ) row039_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row039_coefficients,Fin.sum_univ_succ] <;> ring
theorem row039_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row039_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_coefficients]
#print axioms row039_identity
#print axioms row039_pos
end
end RH20261023Finite
