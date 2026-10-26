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
def row038_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2268019569704144033017174881566617787/833264151443697017962617187500000:ℝ),(1264961826889554015187172201333682781/166652830288739403592523437500000:ℝ),(1955481780225272050734162397850553683/277754717147899005987539062500000:ℝ),(201034693454963742319955743716651659/92584905715966335329179687500000:ℝ)],
  ![(1664146683142784980517695164181288747/416632075721848508981308593750000:ℝ),(4529944760175995009780917433626658641/416632075721848508981308593750000:ℝ),(1364650222677344501043655764089534647/138877358573949502993769531250000:ℝ),(136404143193616536806827328924803783/46292452857983167664589843750000:ℝ)],
  ![(417100571669591007905111981058331969/277754717147899005987539062500000:ℝ),(1099383921945894863486530415247706459/277754717147899005987539062500000:ℝ),(319434330107294684614408478731184987/92584905715966335329179687500000:ℝ),(10213406996942328776246572990895573/10287211746218481703242187500000:ℝ)]
]
theorem row038_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (30640220990826986328739718972686719/449455139333449611269120000000000000:ℝ) row038_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row038_coefficients,Fin.sum_univ_succ] <;> ring
theorem row038_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row038_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_coefficients]
#print axioms row038_identity
#print axioms row038_pos
end
end RH20261023Finite
