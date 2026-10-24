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
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2393786567261639852997338582270594911/694386792869747514968847656250:ℝ),(6985746667594290971965644689136455087/694386792869747514968847656250:ℝ),(13584982663511797525829702881784460953/1388773585739495029937695312500:ℝ),(1467015250732764404959920479715496867/462924528579831676645898437500:ℝ)],
  ![(2122404982862212110278184761844015997/347193396434873757484423828125:ℝ),(6177345129136302092010845851094503403/347193396434873757484423828125:ℝ),(239596689145201343632459375368205042/13887735857394950299376953125:ℝ),(644989266220832670986769018891129548/115731132144957919161474609375:ℝ)],
  ![(373495658132454428076091240376335253/138877358573949502993769531250:ℝ),(1083709143959422817766209580008185639/138877358573949502993769531250:ℝ),(1047434463088663079637045866580105269/138877358573949502993769531250:ℝ),(112406304739568926566122787628584961/46292452857983167664589843750:ℝ)]
]
theorem row006_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (112406304739568926566122787628584961/690363094016178602909368320000000000:ℝ) row006_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
#print axioms row006_identity
#print axioms row006_pos
end
end RH20261023Finite
