/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row051_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2873570066549482763035325865117460278643/21356851822279341131250000000:ℝ),(300225624260740421022394726255774029807289/747489813779776939593750000000:ℝ),(2333824639060626449934157414651012033792/5839764170154507340576171875:ℝ),(258017914829888145198951103154079740288/1946588056718169113525390625:ℝ)],
![(791633056889366014452623144143987018067/2966229419761019601562500000:ℝ),(49623469987979700169115325047612467264463/62290817814981411632812500000:ℝ),(4628867433606346865815613268684586855936/5839764170154507340576171875:ℝ),(1535194662509261774868027840582517491712/5839764170154507340576171875:ℝ)],
![(3532900482302186101722618689448719572231/26696064777849176414062500000:ℝ),(2952699089939798529119576865654542659289/7474898137797769395937500000:ℝ),(765050411435840318432198419818566281472/1946588056718169113525390625:ℝ),(761177030425921788614335828120619798272/5839764170154507340576171875:ℝ)]]
theorem row051_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2973347775101256986774749328596171087/44589504226073223635140608000000000000:ℝ) row051_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row051_coefficients,Fin.sum_univ_succ]
 ring
theorem row051_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row051_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row051_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row051_pos
