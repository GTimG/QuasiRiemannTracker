/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row192_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1435597873361761016223062430021683/11036091703874169847330968750000:ℝ),(16135709712940815982790557781388013/55180458519370849236654843750000:ℝ),(3878436009884468602841861821334827/18393486173123616412218281250000:ℝ),(26745725433505766610563962956817/557378368882533830673281250000:ℝ)],
![(1610067266782680223648298486875147/5518045851937084923665484375000:ℝ),(296645530340122966976594494629851/501640531994280447605953125000:ℝ),(72454334966473386848514382225633/204372068590262404580203125000:ℝ),(32700579717201314232699457337653/613116205770787213740609375000:ℝ)],
![(1209016244790839219208917587725437/3678697234624723282443656250000:ℝ),(1557924152098493717311106521405711/2043720685902624045802031250000:ℝ),(478878837389192773663494240911819/836067553323800746009921875000:ℝ),(211398135702229220961510160086317/1532790514426968034351523437500:ℝ)]]
theorem row192_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (32700579717201314232699457337653/17858303849508582595424256000000000:ℝ) row192_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row192_coefficients,Fin.sum_univ_succ]
 ring
theorem row192_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row192_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row192_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row192_pos
