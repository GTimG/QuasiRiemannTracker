import Candidate.Target836.Source836.GlobalNamed
import Candidate.Target836.Source836.ZeroScalar
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorTail
import Candidate.Target836.Source836.GeometryErrorZero
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorSecondSplit
import Candidate.Cycle63.Physical.InitialMass.GeometryTailPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorRemainder
import Candidate.Target836.Source836.GeometryAffineRemainder

/- Original module: Candidate.Target836.Source836.GeometryErrorRemainder. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentSupportedTailAggregate CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements RayFourExpansion ConcretePrimeRowBridge CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O
local instance errorRemainderDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _

open CenteredMomentSourceRow CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson
open CenteredMomentSecondLocalization
theorem eventual_actual_geometry_error_zero_prime_weight {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs bs lo hi slotlo Amax B U ξ εzero εmass εcount : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hlo : 0< lo)(hhi : 0≤ hi)(hslotlo : 0< slotlo)
    (hAmax : 0≤ Amax)(hB : 0≤ B)(hU : 0≤ U)(hξ : 0≤ξ)
    (hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃Czero : ℝ,0< Czero ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤ N → (∀j,s.M j≤ Cs) → s.upper≤ bs → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a δ reserve padding t b₁ b₂ : ℝ)(hZ : 1< Z),
      3401/100000≤ beta ∧ beta≤1/25 → 0≤ M → 0≤ a →
      Real.logb Z (volume s)≤ M*GlobalNamed.totalA beta →
      a≤ M*GlobalNamed.amp beta → Real.logb Z (volume s)≤ Amax →
      1≤ b₁ → 1≤ b₂ → Endpoints bs b₁ b₂ s → geometry N bs b₁ b₂≤ Z^padding →
      Squarefree seed → seed≠0 → 0< sourceRadius s → sourceRadius s≤ Z^B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^a) →
      (∀q : elementPool P,∀i I,I∈s.slots i→IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=> logAnnulus)
    let C := fun j : rows=> geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let l := fun j : rows=> geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val
    let weight := fun q=> normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let factor := if reflected then 1/geometryDCompensator key else
      2*(geometrySupportConstant N slotlo lo lo)^2*geometryDCompensator key
    ∀υ : (j : rows)→actualAllocations s.pools (C j)→elementPool P→Fin 3→RayCharacter→Character,
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val alloc*
        firstExtractedZeroSum s reflected (l j) R j.val.2.1.val alloc
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t Φ
          Z M a δ reserve P (υ j alloc))≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*errorZeroPrimeWeight Z εzero P*
        Z^(δ-frequencyLoss Z 32 ξ)*factor*
        Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/(seed.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hfamily⟩ := actual_geometry_error_zero_family N Cs bs lo hi εzero εmass
    hCs hbs hlo hhi hez hem
  obtain ⟨C,hC,hpayment⟩ := eventual_actual_geometry_zero_mass_payment (ι:=ι)
    Amax 0 B (((N:ℝ)+2)*U) ξ εcount hAmax (by norm_num) hB (by positivity) hξ hec
    N slotlo lo lo hslotlo hlo hlo
  refine ⟨K₀*C,mul_pos hK₀ hC,?_⟩
  filter_upwards [hpayment] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed W Φ hn hm hs hl p hp₁ hp₂ beta M a δ reserve padding t b₁ b₂ hZ hb hM ha0
    hA ha hA' hb₁ hb₂ he hgeo hseed hseed0 hsource hcap hpool P hp hbad hpcap hslot
    reflected key hK A rows Cj l weight factor υ
  have hs₁ : ∀x,s.W₁ x≠0→lo≤ x := by
    intro x hx;rw [hp₁] at hx;exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→lo≤ x := by
    intro x hx;rw [hp₂] at hx;exact (p.support 1 hx).1
  have hz₁ : s.W₁ 0=0 := by by_contra h;have hh:=hs₁ 0 h;linarith
  have hz₂ : s.W₂ 0=0 := by by_contra h;have hh:=hs₂ 0 h;linarith
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos s)).symm
  have hVcap : volume s≤ Z^Amax := by
    rw [hV];exact Real.rpow_le_rpow_of_exponent_le hZ.le hA'
  have hKi : (Z^M)⁻¹≤ Z^(0:ℝ) := by
    rw [Real.rpow_zero]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hM)
  have hprojector : ∀r∈rows,(r.2.1.val.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
    intro r hr
    exact actual_geometry_projector_cap s N R seed (Z^M) Z ξ U hK hn hZ.le hU hpool key r
  have hprime (q : elementPool P) : Prime (Ideal.span {q.val}) := by
    exact hp _ (elementPool_data P hp hbad q.val q.property).2.1
  have hzero := hfamily s hn hm hs p hp₁ hp₂ Φ reflected R seed Z beta M A a ξ δ reserve
    padding b₁ b₂ hZ hb hM hA ha ha0 hb₁ hb₂ he hgeo hV.le P hprime hslot key weight rows t υ
  have hmass := hz.2 s R seed W M a reserve padding εzero εmass hZ hn hl hez.le hem.le
    hseed hseed0 hz₁ hz₂ hsource hcap hVcap hKi hs₁ hs₂ reflected key rows
    (Finset.Subset.refl _) hprojector
  have hpnonneg : 0≤ errorZeroPrimeWeight Z εzero P := by
    unfold errorZeroPrimeWeight
    exact Finset.sum_nonneg (fun q _=> Finset.sum_nonneg
      (fun i _=> Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  apply hzero.trans
  apply (mul_le_mul_of_nonneg_left hmass (by positivity :
    0≤ K₀*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*errorZeroPrimeWeight Z εzero P*
      Z^(δ-frequencyLoss Z 32 ξ))).trans_eq
  ring




def jointErrorRetained {First : Type*}[Fintype First]
    (α : First→Type*)[∀f,Fintype (α f)](s : (f : First)→Input (α f))
    (g : First→FirstBranchGeometry)(w : First→ℝ)(Φ : 𝓢(ℝ,ℂ))(Z sigma ξ reserve : ℝ)
    (P : Finset (Ideal O))(υ : First→elementPool P→Fin 3→RayCharacter→Character)
    (Fourier : First→elementPool P→Fin 3→ℝ) : ℂ :=
  let Label := (f : First) × (q : elementPool P) × (i : Fin 3) ×
    (_ψ : RayCharacter) × actualAllocations (activeInput (s f)).pools
      ((Ideal.span {q.val})^(errorIndex i+1))
  let E := fun l : Label=>(Ideal.span {l.2.1.val})^(errorIndex l.2.2.1+1)
  let source := fun l : Label=> child (s l.1) (E l) (g l.1).R
    (errorActiveAllocation (s l.1) _ l.2.2.2.2) (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) (s l.1).t
  let radius := fun l : Label=> errorCommonRadius Z (g l.1).d
    (nominalLog (g l.1).I (g l.1).J (g l.1).E (g l.1).K (g l.1).X Z)
    (g l.1).cLog sigma (frequencyLoss Z 32 ξ) reserve l.2.1.val (errorIndex l.2.2.1+1)
  let coeff := fun l : Label=> w l.1*(16*(errorIndex l.2.2.1+2:ℝ)*localErrorCost l.2.1.val (errorIndex l.2.2.1))
  ∑l : Label,((coeff l/volume (source l):ℝ):ℂ)*secondRetainedEnergy (source l).η (source l).t
    (original (source l) ((g l.1).R*E l) (g l.1).seed).columns
    (original (source l) ((g l.1).R*E l) (g l.1).seed).beta
    Φ (radius l) (Fourier l.1 l.2.1 l.2.2.1) Z ξ

lemma actual_joint_error_split_grouped {First : Type*}[Fintype First]
    (α : First→Type*)[∀f,Fintype (α f)](s : (f : First)→Input (α f))
    (g : First→FirstBranchGeometry)(w : First→ℝ)(hw : ∀f,0≤ w f)
    (Z sigma ξ reserve : ℝ)(hZ : 0< Z)(P : Finset (Ideal O))
    (υ : First→elementPool P→Fin 3→RayCharacter→Character)
    (Fourier : First→elementPool P→Fin 3→ℝ) :
    let radius := fun f (q : elementPool P)(i : Fin 3)=> errorCommonRadius Z (g f).d
      (nominalLog (g f).I (g f).J (g f).E (g f).K (g f).X Z)
      (g f).cLog sigma (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1)
    (∑f : First,w f*actualErrorSources (s f) (g f) Z sigma 1 ξ reserve P (υ f))≤
      (∑f : First,w f*extractedZeroSum (s f) (g f).R (g f).seed ballProfile P (radius f) (υ f))+
      (∑f : First,w f*extractedTailSum (s f) (g f).R (g f).seed ballProfile Z ξ P
        (radius f) (Fourier f) (υ f))+‖jointErrorRetained α s g w ballProfile Z sigma ξ reserve P υ Fourier‖ := by
  intro radius
  have hh := actual_joint_error_second_split α s g w hw Z sigma 1 ξ reserve hZ P υ
    (fun l=> Fourier l.1 l.2.1 l.2.2.1)
  simpa only [extractedZeroSum,extractedTailSum,jointErrorRetained,
    show (32:ℝ)*1=32 by ring,Fintype.sum_sigma,Finset.mul_sum,
    mul_add,Finset.sum_add_distrib,div_eq_mul_inv,mul_assoc] using hh

-- Dependent allocation domains below are definitionally equal after physical label unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The complete literal error sources are paid except for one exact joint
retained sum. No separate retained-label norm or analytic budget is assumed. -/
theorem eventual_actual_geometry_error_remainder {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi slotlo B U ξ εzero εmass εcount saving : ℝ)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hlo : 0< lo)(hhi : 0≤ hi)(hslotlo : 0< slotlo)
    (hB : 0≤ B)(hU : 0≤ U)(hξ : 0<ξ)(hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Czero Ctail : ℝ,0< Czero ∧ 0< Ctail ∧
    ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input α)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ)),
      Fintype.card α≤ N → (∀i,s.M i≤ Cs) → s.upper≤ b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta M a reserve padding t b₁ b₂ : ℝ)(hZ : 1< Z),
      3401/100000≤ beta ∧ beta≤1/25 → 0≤ M → M≤ B → 0≤ a → a≤ B → 0≤ reserve →
      frequencyLoss Z 32 ξ+reserve≤ B →
      Real.logb Z (volume s)≤ M*GlobalNamed.totalA beta →
      a≤ M*GlobalNamed.amp beta →
      1≤ b₁ → 1≤ b₂ → Endpoints b b₁ b₂ s → geometry N b b₁ b₂≤ Z^padding →
      Squarefree seed → seed≠0 → 0< sourceRadius s → sourceRadius s≤ Z^B →
      |Real.logb Z (volume s)|≤ B → (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^a) →
      (∀q : elementPool P,∀i I,I∈s.slots i→IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=> logAnnulus)
    let C := fun j : rows=> geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let weight := fun q=> normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let First := (j : rows) × actualAllocations s.pools (C j)
    let first := fun f : First=> child s (C f.1) R f.2
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key f.1.val) t
    let g := fun f : First=> geometryBranch reflected s R seed (Z^M) Z ξ hK key f.1.val
    let w := fun f : First=> geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b f.1.val f.2
    ∀υ : First→elementPool P→Fin 3→RayCharacter→Character,
    let Fourier := fun f : First=> fun (q : elementPool P)(i : Fin 3)=>
      firstErrorTailFourier N b (volume s) (C f.1) q.val (errorIndex i+1)
        (firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key f.1.val)
          Z M (volume s) a (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1))
    (∑f : First,w f*actualErrorSources (first f) (g f) Z (3*a) 1 ξ reserve P (υ f))≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier ballProfile 0‖*
        errorZeroPrimeWeight Z εzero P*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/(seed.absNorm:ℝ)+
      Ctail*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(-saving)/(seed.absNorm:ℝ)+
      ‖jointErrorRetained (fun f : First=> liveIndices f.2.val) first g w ballProfile
        Z (3*a) ξ reserve P υ Fourier‖ := by
  obtain ⟨F,Ct,hCt,htail⟩ := eventual_actual_geometry_error_tail (α:=α)
    N Cs b lo hi slotlo B U B ξ εmass εcount saving hCs hb hlo hhi hslotlo hB hU hB hξ hem hec
  obtain ⟨Cz,hCz,hzero⟩ := eventual_actual_geometry_error_zero_prime_weight (ι:=α)
    N Cs b lo hi slotlo B B U ξ εzero εmass εcount hCs hb hlo hhi hslotlo hB hB hU hξ.le hez hem hec
  refine ⟨F,Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [htail,hzero] with Z ht hz
  refine ⟨ht.1,?_⟩
  intro s R seed W hn hm hs hl p hp₁ hp₂ beta M a reserve padding t b₁ b₂ hZ hb₀ hM hMB ha haB
    hr hω hvol hamp hb₁ hb₂ hend hgeometry hseed hseed0 hsource hcap hA hpool P hp hbad hpcap hslot
    reflected key hK A rows C weight First first g w υ Fourier
  have hzt := hz.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ beta M a (frequencyLoss Z 32 ξ)
    reserve padding t b₁ b₂ hZ hb₀ hM ha hvol hamp (abs_le.mp hA).2 hb₁ hb₂ hend hgeometry
    hseed hseed0 hsource hcap hpool P hp hbad hpcap hslot reflected key (fun j alloc=>υ ⟨j,alloc⟩)
  have hpcapB : ∀Q∈P,(Q.absNorm:ℝ)≤ Z^B := fun Q hQ=>(hpcap Q hQ).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le haB)
  have htt := ht.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ M a reserve t hZ hM hMB ha haB
    hr hω hseed hseed0 hsource hcap hA hpool P hp hbad hpcapB hslot reflected key
    (fun j alloc=>υ ⟨j,alloc⟩)
  have hnonneg : ∀f : First,0≤ w f := fun f=> geometryAllocationWeight_nonneg reflected s R seed
    (Z^M) Z ξ M A hK key weight N b f.1.val f.2
  have hh := actual_joint_error_split_grouped (fun f : First=> liveIndices f.2.val) first g w hnonneg
    Z (3*a) ξ reserve (zero_lt_one.trans hZ) P υ Fourier
  let radius := fun f (q : elementPool P)(i : Fin 3)=> errorCommonRadius Z (g f).d
    (nominalLog (g f).I (g f).J (g f).E (g f).K (g f).X Z)
    (g f).cLog (3*a) (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1)
  have hzsum : (∑f : First,w f*extractedZeroSum (first f) (g f).R (g f).seed
      ballProfile P (radius f) (υ f))=
    ∑j : rows,∑alloc : actualAllocations s.pools (C j),w ⟨j,alloc⟩*
      firstExtractedZeroSum s reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
        R j.val.2.1.val alloc (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t
        ballProfile Z M a (frequencyLoss Z 32 ξ) reserve P (υ ⟨j,alloc⟩) := by
    dsimp only [First,C,geometryColumnIdeal,geometryFirstLabel]
    simp only [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro alloc _
    congr 1
    unfold firstExtractedZeroSum
    have he : radius ⟨j,alloc⟩=fun q i=> firstErrorZeroRadius reflected Z M (volume s) a
        (frequencyLoss Z 32 ξ) reserve (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
          q.val (errorIndex i+1) := by
      funext q i
      exact geometry_error_zero_radius s R seed Z M ξ a (frequencyLoss Z 32 ξ) reserve hK
        reflected key j.val q.val (errorIndex i+1)
    rw [he]
    rfl
  have htsum : (∑f : First,w f*extractedTailSum (first f) (g f).R (g f).seed
      ballProfile Z ξ P (radius f) (Fourier f) (υ f))=
    ∑j : rows,∑alloc : actualAllocations s.pools (C j),w ⟨j,alloc⟩*
      firstExtractedTailSum N b s reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
        R j.val.2.1.val alloc (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t
        ballProfile Z M a (frequencyLoss Z 32 ξ) reserve ξ P (υ ⟨j,alloc⟩) := by
    dsimp only [First,C,geometryColumnIdeal,geometryFirstLabel]
    simp only [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro alloc _
    congr 1
  dsimp only at hh
  rw [hzsum,htsum] at hh
  apply hh.trans
  apply add_le_add
  · apply add_le_add
    · simpa only [sub_self,Real.rpow_zero,mul_one,geometryHighFactor,one_div] using hzt
    · exact htt
  · exact le_refl _

end
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.eventual_actual_geometry_error_zero_prime_weight
#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_joint_error_split_grouped
#print axioms OAI.SevenEighths.Target836SourceAssembly.eventual_actual_geometry_error_remainder
end

/- Original module: Candidate.Target836.Source836.GeometryAffineErrorRemainder. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius EisensteinSchwartzPoisson
open CenteredMomentPrimeElements CenteredMomentAmplificationErrorEnergy RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineErrorRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _



/-- All extracted zero and tail terms are paid after the single literal
prime average. The exact retained norm keeps its own 56/P factor. -/
theorem eventual_actual_affine_error_remainder
    (Cs μ : ℝ) (hCs : 1≤ Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,3401/100000≤ beta ∧ beta≤1/25 →
      Real.logb Z (volume s)≤ GlobalNamed.totalA beta →
    ∀P : Finset (Ideal O),P.Nonempty →
      (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^(GlobalNamed.amp beta)) →
      (∀q : elementPool P,∀i I,I∈s.slots i→IsCoprime (Ideal.span {q.val}) I) →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    ∀υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
          elementPool P→Fin 3→RayCharacter→Character,
      (56/(P.card:ℝ))*geometryAffineErrorSourceTotal s Ψ Z (GlobalNamed.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z (GlobalNamed.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_error_remainder (α:=ι)
    (Fintype.card ι) Cs (9/4) (1/4) (9/4) 1 3 3 (μ/64) (μ/128) (μ/128) (μ/128) 1
    hCs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
  let zconst := Cz*‖paperRadialFourier ballProfile 0‖
  let tconst := Ct*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  refine ⟨1+168*zconst+56*tconst,by dsimp [zconst,tconst];positivity,?_⟩
  have hpad := (tendsto_rpow_atTop (show 0<μ/128 by positivity)).eventually
    (eventually_ge_atTop (geometry (Fintype.card ι) (9/4) (9/4) (9/4)))
  filter_upwards [hraw,eventual_geometry_small_frequency μ hμ,hpad] with Z hr hfreq hpad
  intro hZ s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  have ha := (GlobalNamed.amp_pos hb).le
  have haB : GlobalNamed.amp beta≤3 := (GlobalNamed.amp_bounds hb).2.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (GlobalNamed.amp beta) (μ/8) (μ/128) t (9/4) (9/4) hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) (by norm_num) (by norm_num) caps.endpoints hpad squarefree_one one_ne_zero
    caps.sourcePositive caps.sourceCap caps.volumeLog caps.poolCap P hp hbad hpcap hcop reflected key υ
  have hn : (1:ℝ)≤ P.card := by exact_mod_cast hne.card_pos
  have haverageNonneg : 0≤56/(P.card:ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have haverage : 56/(P.card:ℝ)≤56 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
    linarith
  have hzero := Target836ErrorPayment.actual_error_zero_prime_average P Z (μ/128) hne hZ (by positivity) hp hbad
  have hz := geometry_affine_zero_loss Z μ (Real.logb Z (volume s)) beta hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -(1:ℝ)≤-(1/20:ℝ))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hzconst : 0≤ zconst := by dsimp [zconst];positivity
  have htconst : 0≤ tconst := by dsimp [tconst];positivity
  change 56/(P.card:ℝ)*errorZeroPrimeWeight Z (μ/128) P≤168 at hzero
  have hzavg := mul_le_mul hzero hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤168)
  have htavg := mul_le_mul haverage htail (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤56)
  have h₁ := mul_le_mul_of_nonneg_left hzavg
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)
  have h₂ := mul_le_mul_of_nonneg_left htavg
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(1/20:ℝ)) := by positivity
  have hnorm : geometryAffineErrorSourceTotal s Ψ Z (GlobalNamed.amp beta) (μ/64) (μ/8)
      t hZ reflected key P υ≤
      zconst*(p.control {(0,0)})^2*errorZeroPrimeWeight Z (μ/128) P*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (GlobalNamed.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖geometryAffineErrorRetainedSum s Ψ Z (GlobalNamed.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
    convert hh using 1 <;>
      simp only [geometryAffineErrorSourceTotal,geometryAffineErrorRetainedSum,
        geometryLowFirstChild,zconst,tconst,map_one,Nat.cast_one,div_one];
      first | rfl | (ring_nf; rfl)
  have hnorm' := mul_le_mul_of_nonneg_left hnorm haverageNonneg
  nlinarith only [hnorm',h₁,h₂,hrest]

end
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.eventual_actual_affine_error_remainder
end
