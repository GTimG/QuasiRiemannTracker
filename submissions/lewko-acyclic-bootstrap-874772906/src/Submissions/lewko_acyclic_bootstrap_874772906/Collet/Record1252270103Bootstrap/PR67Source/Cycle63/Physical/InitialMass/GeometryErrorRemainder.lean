import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorTail
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorZero
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorSecondSplit
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryTailPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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
local instance errorRemainderDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _

open CenteredMomentSourceRow CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson
open CenteredMomentSecondLocalization
variable [Cycle63.AffineLedger] in
theorem eventual_actual_geometry_error_zero_prime_weight {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs bs lo hi slotlo Amax B U ξ εzero εmass εcount : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hlo : 0<lo)(hhi : 0≤hi)(hslotlo : 0<slotlo)
    (hAmax : 0≤Amax)(hB : 0≤B)(hU : 0≤U)(hξ : 0≤ξ)
    (hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃Czero : ℝ,0<Czero ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card ι≤N → (∀j,s.M j≤Cs) → s.upper≤bs → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta unit Mrow a δ reserve padding t b₁ b₂ : ℝ)(hZ : 1<Z),
      Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      0≤unit → 0≤Mrow → 0≤a →
      Real.logb Z (volume s)≤unit*Cycle63.AffineLedger.totalA beta →
      a≤unit*Cycle63.AffineLedger.amp beta → Real.logb Z (volume s)≤Amax →
      1≤b₁ → 1≤b₂ → Endpoints bs b₁ b₂ s → geometry N bs b₁ b₂≤Z^padding →
      Squarefree seed → seed≠0 → 0<sourceRadius s → sourceRadius s≤Z^B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤Z^a) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
    let l := fun j : rows=>geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key j.val
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^Mrow) Z ξ q)
    let factor := if reflected then 1/geometryDCompensator key else
      2*(geometrySupportConstant N slotlo lo lo)^2*geometryDCompensator key
    ∀υ : (j : rows)→actualAllocations s.pools (C j)→elementPool P→Fin 3→RayCharacter→ Character,
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mrow A hK key weight N bs j.val alloc*
        firstExtractedZeroSum s reflected (l j) R j.val.2.1.val alloc
          (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK key j.val) t Φ
          Z Mrow a δ reserve P (υ j alloc))≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*errorZeroPrimeWeight Z εzero P*
        Z^(δ-frequencyLoss Z 32 ξ)*factor*
        Z^(zeroPaymentExponent Z unit Mrow A a ξ reserve padding εzero εmass B+3*εcount)/(seed.absNorm:ℝ) := by
  have hfamily := actual_geometry_error_zero_family N Cs bs lo hi εzero εmass
    hCs hbs hlo hhi hez hem
  obtain ⟨K₀,hK₀,hfamily⟩ := hfamily
  obtain ⟨C,hC,hpayment⟩ := eventual_actual_geometry_zero_mass_payment (ι:=ι)
    Amax 0 B (((N:ℝ)+2)*U) ξ εcount hAmax (by norm_num) hB (by positivity) hξ hec
    N slotlo lo lo hslotlo hlo hlo
  refine ⟨K₀*C,mul_pos hK₀ hC,?_⟩
  filter_upwards [hpayment] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed W Φ hn hm hs hl p hp₁ hp₂ beta unit Mrow a δ reserve padding t b₁ b₂ hZ hb hunit hM ha0
    hA ha hA' hb₁ hb₂ he hgeo hseed hseed0 hsource hcap hpool P hp hbad hpcap hslot
    reflected key hK A rows Cj l weight factor υ
  have hs₁ : ∀x,s.W₁ x≠0→lo≤x := by
    intro x hx;rw [hp₁] at hx;exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→lo≤x := by
    intro x hx;rw [hp₂] at hx;exact (p.support 1 hx).1
  have hz₁ : s.W₁ 0=0 := by by_contra h;have hh:=hs₁ 0 h;linarith
  have hz₂ : s.W₂ 0=0 := by by_contra h;have hh:=hs₂ 0 h;linarith
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos s)).symm
  have hVcap : volume s≤Z^Amax := by
    rw [hV];exact Real.rpow_le_rpow_of_exponent_le hZ.le hA'
  have hKi : (Z^Mrow)⁻¹≤Z^(0:ℝ) := by
    rw [Real.rpow_zero]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hM)
  have hprojector : ∀r∈rows,(r.2.1.val.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
    intro r hr
    exact actual_geometry_projector_cap s N R seed (Z^Mrow) Z ξ U hK hn hZ.le hU hpool key r
  have hprime (q : elementPool P) : Prime (Ideal.span {q.val}) := by
    exact hp _ (elementPool_data P hp hbad q.val q.property).2.1
  have hzero := hfamily s hn hm hs p hp₁ hp₂ Φ reflected R seed Z beta unit Mrow A a ξ δ reserve
    padding b₁ b₂ hZ hb hunit hA ha ha0 hb₁ hb₂ he hgeo hV.le P hprime hslot key weight rows t υ
  have hmass := hz.2 s R seed W unit Mrow a reserve padding εzero εmass hZ hn hl hez.le hem.le
    hseed hseed0 hz₁ hz₂ hsource hcap hVcap hKi hs₁ hs₂ reflected key rows
    (Finset.Subset.refl _) hprojector
  have hpnonneg : 0≤errorZeroPrimeWeight Z εzero P := by
    unfold errorZeroPrimeWeight
    exact Finset.sum_nonneg (fun q _=>Finset.sum_nonneg
      (fun i _=>Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  apply hzero.trans
  apply (mul_le_mul_of_nonneg_left hmass (by positivity :
    0≤K₀*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*errorZeroPrimeWeight Z εzero P*
      Z^(δ-frequencyLoss Z 32 ξ))).trans_eq
  ring

def jointErrorRetained {First : Type*}[Fintype First]
    (α : First→Type*)[∀f,Fintype (α f)](s : (f : First)→ Input (α f))
    (g : First→FirstBranchGeometry)(w : First→ℝ)(Φ : 𝓢(ℝ,ℂ))(Z sigma ξ reserve : ℝ)
    (P : Finset (Ideal O))(υ : First→elementPool P→Fin 3→RayCharacter→ Character)
    (Fourier : First→elementPool P→Fin 3→ℝ) : ℂ :=
  let Label := (f : First) × (q : elementPool P) × (i : Fin 3) ×
    (_ψ : RayCharacter) × actualAllocations (activeInput (s f)).pools
      ((Ideal.span {q.val})^(errorIndex i+1))
  let E := fun l : Label=>(Ideal.span {l.2.1.val})^(errorIndex l.2.2.1+1)
  let source := fun l : Label=>child (s l.1) (E l) (g l.1).R
    (errorActiveAllocation (s l.1) _ l.2.2.2.2) (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) (s l.1).t
  let radius := fun l : Label=>errorCommonRadius Z (g l.1).d
    (nominalLog (g l.1).I (g l.1).J (g l.1).E (g l.1).K (g l.1).X Z)
    (g l.1).cLog sigma (frequencyLoss Z 32 ξ) reserve l.2.1.val (errorIndex l.2.2.1+1)
  let coeff := fun l : Label=>w l.1*(16*(errorIndex l.2.2.1+2:ℝ)*localErrorCost l.2.1.val (errorIndex l.2.2.1))
  ∑l : Label,((coeff l/volume (source l):ℝ):ℂ)*secondRetainedEnergy (source l).η (source l).t
    (original (source l) ((g l.1).R*E l) (g l.1).seed).columns
    (original (source l) ((g l.1).R*E l) (g l.1).seed).beta
    Φ (radius l) (Fourier l.1 l.2.1 l.2.2.1) Z ξ

lemma actual_joint_error_split_grouped {First : Type*}[Fintype First]
    (α : First→Type*)[∀f,Fintype (α f)](s : (f : First)→ Input (α f))
    (g : First→FirstBranchGeometry)(w : First→ℝ)(hw : ∀f,0≤w f)
    (Z sigma ξ reserve : ℝ)(hZ : 0<Z)(P : Finset (Ideal O))
    (υ : First→elementPool P→Fin 3→RayCharacter→ Character)
    (Fourier : First→elementPool P→Fin 3→ℝ) :
    let radius := fun f (q : elementPool P)(i : Fin 3)=>errorCommonRadius Z (g f).d
      (nominalLog (g f).I (g f).J (g f).E (g f).K (g f).X Z)
      (g f).cLog sigma (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1)
    (∑f : First,w f*actualErrorSources (s f) (g f) Z sigma 1 ξ reserve P (υ f))≤
      (∑f : First,w f*extractedZeroSum (s f) (g f).R (g f).seed ballProfile P (radius f) (υ f))+
      (∑f : First,w f*extractedTailSum (s f) (g f).R (g f).seed ballProfile Z ξ P
        (radius f) (Fourier f) (υ f))+‖jointErrorRetained α s g w ballProfile Z sigma ξ reserve P υ Fourier‖ := by
  intro radius
  have hh := actual_joint_error_second_split α s g w hw Z sigma 1 ξ reserve hZ P υ
    (fun l=>Fourier l.1 l.2.1 l.2.2.1)
  simpa only [extractedZeroSum,extractedTailSum,jointErrorRetained,
    show (32:ℝ)*1=32 by ring,Fintype.sum_sigma,Finset.mul_sum,
    mul_add,Finset.sum_add_distrib,div_eq_mul_inv,mul_assoc] using hh

-- Dependent allocation domains below are definitionally equal after physical label unfolding.
variable [Cycle63.AffineLedger] in
set_option backward.isDefEq.respectTransparency false in
/-- The complete literal error sources are paid except for one exact joint
retained sum. No separate retained-label norm or analytic budget is assumed. -/
theorem eventual_actual_geometry_error_remainder {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi slotlo B U ξ εzero εmass εcount saving : ℝ)
    (hCs : 1≤Cs)(hb : 1≤b)(hlo : 0<lo)(hhi : 0≤hi)(hslotlo : 0<slotlo)
    (hB : 0≤B)(hU : 0≤U)(hξ : 0<ξ)(hez : 0<εzero)(hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input α)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ)),
      Fintype.card α≤N → (∀i,s.M i≤Cs) → s.upper≤b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(beta unit Mrow a reserve padding t b₁ b₂ : ℝ)(hZ : 1<Z),
      Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      0≤unit → 0≤Mrow → Mrow≤B → 0≤a → a≤B → 0≤ reserve →
      frequencyLoss Z 32 ξ+reserve≤B →
      Real.logb Z (volume s)≤unit*Cycle63.AffineLedger.totalA beta →
      a≤unit*Cycle63.AffineLedger.amp beta →
      1≤b₁ → 1≤b₂ → Endpoints b b₁ b₂ s → geometry N b b₁ b₂≤Z^padding →
      Squarefree seed → seed≠0 → 0<sourceRadius s → sourceRadius s≤Z^B →
      |Real.logb Z (volume s)|≤B → (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤Z^a) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^Mrow) Z ξ q)
    let First := (j : rows) × actualAllocations s.pools (C j)
    let first := fun f : First=>child s (C f.1) R f.2
      (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK key f.1.val) t
    let g := fun f : First=>geometryBranch reflected s R seed (Z^Mrow) Z ξ hK key f.1.val
    let w := fun f : First=>geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mrow A hK key weight N b f.1.val f.2
    ∀υ : First→elementPool P→Fin 3→RayCharacter→ Character,
    let Fourier := fun f : First=>fun (q : elementPool P)(i : Fin 3)=>
      firstErrorTailFourier N b (volume s) (C f.1) q.val (errorIndex i+1)
        (firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key f.1.val)
          Z Mrow (volume s) a (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1))
    (∑f : First,w f*actualErrorSources (first f) (g f) Z (3*a) 1 ξ reserve P (υ f))≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier ballProfile 0‖*
        errorZeroPrimeWeight Z εzero P*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(zeroPaymentExponent Z unit Mrow A a ξ reserve padding εzero εmass B+3*εcount)/(seed.absNorm:ℝ)+
      Ctail*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
        Z^(-saving)/(seed.absNorm:ℝ)+
      ‖jointErrorRetained (fun f : First=>liveIndices f.2.val) first g w ballProfile
        Z (3*a) ξ reserve P υ Fourier‖ := by
  have htail := eventual_actual_geometry_error_tail (α:=α)
    N Cs b lo hi slotlo B U B ξ εmass εcount saving hCs hb hlo hhi hslotlo hB hU hB hξ hem hec
  obtain ⟨F,Ct,hCt,htail⟩ := htail
  obtain ⟨Cz,hCz,hzero⟩ := eventual_actual_geometry_error_zero_prime_weight (ι:=α)
    N Cs b lo hi slotlo B B U ξ εzero εmass εcount hCs hb hlo hhi hslotlo hB hB hU hξ.le hez hem hec
  refine ⟨F,Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [htail,hzero] with Z ht hz
  refine ⟨ht.1,?_⟩
  intro s R seed W hn hm hs hl p hp₁ hp₂ beta unit Mrow a reserve padding t b₁ b₂ hZ hb₀ hunit hM hMB ha haB
    hr hω hvol hamp hb₁ hb₂ hend hgeometry hseed hseed0 hsource hcap hA hpool P hp hbad hpcap hslot
    reflected key hK A rows C weight First first g w υ Fourier
  have hzt := hz.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ beta unit Mrow a (frequencyLoss Z 32 ξ)
    reserve padding t b₁ b₂ hZ hb₀ hunit hM ha hvol hamp (abs_le.mp hA).2 hb₁ hb₂ hend hgeometry
    hseed hseed0 hsource hcap hpool P hp hbad hpcap hslot reflected key (fun j alloc=>υ ⟨j,alloc⟩)
  have hpcapB : ∀Q∈P,(Q.absNorm:ℝ)≤Z^B := fun Q hQ=>(hpcap Q hQ).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le haB)
  have htt := ht.2 s R seed W ballProfile hn hm hs hl p hp₁ hp₂ Mrow a reserve t hZ hM hMB ha haB
    hr hω hseed hseed0 hsource hcap hA hpool P hp hbad hpcapB hslot reflected key
    (fun j alloc=>υ ⟨j,alloc⟩)
  have hnonneg : ∀f : First,0≤w f := fun f=>geometryAllocationWeight_nonneg reflected s R seed
    (Z^Mrow) Z ξ Mrow A hK key weight N b f.1.val f.2
  have hh := actual_joint_error_split_grouped (fun f : First=>liveIndices f.2.val) first g w hnonneg
    Z (3*a) ξ reserve (zero_lt_one.trans hZ) P υ Fourier
  let radius := fun f (q : elementPool P)(i : Fin 3)=>errorCommonRadius Z (g f).d
    (nominalLog (g f).I (g f).J (g f).E (g f).K (g f).X Z)
    (g f).cLog (3*a) (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1)
  have hzsum : (∑f : First,w f*extractedZeroSum (first f) (g f).R (g f).seed
      ballProfile P (radius f) (υ f))=
    ∑j : rows,∑alloc : actualAllocations s.pools (C j),w ⟨j,alloc⟩*
      firstExtractedZeroSum s reflected (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key j.val)
        R j.val.2.1.val alloc (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK key j.val) t
        ballProfile Z Mrow a (frequencyLoss Z 32 ξ) reserve P (υ ⟨j,alloc⟩) := by
    dsimp only [First,C,geometryColumnIdeal,geometryFirstLabel]
    simp only [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun alloc _ => ?_
    congr 1
    unfold firstExtractedZeroSum
    have he : radius ⟨j,alloc⟩=fun q i=>firstErrorZeroRadius reflected Z Mrow (volume s) a
        (frequencyLoss Z 32 ξ) reserve (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key j.val)
          q.val (errorIndex i+1) := by
      funext q i
      exact geometry_error_zero_radius s R seed Z Mrow ξ a (frequencyLoss Z 32 ξ) reserve hK
        reflected key j.val q.val (errorIndex i+1)
    rw [he]
    rfl
  have htsum : (∑f : First,w f*extractedTailSum (first f) (g f).R (g f).seed
      ballProfile Z ξ P (radius f) (Fourier f) (υ f))=
    ∑j : rows,∑alloc : actualAllocations s.pools (C j),w ⟨j,alloc⟩*
      firstExtractedTailSum N b s reflected (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key j.val)
        R j.val.2.1.val alloc (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK key j.val) t
        ballProfile Z Mrow a (frequencyLoss Z 32 ξ) reserve ξ P (υ ⟨j,alloc⟩) := by
    dsimp only [First,C,geometryColumnIdeal,geometryFirstLabel]
    simp only [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun alloc _ => ?_
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
