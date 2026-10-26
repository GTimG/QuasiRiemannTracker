import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalSplit
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondChildCaps
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRetainedAssembly
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ExceptionalReference
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalChildPaid
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocationControl
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSecondEnergySplit
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalFixedQSource
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentSectorLocalization CenteredMomentCommonProfile
open CenteredMomentFiniteProfileExceptional RayFourExpansion CenteredMomentFirstScale
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimePool CenteredMomentPrimeElements
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentFirstPhysicalSource
local instance geometryExceptionalBudgetDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  Classical.decEq _

/-- The saved estimate is for the whole exceptional energy, with its original
seed divisor. Its conductor, Fourier and minimum-scale gates remain arithmetic. -/
def geometryExceptionalSourceEstimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ) (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ)
    (Q : Ideal O) (K Z : ℝ) : Prop :=
  ∀(s : Input ι)(p : Profiles wlo whi),
    (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → (∀i,1≤ s.P i) →
    s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(R0 seed : Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤Z^B →
    ∀(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
    ∀(Tsec ξ Kphys : ℝ),0<Kphys →
    0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Cr*Z^L →
    (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*
      (4*frequencyRadius Tsec Z ξ)≤Z^B →
    ∀r : ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖partEnergy true s.η χ₀ Q m s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R0 seed) W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      Ck*profileFactor Sp s p J Q K*Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*
        ((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)

/-- All finite original-slot restrictions are selected before the source and
scale. The individual profile factors are retained; the maximum degree permits
one later height choice without a cardinality loss in the energy. -/
theorem actual_finite_slot_exceptional_family {Label : Type*} [Fintype Label]
    [DecidableEq Label] (slot : Label→Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0<wlo)(hwhi : 0≤whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤B)(hL : 0≤L)(hCr : 0<Cr) :
    ∃(J : Label→ℕ)(Sp : Label→Finset (ℕ×ℕ))(Ck : Label→ℝ)(Jmax : ℕ),
      (∀a,(0,0)∈Sp a ∧ 0≤Ck a ∧ J a≤Jmax) ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K : Label→ℝ,(∀a,0<K a) ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1<Z ∧ geometryExceptionalSourceEstimate wlo whi (lo a) (hi a) W
          ε δ θ B L Cr (J a) (Sp a) (Ck a) Q (K a) Z := by
  have hex (a : Label) := original_exceptional_energy wlo whi hwlo hwhi
    (lo a) (hi a) W ε δ θ B L Cr hε hδ hθ hB hL hCr
  choose J Sp hSp Ck hCk hb using hex
  refine ⟨J,Sp,Ck,Finset.univ.sup J,?_,?_⟩
  · intro a
    exact ⟨hSp a,hCk a,Finset.le_sup (f:=J) (Finset.mem_univ a)⟩
  · intro Q hQ hQt hQ72
    choose K hK hbound using (fun a=>hb a Q hQ hQt hQ72)
    refine ⟨K,hK,?_⟩
    filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
    intro a
    exact ⟨(hz a).1,(hz a).2⟩

theorem actual_finite_slot_exceptional_uniform {Label : Type*} [Fintype Label]
    [DecidableEq Label] (slot : Label→Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0<wlo)(hwhi : 0≤whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤B)(hL : 0≤L)(hCr : 0<Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤Ck ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1<Z ∧ geometryExceptionalSourceEstimate wlo whi (lo a) (hi a) W
          ε δ θ B L Cr J Sp Ck Q K Z := by
  obtain ⟨J,Sp,Ck,Jmax,hdata,hfamily⟩:=actual_finite_slot_exceptional_family slot
    wlo whi hwlo hwhi lo hi W ε δ θ B L Cr hε hδ hθ hB hL hCr
  let Sp₀:=Finset.univ.biUnion Sp
  let C₀:=1+∑a,Ck a
  have hCsum : 0≤∑a,Ck a := Finset.sum_nonneg (fun a _=>(hdata a).2.1)
  have hC₀ : 0≤C₀ := by dsimp [C₀]; linarith
  refine ⟨Jmax,Sp₀,C₀,hC₀,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hfamily Q hQ hQt hQ72
  let K₀:=1+∑a,K a
  have hKsum : 0≤∑a,K a := Finset.sum_nonneg (fun a _=>(hK a).le)
  have hK₀ : 0<K₀ := by dsimp [K₀]; linarith
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hbound] with Z hz
  intro a
  refine ⟨(hz a).1,?_⟩
  unfold geometryExceptionalSourceEstimate
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hh:=(hz a).2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hCa : Ck a≤C₀ := by
    have h:=Finset.single_le_sum (fun a _=>(hdata a).2.1) (Finset.mem_univ a)
    dsimp [C₀]; linarith
  have hKa : K a≤K₀ := by
    have h:=Finset.single_le_sum (fun a _=>(hK a).le) (Finset.mem_univ a)
    dsimp [K₀]; linarith
  have hfactor:=CenteredMomentSecondUniformSubsetSource.factor_mono
    (Finset.subset_biUnion_of_mem Sp (Finset.mem_univ a)) s p (hdata a).2.2 Q (hK a).le hKa
  apply hh.trans
  have hp:=profileFactor_nonneg (Sp a) s p (J a) Q (K a) (hK a).le
  have hzpos:=zero_lt_one.trans (hz a).1
  have hV:=(CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le
  gcongr
  exact Real.rpow_nonneg (mul_nonneg (mul_nonneg
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)) hwlo.le) hwlo.le) _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_child_exceptional_profile_payment {wlo whi : ℝ}
    (Sp : Finset (ℕ×ℕ))(p : Profiles wlo whi)(J : ℕ)(Qfix : Ideal O)(K : ℝ)(hK : 0≤K)
    (N : ℕ)(b : ℝ)(hb : 1≤b)(s : Input ι)(hu : s.upper≤b)(hc : Fintype.card ι≤N)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ) :
    (frozenControl B.val s.M)^2*profileFactor Sp (child s C R B τ t) p J Qfix K≤
      CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix K*
      p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6 := by
  have hh:=CenteredMomentFirstChildProfileControl.exceptional_factor_bound Sp p J Qfix K hK
    (child s C R B τ t) N b (CenteredMomentFirstChildProfileControl.mass s) hb hu
    ((live_card_le B.val).trans hc)
    (CenteredMomentFirstChildProfileControl.child_mass s C R B τ t)
  have hp:=mul_le_mul_of_nonneg_left hh (sq_nonneg (frozenControl B.val s.M))
  have hm:=CenteredMomentFirstPhysicalSource.frozen_child_control s C R B τ t
  apply hp.trans_eq
  dsimp only [CenteredMomentFirstChildProfileControl.mass]
  calc
    _=CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix K*
      p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^4*
        ((frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2) := by simp only [child_height]; ring
    _=_ := by rw [hm]; ring

omit [DecidableEq ι] in
theorem actual_twice_exceptional_profile_payment {wlo whi : ℝ}
    (Sp : Finset (ℕ×ℕ))(p : Profiles wlo whi)(J : ℕ)(Qfix : Ideal O)(K : ℝ)(hK : 0≤K)
    (N : ℕ)(b : ℝ)(hb : 1≤b)(s : Input ι)(hu : s.upper≤b)(hc : Fintype.card ι≤N)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
    (Q : Ideal O)(k : ℕ)(Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character)(v : ℝ) :
    (frozenControl B.val s.M)^2*(frozenControl Bp.val (child s C R B τ t).M)^2*
      profileFactor Sp (twiceChild s C R B τ t Q k Bp υ v) p J Qfix K≤
      CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix K*
      p.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6 := by
  have hh:=CenteredMomentFirstChildProfileControl.twice_exceptional_factor Sp p J Qfix K hK
    N b hb s hu hc C R B τ t Q k Bp υ v
  have hp:=mul_le_mul_of_nonneg_left hh
    (mul_nonneg (sq_nonneg (frozenControl B.val s.M))
      (sq_nonneg (frozenControl Bp.val (child s C R B τ t).M)))
  have hm:=CenteredMomentFirstPhysicalSource.frozen_child_control s C R B τ t
  have hm₂:=CenteredMomentFirstPhysicalSource.frozen_child_control
    (child s C R B τ t) (Q^k) (R*C) Bp υ v
  apply hp.trans_eq
  dsimp only [CenteredMomentFirstChildProfileControl.mass]
  calc
    _=CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix K*
      p.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^4*
      (frozenControl B.val s.M)^2*
      ((frozenControl Bp.val (child s C R B τ t).M)^2*
        (∏i,(child (child s C R B τ t) (Q^k) (R*C) Bp υ v).M i)^2) := by simp only [twiceChild]; ring
    _=CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix K*
      p.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^4*
      ((frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2) := by rw [hm₂]; ring
    _=_ := by rw [hm]; ring

omit [DecidableEq ι] in
/-- The saved estimate uses the exact minimum of the four plain scales. -/
theorem actual_child_exceptional_reference_range (s : Input ι)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t Z L loss : ℝ)
    (hZ : 1<Z)(hX₁ : Z^(L-loss)≤ s.X₁)(hX₂ : Z^(L-loss)≤ s.X₂)
    (hY₁ : Z^(L-loss)≤ s.Y₁)(hY₂ : Z^(L-loss)≤ s.Y₂) :
    L-Real.logb Z (C.absNorm:ℝ)-loss≤ inputCap Z (child s C R B τ t) := by
  have hl:=child_lower s C R (allocation_ne s C B) B τ t Z (L-loss) hZ hX₁ hX₂ hY₁ hY₂
  have hh:=input_cap_lower Z _ hZ (child s C R B τ t) hl.1 hl.2.1 hl.2.2.1 hl.2.2.2
  linarith

omit [DecidableEq ι] in
theorem actual_twice_exceptional_reference_range (s : Input ι)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
    (Q : Ideal O)(hQ : Q≠0)(k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k))(υ : Character)(v Z L loss : ℝ)
    (hZ : 1<Z)(hX₁ : Z^(L-loss)≤ s.X₁)(hX₂ : Z^(L-loss)≤ s.X₂)
    (hY₁ : Z^(L-loss)≤ s.Y₁)(hY₂ : Z^(L-loss)≤ s.Y₂) :
    L-Real.logb Z (C.absNorm:ℝ)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)-loss≤
      inputCap Z (twiceChild s C R B τ t Q k Bp υ v) := by
  have hl:=twice_lower s C R (allocation_ne s C B) B τ t Q hQ k Bp υ v Z (L-loss)
    hZ hX₁ hX₂ hY₁ hY₂
  have hh:=input_cap_lower Z _ hZ (twiceChild s C R B τ t Q k Bp υ v)
    hl.1 hl.2.1 hl.2.2.1 hl.2.2.2
  linarith

def geometryExceptionalMainReference (τ : Character)(I J E : Ideal O)
    (K X Z sigma delta reserve r : ℝ) : ℝ :=
  ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^(1/3:ℝ)*
    (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z)
      (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^(5/6:ℝ)*Z^(-sigma/3)/
    ((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)))*
    Z^(-2*max r 0/3)

def geometryExceptionalErrorReference (τ : Character)(I J E : Ideal O)
    (K X Z sigma delta reserve r : ℝ)(p : O)(k : ℕ) : ℝ :=
  ((X/(I.absNorm:ℝ))*localErrorCost p (k-1)*
    (X/(I.absNorm:ℝ)/(normValue p)^k)^(1/3:ℝ)*
    (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z)
      (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p k)^(5/6:ℝ)/
    ((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)))*
    Z^(-2*max r 0/3)

omit [DecidableEq ι] in
theorem actual_main_child_exceptional_reference (η τ : Character)
    (I J E : Ideal O)(hI : Supported I)(hJ : Supported J)
    (hIJ : primeSupport I=primeSupport J)(A : Finset (CommonIndex I J))
    (hE : E=Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J=>P.val) A})
    (s : Input ι)(R : Ideal O)(B : actualAllocations s.pools I)
    (K Z sigma delta reserve t plainLoss : ℝ)(hK : 0<K)(hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J=>P.val) A*activeConductor I J})
    (hX₁ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂) :
    geometryExceptionalMainReference τ I J E K (volume s.toData) Z sigma delta reserve
      (inputCap Z (child s I R B τ t))≤
      Z^(Real.logb Z (volume s.toData)-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        4*sigma/3+5*(delta+reserve)/6+2*plainLoss/3) := by
  exact Cycle63ExceptionalReference.actual_main_side_exceptional_reference η τ I J E hI hJ hIJ
    A hE K (volume s.toData) Z 0 sigma delta reserve _ plainLoss hZ hmod hK
    (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData)
    (actual_child_exceptional_reference_range s I R B τ t Z _ plainLoss hZ hX₁ hX₂ hY₁ hY₂)

omit [DecidableEq ι] in
theorem actual_error_twice_exceptional_reference (η τ : Character)
    (I J E : Ideal O)(hI : Supported I)(hJ : Supported J)
    (hIJ : primeSupport I=primeSupport J)(A : Finset (CommonIndex I J))
    (hE : E=Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J=>P.val) A})
    (s : Input ι)(R : Ideal O)(B : actualAllocations s.pools I)
    (K Z sigma delta reserve t plainLoss : ℝ)(hK : 0<K)(hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J=>P.val) A*activeConductor I J})
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad)(p : O)
    (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ)(hk : k=1 ∨ k=6 ∨ k=7)
    (Bp : actualAllocations (child s I R B τ t).pools ((Ideal.span {p})^k))
    (υ : Character)(v : ℝ)
    (hX₁ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂) :
    geometryExceptionalErrorReference τ I J E K (volume s.toData) Z sigma delta reserve
      (inputCap Z (twiceChild s I R B τ t (Ideal.span {p}) k Bp υ v)) p k≤
      Z^(Real.logb Z (volume s.toData)-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        3*sigma/2+5*(delta+reserve)/6+2*plainLoss/3) := by
  have hpdata:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p hp
  have hQ : Ideal.span {p}≠(0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hpdata.1.ne_zero
  have hr:=actual_twice_exceptional_reference_range s I R B τ t (Ideal.span {p}) hQ k Bp υ v
    Z ((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4) plainLoss hZ hX₁ hX₂ hY₁ hY₂
  exact Cycle63ExceptionalReference.actual_error_side_exceptional_reference η τ I J E hI hJ hIJ
    A hE K (volume s.toData) Z 0 sigma delta reserve _ plainLoss hZ hmod M H Sbad hbad p hp
    k hk hK (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData) hr

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
