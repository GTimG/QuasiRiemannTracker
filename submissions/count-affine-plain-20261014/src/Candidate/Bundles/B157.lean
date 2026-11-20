/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B088
import Candidate.Bundles.B090
import Candidate.Bundles.B117
import Candidate.Bundles.B123
import Candidate.Bundles.B134
import Candidate.Bundles.B135
import Candidate.Bundles.B137
import Candidate.Bundles.B145
import Candidate.Bundles.B146
import Candidate.Bundles.B149
import Candidate.Bundles.B156
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalChildPaid
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocationControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePresentation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalBudget; sha256 22a33d77cb3b81e47ef4dc8a2df0cc08ab04253490b39dbecd01cc470958a6b9 -/
section
                                                            
                                                    
                                            
                                                                        
                                                                    
                                                                    
                                                                   
                                                                               

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
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
local notation "O" => HeckeFamily.O
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
    ∀(R0 seed : Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤ Z^B →
    ∀(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
    ∀(Tsec ξ Kphys : ℝ),0< Kphys →
    0< frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤ Cr*Z^L →
    (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*
      (4*frequencyRadius Tsec Z ξ)≤ Z^B →
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
    [DecidableEq Label] (slot : Label→ Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0< wlo)(hwhi : 0≤ whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤ B)(hL : 0≤ L)(hCr : 0< Cr) :
    ∃(J : Label→ℕ)(Sp : Label→ Finset (ℕ×ℕ))(Ck : Label→ℝ)(Jmax : ℕ),
      (∀a,(0,0)∈Sp a ∧ 0≤ Ck a ∧ J a≤ Jmax) ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K : Label→ℝ,(∀a,0< K a) ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1< Z ∧ geometryExceptionalSourceEstimate wlo whi (lo a) (hi a) W
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
    [DecidableEq Label] (slot : Label→ Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0< wlo)(hwhi : 0≤ whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤ B)(hL : 0≤ L)(hCr : 0< Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤ Ck ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1< Z ∧ geometryExceptionalSourceEstimate wlo whi (lo a) (hi a) W
          ε δ θ B L Cr J Sp Ck Q K Z := by
  obtain ⟨J,Sp,Ck,Jmax,hdata,hfamily⟩:=actual_finite_slot_exceptional_family slot
    wlo whi hwlo hwhi lo hi W ε δ θ B L Cr hε hδ hθ hB hL hCr
  let Sp₀:=Finset.univ.biUnion Sp
  let C₀:=1+∑a,Ck a
  have hCsum : 0≤∑a,Ck a := Finset.sum_nonneg (fun a _=>(hdata a).2.1)
  have hC₀ : 0≤ C₀ := by dsimp [C₀]; linarith
  refine ⟨Jmax,Sp₀,C₀,hC₀,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hfamily Q hQ hQt hQ72
  let K₀:=1+∑a,K a
  have hKsum : 0≤∑a,K a := Finset.sum_nonneg (fun a _=>(hK a).le)
  have hK₀ : 0< K₀ := by dsimp [K₀]; linarith
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hbound] with Z hz
  intro a
  refine ⟨(hz a).1,?_⟩
  unfold geometryExceptionalSourceEstimate
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hh:=(hz a).2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hCa : Ck a≤ C₀ := by
    have h:=Finset.single_le_sum (fun a _=>(hdata a).2.1) (Finset.mem_univ a)
    dsimp [C₀]; linarith
  have hKa : K a≤ K₀ := by
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
    (Sp : Finset (ℕ×ℕ))(p : Profiles wlo whi)(J : ℕ)(Qfix : Ideal O)(K : ℝ)(hK : 0≤ K)
    (N : ℕ)(b : ℝ)(hb : 1≤ b)(s : Input ι)(hu : s.upper≤ b)(hc : Fintype.card ι≤ N)
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
    (Sp : Finset (ℕ×ℕ))(p : Profiles wlo whi)(J : ℕ)(Qfix : Ideal O)(K : ℝ)(hK : 0≤ K)
    (N : ℕ)(b : ℝ)(hb : 1≤ b)(s : Input ι)(hu : s.upper≤ b)(hc : Fintype.card ι≤ N)
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
theorem actual_child_exceptional_support_gates
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t Z r : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)(hZ : 1< Z)
    (hX₁ : Z^r≤ s.X₁)(hX₂ : Z^r≤ s.X₂)(hY₁ : Z^r≤ s.Y₁)(hY₂ : Z^r≤ s.Y₂) :
    let src:=child s C R B τ t
    volume src.toData≤ b^N*volume s.toData/(C.absNorm:ℝ) ∧
    sourceRadius src≤ geometry N b bs bs*volume s.toData/(C.absNorm:ℝ) ∧
    r-Real.logb Z (C.absNorm:ℝ)≤ inputCap Z src := by
  intro src
  have hl:=child_lower s C R (allocation_ne s C B) B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  refine ⟨?_,?_,input_cap_lower Z _ hZ src hl.1 hl.2.1 hl.2.2.1 hl.2.2.2⟩
  · exact common_volume_le N b hb s hcard he.1 C R B τ t hne
  · exact actual_common_child_source_cap N b bs hb hbs s hcard he C R B τ t hne

omit [DecidableEq ι] in
theorem actual_twice_exceptional_support_gates
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O)(hQ : Q≠0)(k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k))(υ : Character)(v Z r : ℝ)
    (hZ : 1< Z)(hX₁ : Z^r≤ s.X₁)(hX₂ : Z^r≤ s.X₂)
    (hY₁ : Z^r≤ s.Y₁)(hY₂ : Z^r≤ s.Y₂) :
    let src:=twiceChild s C R B τ t Q k Bp υ v
    volume src.toData≤ geometry N b bs bs*volume s.toData/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k) ∧
    sourceRadius src≤ geometry N b bs bs*volume s.toData/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k) ∧
    r-Real.logb Z (C.absNorm:ℝ)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)≤ inputCap Z src := by
  intro src
  have hc:=twice_caps N b bs bs hb hbs hbs s hcard he C R B τ t hne Q hQ k hslot Bp υ v
  have hl:=twice_lower s C R (allocation_ne s C B) B τ t Q hQ k Bp υ v Z r hZ
    hX₁ hX₂ hY₁ hY₂
  refine ⟨?_,?_,input_cap_lower Z _ hZ src hl.1 hl.2.1 hl.2.2.1 hl.2.2.2⟩
  · simpa only [CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume,mul_div_assoc] using hc.2.2.1
  · simpa only [CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume,mul_div_assoc] using hc.2.2.2

omit [DecidableEq ι] in
theorem actual_child_exceptional_conductor_cap
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t F : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)(hF : 0≤ F) :
    (expandedFactor τ:ℝ)*(R*C).absNorm*(sourceRadius (child s C R B τ t))^2*(4*F)≤
      (expandedFactor τ:ℝ)*R.absNorm*(geometry N b bs bs*volume s.toData)^2*(4*F)/C.absNorm := by
  have hc : 0<(C.absNorm:ℝ) := norm_pos C (allocation_ne s C B)
  have hr := actual_common_child_source_cap N b bs hb hbs s hcard he C R B τ t hne
  have hnon : 0≤ sourceRadius (child s C R B τ t) :=
    (radius_bound N b bs bs hb hbs hbs (child s C R B τ t)
      ((live_card_le B.val).trans hcard) (endpoints_child b bs bs s he C R B τ t)).1
  have hs := pow_le_pow_left₀ hnon hr 2
  rw [map_mul,Nat.cast_mul]
  calc
    _≤(expandedFactor τ:ℝ)*(R.absNorm*C.absNorm)*
      (geometry N b bs bs*volume s.toData/(C.absNorm:ℝ))^2*(4*F) := by
        gcongr
        exact hr
    _=_ := by field_simp

omit [DecidableEq ι] in
/-- The saved estimate uses the exact minimum of the four plain scales. -/
theorem actual_child_exceptional_reference_range (s : Input ι)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t Z L loss : ℝ)
    (hZ : 1< Z)(hX₁ : Z^(L-loss)≤ s.X₁)(hX₂ : Z^(L-loss)≤ s.X₂)
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
    (hZ : 1< Z)(hX₁ : Z^(L-loss)≤ s.X₁)(hX₂ : Z^(L-loss)≤ s.X₂)
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
    (K Z sigma delta reserve t plainLoss : ℝ)(hK : 0< K)(hZ : 1< Z)
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
  exact Cycle61ExceptionalReference.actual_main_side_exceptional_reference η τ I J E hI hJ hIJ
    A hE K (volume s.toData) Z 0 sigma delta reserve _ plainLoss hZ hmod hK
    (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData)
    (actual_child_exceptional_reference_range s I R B τ t Z _ plainLoss hZ hX₁ hX₂ hY₁ hY₂)

omit [DecidableEq ι] in
theorem actual_error_twice_exceptional_reference (η τ : Character)
    (I J E : Ideal O)(hI : Supported I)(hJ : Supported J)
    (hIJ : primeSupport I=primeSupport J)(A : Finset (CommonIndex I J))
    (hE : E=Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J=>P.val) A})
    (s : Input ι)(R : Ideal O)(B : actualAllocations s.pools I)
    (K Z sigma delta reserve t plainLoss : ℝ)(hK : 0< K)(hZ : 1< Z)
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
  exact Cycle61ExceptionalReference.actual_error_side_exceptional_reference η τ I J E hI hJ hIJ
    A hE K (volume s.toData) Z 0 sigma delta reserve _ plainLoss hZ hmod M H Sbad hbad p hp
    k hk hK (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData) hr

theorem geometry_exceptional_strict_exponent (A M sigma delta reserve plainLoss analyticLoss gap margin : ℝ)
    (hbudget : 3*sigma/2+5*(delta+reserve)/6+2*plainLoss/3+analyticLoss≤ gap-margin)
    (hsigma : 0≤ sigma) :
    A-M+4*sigma/3+5*(delta+reserve)/6+2*plainLoss/3+analyticLoss≤ A-M+gap-margin ∧
    A-M+3*sigma/2+5*(delta+reserve)/6+2*plainLoss/3+analyticLoss≤ A-M+gap-margin := by
  constructor <;> linarith

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_finite_slot_exceptional_family
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_exceptional_support_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_twice_exceptional_support_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_exceptional_conductor_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_exceptional_reference_range
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_twice_exceptional_reference_range
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_child_exceptional_reference
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_twice_exceptional_reference
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_exceptional_strict_exponent

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_finite_slot_exceptional_uniform
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_exceptional_profile_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_twice_exceptional_profile_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalAdmission; sha256 e5c039898855bdeb4abb66d8a2c010b9e16bf5fe3e710f784ad6439189d8d1ee -/
section
                                                             
                                                      
                                                      
                                                          
                                                     
                                                                   
                                                                      

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondExceptionalSourceCaps CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyInputParentCapacity Cycle61InitialSource
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile
open CenteredMomentFirstScale CenteredMomentFirstChildLower
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstExceptionalChildPaid CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstAnnularInput CenteredMomentPrimePool CenteredMomentPrimeElements
open PNT.AnnularPrimeMass
local notation "O" => HeckeFamily.O
local instance geometryExceptionalAdmissionDecidable {α : Type*} : DecidableEq α := Classical.decEq _

section Affine
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance geometryExceptionalAdmissionFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z bΦ a b : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0 < a)
variable (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂

/-- The comparison rectangle preserves the product, so its second side is
also above the original quarter-width scale. -/
theorem affine_exceptional_plain_minimum (hZ : 1 < Z) (hM : 0 < M)
    (hlo₁ : (41/100)*M ≤ length Z X₁) (hlo₂ : (41/100)*M ≤ length Z X₂) :
    Z^(M/4) ≤ (inp).X₁ ∧ Z^(M/4) ≤ (inp).X₂ ∧
    Z^(M/4) ≤ (inp).Y₁ ∧ Z^(M/4) ≤ (inp).Y₂ := by
  have hz := zero_lt_one.trans hZ
  have hx₁ : Z^((41/100)*M) ≤ X₁ :=
    (by
      conv_rhs => rw [initial_scale_exact Z X₁ M hZ hM hlo₁]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le hlo₁)
  have hx₂ : Z^((41/100)*M) ≤ X₂ :=
    (by
      conv_rhs => rw [initial_scale_exact Z X₂ M hZ hM hlo₂]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le hlo₂)
  have hp : Z^(M/2) ≤ X₁*X₂ := by
    calc
      _ ≤ Z^((41/100)*M+(41/100)*M) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = Z^((41/100)*M)*Z^((41/100)*M) := Real.rpow_add hz _ _
      _ ≤ _ := mul_le_mul hx₁ hx₂ (Real.rpow_nonneg hz.le _) hX₁.le
  refine ⟨?_, ?_, le_rfl, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hx₁
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hx₂
  · change Z^(M/4) ≤ X₁*X₂/Z^(M/4)
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr
    rw [←Real.rpow_add hz]
    convert hp using 1
    congr 1
    ring
end Affine

theorem eventual_fixed_character_plain_loss (η : Character) (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      (1+Real.logb Z (η.modulus.absNorm:ℝ))/4-loss ≤ (1/4:ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (show 0 < 4*loss by positivity)).eventually
    (eventually_ge_atTop (η.modulus.absNorm:ℝ)), eventually_gt_atTop (1:ℝ)] with Z hη hZ
  refine ⟨hZ, ?_⟩
  have hn : 0 < (η.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hh := (Real.logb_le_iff_le_rpow hZ hn).mpr hη
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_geometry_exceptional_character_cap
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0< K)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^A) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    ((geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus.absNorm:ℝ) ≤
      fixedPresentationCost*(s.η.modulus.absNorm:ℝ)*(Z^A)^2 := by
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  have hc : (src.C.absNorm:ℝ) ≤ Z^A :=
    (actual_geometry_norm_caps s R seed K Z ξ A hs hz₁ hz₂ hsource j.1.val 0).2
  have hf := fixed_pair_caps s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹ F
  have hr : ((geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus.absNorm:ℝ) ≤
      fixedPresentationCost*(s.η.modulus.absNorm:ℝ)*(src.C.absNorm:ℝ)^2 := by
    cases reflected
    · exact hf.1
    · exact hf.2
  apply hr.trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2)
    (mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _))

/-- The polynomial exponents are fixed; only the threshold uses the
original number of slots, support endpoints and original character. -/
theorem eventual_actual_geometry_main_exceptional_admission
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K ξ sigma reserve t : ℝ)
      (hK : 0< K), s.η=η → Fintype.card ι≤ N → Endpoints b bs bs s →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → volume s≤ Z^(2:ℝ) → sourceRadius s≤ Z^(3:ℝ) →
      (R.absNorm:ℝ)≤ Z → K≤ Z → 0≤ξ → ξ≤1 → 0≤ sigma → 0≤ reserve →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin),
      frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R s.ν s.W s.P≠0 →
      let u := geometryLowFirstChild reflected s R seed K Z ξ hK bin t q
      let F := frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin q.1.val)) Z ξ
      0< F ∧ F≤ Z^(8:ℝ) ∧ sourceRadius u≤ Z^(41:ℝ) ∧
      (expandedFactor u.η:ℝ)*(R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm*
        (sourceRadius u)^2*(4*F)≤ Z^(41:ℝ) := by
  filter_upwards [eventually_source_caps,
    eventually_ge_atTop (geometry N b bs bs),
    eventually_ge_atTop (η.modulus.absNorm:ℝ),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop (b^(2*N))]
    with Z he hgeom hη hcost hbN
  refine ⟨he.1, ?_⟩
  intro reflected s R seed K ξ sigma reserve t hK hsame hn hend hs hz₁ hz₂ hV hrad hR
    hKZ hξ hξ₁ hsigma hreserve bin q hne u F
  have hz := zero_lt_one.trans he.1
  have hc (i : Fin 5) := (actual_geometry_norm_caps s R seed K Z ξ 3 hs hz₁ hz₂ hrad q.1.val.1.val i).2
  have hI : ((geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)≤ Z^(3:ℝ) := by
    cases reflected
    · exact hc 0
    · exact hc 1
  have hχ := actual_geometry_exceptional_character_cap reflected s R seed K Z ξ 3 hK
    hs hz₁ hz₂ hrad bin q.1.val
  have hχ₈ : (u.η.modulus.absNorm:ℝ)≤ Z^(8:ℝ) := by
    change ((geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val).modulus.absNorm:ℝ)≤ _
    apply hχ.trans
    rw [hsame]
    calc
      _≤ Z*Z*(Z^(3:ℝ))^2 := by gcongr
      _=Z^(8:ℝ) := by
        rw [show (Z^(3:ℝ))^2=Z^(3:ℝ)*Z^(3:ℝ) by ring]
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        conv_lhs => arg 1; arg 2; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hI₈ : ((R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)≤ Z^(8:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _≤ Z*Z^(3:ℝ) := mul_le_mul hR hI (Nat.cast_nonneg _) hz.le
      _=Z^(4:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]
        norm_num
      _≤ _ := Real.rpow_le_rpow_of_exponent_le he.1.le (by norm_num)
  have hu₃ : sourceRadius u≤ Z^(3:ℝ) := by
    have hh := actual_common_child_source_cap N b bs hb hbs s hn hend
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R q.2
      (geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val) t hne
    have hnI := norm_ge_one _ (allocation_ne s _ q.2)
    calc
      _≤ geometry N b bs bs*volume s := hh.trans (div_le_self
        (mul_nonneg ((geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)) (volume_pos s).le) hnI)
      _≤ Z*Z^(2:ℝ) := mul_le_mul hgeom hV (volume_pos s).le hz.le
      _=Z^(3:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]; norm_num
  have hu₀ : 0≤ sourceRadius u := by
    exact (radius_bound N b bs bs hb hbs hbs u ((live_card_le q.2.val).trans hn)
      (endpoints_child b bs bs s hend _ R q.2 _ t)).1
  have hFpos : 0< F := by
    let hl := geometryFirstLabel s R seed K Z ξ hK bin q.1.val
    have hr := first_main_radius_pos reflected K (volume s) Z ξ sigma reserve hz hl
    change 0 < (b^N*volume s/((if reflected then hl.1.2 else hl.1.1).absNorm:ℝ))^2 /
      firstMainRadius reflected K (volume s) Z ξ sigma reserve hl * Z^(ξ/2)
    have hn : 0 < ((if reflected then hl.1.2 else hl.1.1).absNorm:ℝ) := by
      cases reflected
      · exact norm_pos _ (geometryFirstSource s R seed K Z ξ hK bin q.1.val.1).hC.1
      · exact norm_pos _ (geometryFirstSource s R seed K Z ξ hK bin q.1.val.1).hD.1
    have hbpos := zero_lt_one.trans_le hb
    have hv := volume_pos s
    positivity
  have hF₈ : F≤ Z^(8:ℝ) := by
    have hf := actual_geometry_main_cutoff_cap reflected s R seed K Z ξ sigma reserve b 1 N
      hK he.1 (zero_lt_one.trans_le hb) hξ hsigma hreserve
      (by simpa using hKZ) bin q.1.val
    apply hf.trans
    calc
      _≤ Z*Z^(1+ξ/2) := mul_le_mul_of_nonneg_right hbN (Real.rpow_nonneg hz.le _)
      _=Z^(1+(1+ξ/2)) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]
      _≤ _ := Real.rpow_le_rpow_of_exponent_le he.1.le (by linarith)
  have hu₈ := hu₃.trans (Real.rpow_le_rpow_of_exponent_le he.1.le (show (3:ℝ)≤8 by norm_num))
  have hh := he.2 u.η (R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val)
    (sourceRadius u) F 8 (by norm_num) hu₀ hFpos.le hχ₈ hI₈ hu₈ hF₈
  have hnum : (5*(8:ℝ)+1)=(41:ℝ) := by norm_num
  rw [hnum] at hh
  exact ⟨hFpos,hF₈,hh.1,hh.2⟩

omit [DecidableEq ι] in
/-- This is the minimum gate for the literal retained main source, with
its actual selected ideal and fixed original character. -/
theorem eventual_actual_geometry_main_exceptional_minimum
    (η : Character) (loss : ℝ) (hloss : 0< loss) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K ξ t : ℝ) (hK : 0< K),
      s.η=η → K≤ Z → Z^(1/4:ℝ)≤ s.X₁ → Z^(1/4:ℝ)≤ s.X₂ →
      Z^(1/4:ℝ)≤ s.Y₁ → Z^(1/4:ℝ)≤ s.Y₂ →
      ∀ (bin : ℤ×(Fin 5→ℤ)) (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin),
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
        Real.logb Z ((geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)-loss ≤
      inputCap Z (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q) := by
  filter_upwards [eventual_fixed_character_plain_loss η loss hloss] with Z hh
  refine ⟨hh.1, ?_⟩
  intro reflected s R seed K ξ t hK hη hKZ hx₁ hx₂ hy₁ hy₂ bin q
  have hk : Real.logb Z K≤1 := by
    have hp : K≤ Z^(1:ℝ) := by simpa using hKZ
    exact (Real.logb_le_iff_le_rpow hh.1 hK).mpr hp
  have hL : (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-loss≤1/4 := by
    rw [hη]
    linarith [hh.2]
  have hp := Real.rpow_le_rpow_of_exponent_le hh.1.le hL
  exact actual_child_exceptional_reference_range s _ R q.2 _ t Z _ loss hh.1
    (hp.trans hx₁) (hp.trans hx₂) (hp.trans hy₁) (hp.trans hy₂)

omit [DecidableEq ι] in
/-- Prime extraction subtracts exactly its retained power from the plain
minimum; the source remains the full padded twice-child dictionary. -/
theorem actual_geometry_error_exceptional_minimum
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Z M ξ t : ℝ) (hZ : 1< Z)
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (hp : p≠0) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v L loss : ℝ)
    (hL : L-loss≤1/4)
    (hx₁ : Z^(1/4:ℝ)≤ s.X₁) (hx₂ : Z^(1/4:ℝ)≤ s.X₂)
    (hy₁ : Z^(1/4:ℝ)≤ s.Y₁) (hy₂ : Z^(1/4:ℝ)≤ s.Y₂) :
    L-Real.logb Z ((geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val).absNorm:ℝ)-
      ((errorIndex i+1:ℕ):ℝ)*Real.logb Z ((Ideal.span {p}).absNorm:ℝ)-loss ≤
    inputCap Z (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v) := by
  have hh := Real.rpow_le_rpow_of_exponent_le hZ.le hL
  exact actual_twice_exceptional_reference_range s _ R q.2 _ t (Ideal.span {p})
    (Ideal.span_singleton_eq_bot.not.mpr hp) _ (errorActiveAllocation _ _ Bp) υ v Z L loss hZ
    (hh.trans hx₁) (hh.trans hx₂) (hh.trans hy₁) (hh.trans hy₂)

/-- Literal error Fourier admission is obtained from the actual first-label
support and the original volume. No error energy estimate is a premise. -/
theorem eventual_actual_geometry_error_fourier_admission
    (N : ℕ) (b : ℝ) (hb : 1≤ b) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (amp ξ reserve _t : ℝ)
      (hZ : 1< Z), Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      sourceRadius s≤ Z^(3:ℝ) → |Real.logb Z (volume s)|≤3 →
      0≤ amp → amp≤1 → 0≤ξ → ξ≤1 → 0≤ reserve → frequencyLoss Z 32 ξ+reserve≤3 →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
        (p : O) (_hp : p≠0) (i : Fin 3),
      0< frequencyRadius (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i) Z ξ ∧
      frequencyRadius (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i) Z ξ≤ Z^(24:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop (b^N)] with Z hZ hbZ
  refine ⟨hZ, ?_⟩
  intro reflected s R seed amp ξ reserve t hZ' hs hz₁ hz₂ hsource hV ha ha₁ hξ hξ₁ hr hω bin q p hp i
  let l := geometryFirstLabel s R seed (Z^(1:ℝ)) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val
  let src := geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val.1
  have hcaps := actual_geometry_error_tail_label_caps s R seed 1 Z ξ 3 hZ'
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) hs hz₁ hz₂ hsource bin q.1.val
  have hk : 1≤ errorIndex i+1 := Nat.succ_le_succ (Nat.zero_le _)
  have hbox := actual_error_radius_box reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex src.C src.D=>P.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported _ _ src.hC _).1 src.sameSupport
    Z 1 (volume s) amp (frequencyLoss Z 32 ξ) reserve 3 hZ' (volume_pos s)
    (by norm_num) (by norm_num) (by norm_num) ha (by linarith)
    (frequencyLoss_nonneg Z 32 ξ hZ' (by norm_num) hξ) hr hω hV
    hcaps.1 hcaps.2.1 hcaps.2.2.1 hcaps.2.2.2 p hp (errorIndex i+1) hk
  let rad := geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ' bin q p i
  have hrad : Z^(-15:ℝ)≤ rad := by
    have hexp : (-5:ℝ)*3=(-15:ℝ) := by norm_num
    rw [hexp] at hbox
    change Z^(-15:ℝ)≤ geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ' bin q p i
    unfold geometryErrorSourceRadius
    rw [actual_geometry_error_tail_radius]
    exact hbox.1
  have hradpos := actual_geometry_error_source_radius_pos reflected s R seed Z 1 amp ξ reserve hZ' bin q p i
  have hI := norm_ge_one _ (allocation_ne s _ q.2)
  have hpN := norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp)
  have hpN' : (1:ℝ)≤(normValue p)^(errorIndex i+1) := by
    exact one_le_pow₀ hpN
  have hvol : volume s≤ Z^(3:ℝ) :=
    (Real.logb_le_iff_le_rpow hZ' (volume_pos s)).mp (abs_le.mp hV).2
  have hnum : b^N*volume s/
      (((geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val).absNorm:ℝ)*(normValue p)^(errorIndex i+1))≤ Z^(4:ℝ) := by
    calc
      _≤ b^N*volume s := div_le_self (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le)
        (one_le_mul_of_one_le_of_one_le hI hpN')
      _≤ Z*Z^(3:ℝ) := mul_le_mul hbZ hvol (volume_pos s).le (by linarith)
      _=Z^(4:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add (zero_lt_one.trans hZ')]; norm_num
  have hnumpos : 0< b^N*volume s/
      (((geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val).absNorm:ℝ)*(normValue p)^(errorIndex i+1)) := by
    have hi0 := zero_lt_one.trans_le hI
    have hp0 := zero_lt_one.trans_le hpN'
    have hbpos := zero_lt_one.trans_le hb
    have hv := volume_pos s
    positivity
  have hT : geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ' bin q p i≤ Z^(23:ℝ) := by
    unfold geometryErrorFourierScale
    calc
      _≤(Z^(4:ℝ))^2/Z^(-15:ℝ) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ hnumpos.le hnum 2)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) hrad
      _=Z^(23:ℝ) := by
        rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ').le,←Real.rpow_sub (zero_lt_one.trans hZ')]
        norm_num
  refine ⟨?_, ?_⟩
  · change 0 < geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ' bin q p i*Z^(ξ/2)
    exact mul_pos (div_pos (pow_pos hnumpos _) hradpos)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _)
  · unfold frequencyRadius
    calc
      _≤ Z^(23:ℝ)*Z^(ξ/2) := mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (by linarith) _)
      _=Z^(23+ξ/2) := (Real.rpow_add (zero_lt_one.trans hZ') _ _).symm
      _≤ _ := Real.rpow_le_rpow_of_exponent_le hZ'.le (by linarith)

section Prime
variable (rayM : Ideal O) [NeZero rayM]
local instance geometryExceptionalAdmissionPrimeFinite : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ)

theorem actual_geometry_exceptional_prime_cap (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad) (Z amp : ℝ) (hZ : 1< Z) (ha : amp≤3)
    (p : O) (hp : p∈elementPool (primePool rayM H Sbad (1/2) 1 (Z^amp))) :
    p≠0 ∧ ((Ideal.span {p}).absNorm:ℝ)≤ Z^(3:ℝ) := by
  have hd := elementPool_data _
    (fun Q hQ=>(primePool_data rayM H Sbad hbad (1/2) 1 (Z^amp) Q hQ).1)
    (fun Q hQ=>(primePool_data rayM H Sbad hbad (1/2) 1 (Z^amp) Q hQ).2) p hp
  have hn := norm_bounds_of_mem_annularPrimeIdeals (show (0:ℝ)≤1/2 by norm_num)
    (show (1/2:ℝ)≤1 by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Finset.mem_sdiff.mp hd.2.1).1
  refine ⟨hd.1.ne_zero, ?_⟩
  have hn' : ((Ideal.span {p}).absNorm:ℝ)≤ Z^amp := by simpa using hn.2
  exact hn'.trans (Real.rpow_le_rpow_of_exponent_le hZ.le ha)
end Prime

/-- The saved exceptional source receives the literal lifted active error
allocation. Every remaining premise is an arithmetic support or source receipt. -/
theorem eventual_actual_geometry_error_exceptional_admission
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (amp ξ reserve t : ℝ)
      (hZ : 1< Z), s.η=η → Fintype.card ι≤ N → Endpoints b bs bs s →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → volume s≤ Z^(2:ℝ) → sourceRadius s≤ Z^(3:ℝ) →
      |Real.logb Z (volume s)|≤3 → (R.absNorm:ℝ)≤ Z →
      0≤ amp → amp≤1 → 0≤ξ → ξ≤1 → 0≤ reserve → frequencyLoss Z 32 ξ+reserve≤3 →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0 →
      ∀ (p : O) (_hp : p≠0), ((Ideal.span {p}).absNorm:ℝ)≤ Z^(3:ℝ) →
      (∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I) →
      ∀ (i : Fin 3)
        (Bp : actualAllocations (activeInput
          (geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
              ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (χ : RayCharacter) (v : ℝ),
      υ.modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) χ)
          fixedBadMask p (errorMovingExponent (errorIndex i)) →
      let u := geometryErrorChild reflected s R seed Z 1 ξ t hZ bin q p i Bp υ v
      let F := frequencyRadius (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i) Z ξ
      0< F ∧ F≤ Z^(25:ℝ) ∧ sourceRadius u≤ Z^(126:ℝ) ∧
      (expandedFactor u.η:ℝ)*
        ((R*geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)).absNorm*
        (sourceRadius u)^2*(4*F)≤ Z^(126:ℝ) := by
  filter_upwards [eventually_source_caps,
    eventual_actual_geometry_error_fourier_admission (ι:=ι) N b hb,
    eventually_ge_atTop (geometry N b bs bs), eventually_ge_atTop (η.modulus.absNorm:ℝ),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop rayCost]
    with Z he hfourier hgeom hη hcost hray
  refine ⟨he.1, ?_⟩
  intro reflected s R seed amp ξ reserve t hZ hsame hn hend hs hz₁ hz₂ hV hsource hlogV hR
    ha ha₁ hξ hξ₁ hreserve hω bin q hne p hp hpN hslot i Bp υ χ v hυ u F
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let I := geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK bin q.1.val
  let τ := geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hK bin q.1.val
  have hz := zero_lt_one.trans hZ
  have hc := actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂ hsource q.1.val.1.val
  have hI : (I.absNorm:ℝ)≤ Z^(3:ℝ) := by
    cases reflected
    · exact (hc 0).2
    · exact (hc 1).2
  have hτ := actual_geometry_exceptional_character_cap reflected s R seed (Z^(1:ℝ)) Z ξ 3 hK
    hs hz₁ hz₂ hsource bin q.1.val
  have hτ₈ : (τ.modulus.absNorm:ℝ)≤ Z^(8:ℝ) := by
    apply hτ.trans
    rw [hsame]
    calc
      _≤ Z*Z*(Z^(3:ℝ))^2 := by gcongr
      _=Z^(8:ℝ) := by
        rw [show (Z^(3:ℝ))^2=Z^(3:ℝ)*Z^(3:ℝ) by ring]
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        conv_lhs => arg 1; arg 2; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hυ₁₂ : (u.η.modulus.absNorm:ℝ)≤ Z^(12:ℝ) := by
    have hh := radical_once_cap τ υ χ p hp (errorMovingExponent (errorIndex i)) hυ
    change (υ.modulus.absNorm:ℝ)≤ _
    apply hh.trans
    calc
      _≤ Z*Z^(8:ℝ)*Z^(3:ℝ) := by gcongr
      _=Z^(12:ℝ) := by
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hk₇ : errorIndex i+1≤7 := by rcases error_extracted_index_cases i with h|h|h <;> omega
  have hp₇ : ((Ideal.span {p}).absNorm:ℝ)^(errorIndex i+1)≤ Z^(21:ℝ) := by
    calc
      _≤(Z^(3:ℝ))^(errorIndex i+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hpN _
      _≤(Z^(3:ℝ))^7 := pow_le_pow_right₀ (Real.one_le_rpow hZ.le (by norm_num)) hk₇
      _=Z^(21:ℝ) := by rw [←Real.rpow_mul_natCast hz.le]; norm_num
  have hpuncture : (((R*I)*(Ideal.span {p})^(errorIndex i+1)).absNorm:ℝ)≤ Z^(25:ℝ) := by
    rw [map_mul,map_mul,map_pow,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow]
    calc
      _≤(Z*Z^(3:ℝ))*Z^(21:ℝ) := by gcongr
      _=Z^(25:ℝ) := by
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hcchild := twice_caps N b bs bs hb hbs hbs s hn hend I R q.2 τ t hne
    (Ideal.span {p}) (Ideal.span_singleton_eq_bot.not.mpr hp) (errorIndex i+1) hslot
    (errorActiveAllocation _ _ Bp) υ v
  have hrad : sourceRadius u≤ Z^(3:ℝ) := by
    have hh : sourceRadius u≤ geometry N b bs bs*volume s/
        ((I.absNorm:ℝ)*((Ideal.span {p}).absNorm:ℝ)^(errorIndex i+1)) := by
      convert hcchild.2.2.2 using 1
      · rfl
      · simp only [CenteredMomentAmplificationChildInput.volume,mul_div_assoc]
    have hden := one_le_mul_of_one_le_of_one_le (norm_ge_one I (allocation_ne s I q.2))
      (one_le_pow₀ (n:=errorIndex i+1) (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp)))
    calc
      _≤ geometry N b bs bs*volume s := hh.trans (div_le_self
        (mul_nonneg ((geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)) (volume_pos s).le) hden)
      _≤ Z*Z^(2:ℝ) := mul_le_mul hgeom hV (volume_pos s).le hz.le
      _=Z^(3:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]; norm_num
  have hu₀ : 0≤ sourceRadius u := by
    have ht := endpoints_child b bs bs s hend I R q.2 τ t
    have htt := endpoints_child b bs bs (child s I R q.2 τ t) ht _ (R*I)
      (errorActiveAllocation _ _ Bp) υ v
    exact (radius_bound N b bs bs hb hbs hbs u
      ((live_card_le (errorActiveAllocation _ _ Bp).val).trans ((live_card_le q.2.val).trans hn)) htt).1
  have hf := hfourier.2 reflected s R seed amp ξ reserve t hZ hs hz₁ hz₂ hsource hlogV
    ha ha₁ hξ hξ₁ hreserve hω bin q p hp i
  have hu₂₅ := hrad.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (3:ℝ)≤25 by norm_num))
  have hυ₂₅ := hυ₁₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (12:ℝ)≤25 by norm_num))
  have hF₂₅ := hf.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (24:ℝ)≤25 by norm_num))
  have hh := he.2 u.η ((R*I)*(Ideal.span {p})^(errorIndex i+1)) (sourceRadius u) F 25
    (by norm_num) hu₀ hf.1.le hυ₂₅ hpuncture hu₂₅ hF₂₅
  have hnum : 5*(25:ℝ)+1=126 := by norm_num
  rw [hnum] at hh
  exact ⟨hf.1,hF₂₅,hh.1,hh.2⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_exceptional_plain_minimum
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_fixed_character_plain_loss
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_exceptional_character_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_exceptional_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_exceptional_minimum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_minimum
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_fourier_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_exceptional_prime_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_exceptional_admission

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalAdmission -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalScalar; sha256 9710564291909093c41a66c93b4a978b70de963b8c386123106a036a3150e1a1 -/
section
                                                              
                                                 
                                                         
                                                                          

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentFirstAllocationGaussEnergy
local notation "O" => HeckeFamily.O

lemma exceptional_side_power (Z V I P R E S : ℝ) (hZ : 1< Z)
    (hV : 0< V) (hI : 0< I) (hP : 0< P) (hR : 0< R) (hE : 0< E) :
    Z^(Real.logb Z P+Real.logb Z V-Real.logb Z I+
      Real.logb Z R+Real.logb Z E+S)=P*(V/I)*R*E*Z^S := by
  have hz := zero_lt_one.trans hZ
  simp only [Real.rpow_add hz,Real.rpow_sub hz,
    Real.rpow_logb hz hZ.ne' hP,Real.rpow_logb hz hZ.ne' hV,
    Real.rpow_logb hz hZ.ne' hI,Real.rpow_logb hz hZ.ne' hR,
    Real.rpow_logb hz hZ.ne' hE]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryExceptionalScalarSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The actual side normalization already contains the entire presented
conductor. The radical factor is retained for the arithmetic label sum. -/
theorem actual_geometry_exceptional_denominator (reflected : Bool)
    (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    let src := geometryFirstSource s R seed K Z ξ hK key j.1
    let χ := geometryColumnCharacter reflected s R seed K Z ξ hK key j
    let I := geometryColumnIdeal reflected s R seed K Z ξ hK key j
    let v := geometryExponents s R seed K Z ξ j.1.val
    let S := if reflected then max (3*v 1-5*v 0-v 3) 0/6
      else max (3*v 0-5*v 1-v 3) 0/6
    Z^(if reflected then rightExponent (Real.logb Z (volume s.toData)) v
      else leftExponent (Real.logb Z (volume s.toData)) v)=
      ((commonRadical src.C src.D).absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))*
        ((χ.modulus.absNorm:ℝ)/(fixedPresentationCost*(s.η.modulus.absNorm:ℝ)))*Z^S := by
  intro src χ I v S
  have hC := norm_pos src.C src.hC.1
  have hD := norm_pos src.D src.hD.1
  have hP := norm_pos (commonRadical src.C src.D) (commonRadical_ne_zero _ _)
  have hR := active_norm_pos src.C src.D
  have hE := norm_pos _ (subsetGenerator_supported src.C src.D src.hC src.inactive).1
  have hq := fixed_presentation_norm s.η χ src.C src.D src.inactive
    (actual_geometry_column_modulus reflected s R seed K Z ξ hK key j)
  simp only [eisEmbedding_norm_sq_eq_absNorm_span] at hq
  have hfixed := fixedPresentationCost_pos
  have hη := norm_pos s.η.modulus s.η.modulus_ne_bot
  have hV := volume_pos s.toData
  cases reflected
  · change Z^(Real.logb Z ((commonRadical src.C src.D).absNorm:ℝ)+
      Real.logb Z (volume s.toData)-Real.logb Z (src.C.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val)
        src.inactive}).absNorm:ℝ)+S)=_
    rw [exceptional_side_power Z _ _ _ _ _ S hZ hV hC hP hR hE,hq]
    simp only [I,geometryColumnIdeal,Bool.false_eq_true,ite_false,ite_true]
    dsimp only [src] at hC hD ⊢
    field_simp [hC.ne',hD.ne']
    <;> ring
  · change Z^(Real.logb Z ((commonRadical src.C src.D).absNorm:ℝ)+
      Real.logb Z (volume s.toData)-Real.logb Z (src.D.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val)
        src.inactive}).absNorm:ℝ)+S)=_
    rw [exceptional_side_power Z _ _ _ _ _ S hZ hV hD hP hR hE,hq]
    simp only [I,geometryColumnIdeal,Bool.false_eq_true,ite_false,ite_true]
    dsimp only [src] at hC hD ⊢
    field_simp [hC.ne',hD.ne']
    <;> ring

/-- Squared geometry scalars match the exceptional reference denominator.
Physical D appears as D on the left and 1/D on the reflected right. -/
theorem actual_geometry_exceptional_scalar (reflected : Bool)
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1< Z)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)) :
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
    let χ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j
    let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
    let S := if reflected then max (3*v 1-5*v 0-v 3) 0/6
      else max (3*v 0-5*v 1-v 3) 0/6
    ‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M (Real.logb Z (volume s.toData))
      hK key (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2/(I.absNorm:ℝ)≤
      (if reflected then 1/(src.D.absNorm:ℝ)
        else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((volume s.toData/(I.absNorm:ℝ))/
        ((χ.modulus.absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))^2*Z^S)) := by
  intro hK src χ I v S
  have hC := norm_pos src.C src.hC.1
  have hD := norm_pos src.D src.hD.1
  have hP := norm_pos (commonRadical src.C src.D) (commonRadical_ne_zero _ _)
  have hq := norm_pos χ.modulus χ.modulus_ne_bot
  have hV := volume_pos s.toData
  have hfixed := fixedPresentationCost_pos
  have hη := norm_pos s.η.modulus s.η.modulus_ne_bot
  have hpower := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) S
  have hp := actual_geometry_exceptional_denominator reflected s R seed (Z^M) Z ξ hK hZ key j
  cases reflected
  · simp only [Bool.false_eq_true,ite_false,ite_true] at hp ⊢
    change Z^(leftExponent (Real.logb Z (volume s.toData)) v)=_ at hp
    have hh := div_le_div_of_nonneg_right
      (actual_geometry_left_scalar_sq s R seed W M Z ξ hZ a₁ a₂ ha₁ ha₂ hs₁ hs₂ key j) hC.le
    apply hh.trans_eq
    change (_*(src.C.absNorm:ℝ)*(src.D.absNorm:ℝ)/Z^(leftExponent _ v))/(src.C.absNorm:ℝ)=_
    rw [hp]
    simp only [src,χ,I,v,S,geometryColumnIdeal,Bool.false_eq_true,ite_false,ite_true] at *
    field_simp [hC.ne',hD.ne',hP.ne',hq.ne',hV.ne',hfixed.ne',hη.ne',hpower.ne']
    <;> ring
  · simp only [Bool.false_eq_true,ite_false,ite_true] at hp ⊢
    change Z^(rightExponent (Real.logb Z (volume s.toData)) v)=_ at hp
    have he : ‖geometryColumnScalar true s R seed (Z^M) Z ξ M
        (Real.logb Z (volume s.toData)) hK key
        (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2=
        1/Z^(rightExponent (Real.logb Z (volume s.toData)) v) := by
      dsimp only [v]
      simp only [geometryColumnScalar,ite_true,norm_inv,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,
        Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans hZ).le _),one_div]
    apply le_of_eq
    rw [he,hp]
    simp only [src,χ,I,v,S,geometryColumnIdeal,Bool.false_eq_true,ite_false,ite_true] at *
    field_simp [hC.ne',hD.ne',hP.ne',hq.ne',hV.ne',hfixed.ne',hη.ne',hpower.ne']
    <;> ring

/-- The actual allocation weight pays the presented exceptional denominator
while retaining the physical side factor and arithmetic radical. -/
theorem actual_geometry_exceptional_allocation_weight (reflected : Bool)
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1< Z)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key))
    (N : ℕ) (b : ℝ)
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j)) :
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
    let χ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j
    let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
    let S := if reflected then max (3*v 1-5*v 0-v 3) 0/6
      else max (3*v 0-5*v 1-v 3) 0/6
    geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (volume s.toData)) hK key
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j B≤
      ((if reflected then 1/(src.D.absNorm:ℝ)
        else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((volume s.toData/(I.absNorm:ℝ))/
        ((χ.modulus.absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))^2*Z^S)))*
        ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)*(frozenControl B.val s.M)^2) := by
  intro hK src χ I v S
  let U := (if reflected then 1/(src.D.absNorm:ℝ)
        else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((volume s.toData/(I.absNorm:ℝ))/
        ((χ.modulus.absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))^2*Z^S))
  let T := (max 1 b)^N*((actualAllocations s.pools I).card:ℝ)*(frozenControl B.val s.M)^2
  have hg := actual_geometry_exceptional_scalar reflected s R seed W M Z ξ hZ
    a₁ a₂ ha₁ ha₂ hs₁ hs₂ key j
  change ‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M
    (Real.logb Z (volume s.toData)) hK key
    (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2/(I.absNorm:ℝ)≤ U at hg
  have ht : 0≤ T := by dsimp [T]; positivity
  have hu : 0≤ U := (by positivity : 0≤‖geometryColumnScalar reflected s R seed
    (Z^M) Z ξ M (Real.logb Z (volume s.toData)) hK key
    (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2/(I.absNorm:ℝ)).trans hg
  change _≤ U*T
  unfold geometryAllocationWeight
  dsimp only
  split_ifs
  · have hh := mul_le_mul_of_nonneg_right hg ht
    convert hh using 1 <;> dsimp only [T,I] <;> ring
  · exact mul_nonneg hu ht

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.exceptional_side_power
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_exceptional_denominator
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_exceptional_scalar

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_exceptional_allocation_weight

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalScalar -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalAggregate; sha256 3f7b1da1686303b1f96957d12d1bfe87416821b2dca97f6f68d629d2a6fe103e -/
section
                                                             
                                                                
                                                       
                                                                   
                                                                      

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Cycle61Moment HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSecondEnergySplit RayFourExpansion
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentSecondExceptionalFamily
open CenteredMomentCommonProfile ConcretePrimeRowBridge CenteredMomentActive
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstMixedRoot CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def geometryExceptionalVolume {α : Type*} [Fintype α] (d : Input α) : ℝ :=
  CenteredMomentExceptionalAmplitudePair.volume d.toData
local instance geometryExceptionalAggregateSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

section Main
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
variable (M Z ξ sigma reserve t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
variable (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
variable (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
private def geometryMainExceptionalReferenceCore (τ : Character) (I H E : Ideal O)
    (K X Z sigma delta reserve r : ℝ) : ℝ :=
  ((X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
    Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I H}).absNorm:ℝ)) 0/6)))*
    (X/(I.absNorm:ℝ))^(1/3:ℝ)*
    (mainCommonRadius Z (Real.logb Z (H.absNorm:ℝ)) (nominalLog I H E K X Z)
      (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^(5/6:ℝ)*Z^(-sigma/3)*
    Z^(-2*max r 0/3)

private theorem geometry_main_exceptional_reference_core_eq (τ : Character) (I H E : Ideal O)
    (K X Z sigma delta reserve r : ℝ) :
    geometryMainExceptionalReferenceCore τ I H E K X Z sigma delta reserve r=
      geometryExceptionalMainReference τ I H E K X Z sigma delta reserve r := by
  dsimp only [geometryMainExceptionalReferenceCore,geometryExceptionalMainReference]
  ring

/-- The literal actual main-child reference, with its actual input minimum. -/
def geometryMainExceptionalReferenceActual : ℝ :=
  let src := geometryFirstSource s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
  let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  geometryMainExceptionalReferenceCore τ I (if reflected then src.C else src.D)
    (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
    (Z^M) (geometryExceptionalVolume s) Z sigma (frequencyLoss Z 32 ξ) reserve
    (inputCap Z (child s I R B τ t))

omit [DecidableEq ι] in
/-- Orientation transport is arithmetic. It uses the swapped inactive subset,
not an assumption about the exceptional energy or its prefactor. -/
theorem actual_geometry_main_exceptional_reference_bound (plainLoss : ℝ)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂) :
    geometryMainExceptionalReferenceActual reflected s R seed M Z ξ sigma reserve t hZ bin j B≤
      Z^(Real.logb Z (geometryExceptionalVolume s)-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3) := by
  let src := (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1)
  have hklog : Real.logb Z (Z^M)=M := Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hm := actual_geometry_column_modulus reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  cases reflected
  · have hh := actual_main_child_exceptional_reference s.η (geometryColumnCharacter false s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) src.C src.D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
      src.hC src.hD src.sameSupport src.inactive rfl s R B (Z^M) Z sigma
      (frequencyLoss Z 32 ξ) reserve t plainLoss (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    change geometryMainExceptionalReferenceCore _ _ _ _ _ _ _ _ _ _ _≤ _ 
    rw [geometry_main_exceptional_reference_core_eq]
    exact hh

  · have hm' : (geometryColumnCharacter true s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.D src.C=>P.val)
          (swapSubset src.C src.D src.inactive)*activeConductor src.D src.C} := by
      rw [swapped_modulus_factor]
      exact hm
    have hh := actual_main_child_exceptional_reference s.η (geometryColumnCharacter true s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) src.D src.C
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
      src.hD src.hC src.sameSupport.symm (swapSubset src.C src.D src.inactive)
      (by rw [swapSubset_generator]) s R B (Z^M) Z sigma
      (frequencyLoss Z 32 ξ) reserve t plainLoss (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm'
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    change geometryMainExceptionalReferenceCore _ _ _ _ _ _ _ _ _ _ _≤ _
    rw [geometry_main_exceptional_reference_core_eq]
    exact hh

set_option linter.defProp false in
set_option linter.unnecessarySeqFocus false in
/-- The actual weighted whole exceptional energy pays the original-slot
profile control. The first projector seed and physical side remain visible.
The proof-valued definition infers its actual dependent statement. -/
def actual_geometry_main_exceptional_paid
    (wlo whi : ℝ) (p : Profiles wlo whi) (ε δ θ Bcap L Cr : ℝ)
    (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ) (Qfix : Ideal O) (Kfix : ℝ)
    (hKfix : 0≤ Kfix) (hCk : 0≤ Ck)
    (N : ℕ) (b : ℝ) (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    :=
    let I := (geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
    let τ := (geometryColumnCharacter reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
    let u := child s I R B τ t
    let src := (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1)
    let Kmain := (firstMainRadius reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve (geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    fun (hest : geometryExceptionalSourceEstimate wlo whi u.lo u.hi W ε δ θ Bcap L Cr
      J Sp Ck Qfix Kfix Z)
    (hP : ∀i,1≤ u.P i) (hp₁ : u.W₁=p.profile 0) (hp₂ : u.W₂=p.profile 1)
    (hR : R*I≠0) (hseed : Squarefree j.2.1.val) (hseed0 : j.2.1.val≠0)
    (hcap : sourceRadius u≤ Z^Bcap) (χ₀ : RayCharacter) (m : O)
    (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Tsec : ℝ)
    (hF : 0< frequencyRadius Tsec Z ξ) (hFc : frequencyRadius Tsec Z ξ≤ Cr*Z^L)
    (hcond : (expandedFactor u.η:ℝ)*(R*I).absNorm*(sourceRadius u)^2*
      (4*frequencyRadius Tsec Z ξ)≤ Z^Bcap)
    (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0)=>
    have hparentV : 0< geometryExceptionalVolume s :=
      CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
    have hchildV : 0< geometryExceptionalVolume u :=
      CenteredMomentExceptionalAmplitudePair.volume_pos u.toData
    have hI := norm_pos I (allocation_ne s I B)
    have hfixed := fixedPresentationCost_pos
    have hrad := norm_pos (commonRadical
      src.C
      src.D)
      (commonRadical_ne_zero _ _)
    have hτ := norm_pos (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus_ne_bot
    have hbn : 0≤ b^N := pow_nonneg (zero_le_one.trans hb) _
    have hbase : 0≤((∏i,u.lo i)*wlo*wlo) := by
      rw [mul_assoc,←sq]
      exact mul_nonneg (Finset.prod_nonneg (fun i _=>u.lo_pos i |>.le)) (sq_nonneg wlo)
    have hlower := Real.rpow_nonneg hbase (-2/3:ℝ)
    have hmin := input_cap_scales Z hZ u
    have he := hest u p (fun _=>rfl) (fun _=>rfl) hP hp₁ hp₂
      (R*I) j.2.1.val hR hseed hseed0 hcap χ₀ m hm hml hm2 Tsec ξ Kmain
      (first_main_radius_pos reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve
        (zero_lt_one.trans hZ) (geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)) hF hFc hcond (inputCap Z u)
      hmin.1 hmin.2.1 hmin.2.2.1 hmin.2.2.2
    have hw := actual_geometry_exceptional_allocation_weight reflected s R seed W M Z ξ hZ
      a₁ a₂ ha₁ ha₂ hs₁ hs₂ bin j N b B
    have hp := actual_child_exceptional_profile_payment Sp p J Qfix Kfix hKfix
      N b hb s hu hc I R B τ t
    have hv := common_volume_le N b hb s hc hu I R B τ t hne
    have hvol : (geometryExceptionalVolume u)^(1/3:ℝ)≤(b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ))^(1/3:ℝ) := by
      have hi := norm_pos I (allocation_ne s I B)
      calc
        _≤(b^N*geometryExceptionalVolume s/(I.absNorm:ℝ))^(1/3:ℝ) :=
          Real.rpow_le_rpow hchildV.le hv (by norm_num)
        _=_ := by rw [mul_div_assoc,Real.mul_rpow (by positivity) (by positivity)]
    have hzero : 0≤‖partEnergy true u.η χ₀ Qfix m u.t
        (finiteColumns (Fintype.piFinset u.pools)) (coefficient u (R*I) j.2.1.val)
        W Kmain Tsec Z ξ (sourceRadius u)‖/geometryExceptionalVolume u :=
      div_nonneg (norm_nonneg _) hchildV.le
    let U := (if reflected then 1/(src.D.absNorm:ℝ)
      else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((geometryExceptionalVolume s/(I.absNorm:ℝ))/
        ((τ.modulus.absNorm:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ))^2*
          Z^(if reflected then max (3*geometryExponents s R seed (Z^M) Z ξ j.1.val 1-
            5*geometryExponents s R seed (Z^M) Z ξ j.1.val 0-
            geometryExponents s R seed (Z^M) Z ξ j.1.val 3) 0/6 else
            max (3*geometryExponents s R seed (Z^M) Z ξ j.1.val 0-
            5*geometryExponents s R seed (Z^M) Z ξ j.1.val 1-
            geometryExponents s R seed (Z^M) Z ξ j.1.val 3) 0/6)))
    let A := (max 1 b)^N*((actualAllocations s.pools I).card:ℝ)
    let F := (frozenControl B.val s.M)^2
    let Pf := profileFactor Sp u p J Qfix Kfix
    let Ppaid := CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix*
      p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6
    let Vc := (geometryExceptionalVolume u)^(1/3:ℝ)
    let Vb := (b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ))^(1/3:ℝ)
    let Dpaid := Ck*Z^(2*ε+2*δ+2*Bcap*θ+sigma/3)*Z^(-sigma/3)*
      Z^(-2*max (inputCap Z u) 0/3)*
      Kmain^(5/6:ℝ)*((∏i,u.lo i)*wlo*wlo)^(-2/3:ℝ)/(j.2.1.val.absNorm:ℝ)
    let E := ‖partEnergy true u.η χ₀ Qfix m u.t (finiteColumns (Fintype.piFinset u.pools))
      (coefficient u (R*I) j.2.1.val) W Kmain Tsec Z ξ (sourceRadius u)‖/geometryExceptionalVolume u
    have hside : 0≤(if reflected then 1/(src.D.absNorm:ℝ)
      else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)) := by split_ifs <;> positivity
    have hU : 0≤ U := by
      dsimp only [U]
      exact mul_nonneg (mul_nonneg hside
        (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le))
        (div_nonneg (div_nonneg hparentV.le hI.le)
          (mul_nonneg (mul_nonneg hτ.le (sq_nonneg _))
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    have hA : 0≤ A :=
      mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
        (Nat.cast_nonneg _)
    have hD : 0≤ Dpaid := by
      dsimp only [Dpaid]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg hCk (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (first_main_radius_pos reflected (Z^M) (geometryExceptionalVolume s)
          Z ξ sigma reserve (zero_lt_one.trans hZ)
          (geometryFirstLabel s R seed (Z^M) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)).le _)) hlower)
        (Nat.cast_nonneg _)
    have hPf : 0≤ Pf := profileFactor_nonneg Sp u p J Qfix Kfix hKfix
    have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (geometryExceptionalVolume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j B≤ U*A*F := by
      convert hw using 1 <;> dsimp only [U,A,F,geometryExceptionalVolume] <;> ring
    have hpower : Z^(2*ε+2*δ+2*Bcap*θ-2*max (inputCap Z u) 0/3)=
      Z^(2*ε+2*δ+2*Bcap*θ+sigma/3)*Z^(-sigma/3)*Z^(-2*max (inputCap Z u) 0/3) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 1
      ring
    have he0 : E≤ Dpaid*Pf*Vc := by
      have hh := he
      conv_rhs at hh => arg 1;arg 1;arg 1;arg 1;arg 2;rw [hpower]
      convert hh using 1 <;> dsimp only [E,Dpaid,Pf,Vc,geometryExceptionalVolume] <;> ring
    have hp0 : F*Pf≤ Ppaid := hp
    have hv0 : Vc≤ Vb := hvol
    have hq := mul_le_mul hp0 hv0 (Real.rpow_nonneg hchildV.le _) 
      ((mul_nonneg (sq_nonneg (frozenControl B.val s.M)) hPf).trans hp0)
    have hpaid := mul_le_mul hw0 he0 hzero
      (mul_nonneg (mul_nonneg hU hA) (sq_nonneg _))
    have hfinal : (U*A*F)*(Dpaid*Pf*Vc)≤(U*A*Dpaid)*(Ppaid*Vb) := by
      convert mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg hU hA) hD) using 1 <;> ring
    hpaid.trans hfinal

set_option linter.defProp false in
set_option linter.unnecessarySeqFocus false in
/-- The literal twice-child exceptional energy pays both common-allocation
controls. The prime cost and true prime-power volume remain explicit.
The proof-valued definition infers its actual dependent statement. -/
def actual_geometry_error_exceptional_paid
    (wlo whi : ℝ) (p0 : Profiles wlo whi) (ε δ θ Bcap L Cr : ℝ)
    (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ) (Qfix : Ideal O) (Kfix : ℝ)
    (hKfix : 0≤ Kfix) (hCk : 0≤ Ck)
    (N : ℕ) (b : ℝ) (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x) :=
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let u1 := child s I R B τ t
    let src := geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
    let gv := geometryExponents s R seed (Z^M) Z ξ j.1.val
    let S := if reflected then max (3*gv 1-5*gv 0-gv 3) 0/6
      else max (3*gv 0-5*gv 1-gv 3) 0/6
    fun (p : O) (hp : p≠0) (k : ℕ)
      (Bp : actualAllocations u1.pools ((Ideal.span {p})^k)) (υ : Character) (v : ℝ)
      (hslot : ∀i,∀Q∈u1.slots i,IsCoprime (Ideal.span {p}) Q) =>
    let Q := Ideal.span {p}
    let u := twiceChild s I R B τ t Q k Bp υ v
    let Kerror := errorCommonRadius Z
      (Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ))
      (nominalLog src.C src.D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
        (Z^M) (geometryExceptionalVolume s) Z)
      (Real.logb Z (I.absNorm:ℝ)) sigma (frequencyLoss Z 32 ξ) reserve p k
    fun (hest : geometryExceptionalSourceEstimate wlo whi u.lo u.hi W ε δ θ Bcap L Cr
      J Sp Ck Qfix Kfix Z)
      (hP : ∀i,1≤ u.P i) (hp₁ : u.W₁=p0.profile 0) (hp₂ : u.W₂=p0.profile 1)
      (hR : (R*I)*(Q^k)≠0) (hseed : Squarefree j.2.1.val) (hseed0 : j.2.1.val≠0)
      (hcap : sourceRadius u≤ Z^Bcap) (χ₀ : RayCharacter) (m : O)
      (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Tsec : ℝ)
      (hF : 0< frequencyRadius Tsec Z ξ) (hFc : frequencyRadius Tsec Z ξ≤ Cr*Z^L)
      (hcond : (expandedFactor u.η:ℝ)*((R*I)*(Q^k)).absNorm*(sourceRadius u)^2*
        (4*frequencyRadius Tsec Z ξ)≤ Z^Bcap)
      (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0) =>
    have hparentV : 0< geometryExceptionalVolume s :=
      CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
    have hchildV : 0< geometryExceptionalVolume u :=
      CenteredMomentExceptionalAmplitudePair.volume_pos u.toData
    have hfixed := fixedPresentationCost_pos
    have hrad := norm_pos (commonRadical src.C src.D) (commonRadical_ne_zero _ _)
    have hτ := norm_pos τ.modulus τ.modulus_ne_bot
    have hI := norm_pos I (allocation_ne s I B)
    have hQ : Q≠(0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hp
    have hNQ := norm_pos Q hQ
    have hBpone (i) : Bp.val (Sum.inl i)=1 :=
      CenteredMomentAmplificationAllocationCost.allocation_slot_one u1.pools Q hQ k
        (fun i D hd=>⟨u1.pools_ne (Sum.inl i) D hd,hslot i D hd⟩) Bp i
    have hfBp : frozenControl Bp.val u1.M=1 := by
      dsimp only [frozenControl]
      simp only [hBpone,ne_eq,not_true_eq_false,Finset.filter_false,Finset.prod_empty]
    have hbn : 0≤ b^N := pow_nonneg (zero_le_one.trans hb) _
    have hcost := localErrorCost_nonneg p (k-1)
    have hbase : 0≤((∏i,u.lo i)*wlo*wlo) := by
      rw [mul_assoc,←sq]
      exact mul_nonneg (Finset.prod_nonneg (fun i _=>(u.lo_pos i).le)) (sq_nonneg wlo)
    have hlower := Real.rpow_nonneg hbase (-2/3:ℝ)
    have hmin := input_cap_scales Z hZ u
    have he := hest u p0 (fun _=>rfl) (fun _=>rfl) hP hp₁ hp₂ ((R*I)*(Q^k))
      j.2.1.val hR hseed hseed0 hcap χ₀ m hm hml hm2 Tsec ξ Kerror
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hF hFc hcond
      (inputCap Z u) hmin.1 hmin.2.1 hmin.2.2.1 hmin.2.2.2
    have hw := actual_geometry_exceptional_allocation_weight reflected s R seed W M Z ξ hZ
      a₁ a₂ ha₁ ha₂ hs₁ hs₂ bin j N b B
    have hp := actual_twice_exceptional_profile_payment Sp p0 J Qfix Kfix hKfix
      N b hb s hu hc I R B τ t Q k Bp υ v
    have hp' : (frozenControl B.val s.M)^2*profileFactor Sp u p0 J Qfix Kfix≤
        CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix*
          p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6 := by
      have hh := hp
      change (frozenControl B.val s.M)^2*(frozenControl Bp.val u1.M)^2*
        profileFactor Sp u p0 J Qfix Kfix≤ _ at hh
      rw [hfBp,one_pow,mul_one] at hh
      exact hh
    have hv1 := common_volume_le N b hb s hc hu I R B τ t hne
    have hv : geometryExceptionalVolume u≤ b^N*geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k := by
      change CenteredMomentAmplificationChildInput.volume (twiceChild s I R B τ t Q k Bp υ v)≤ _
      rw [twiceChild,child_volume _ Q hQ k hslot]
      exact div_le_div_of_nonneg_right hv1 (pow_nonneg hNQ.le k)
    have hvol : (geometryExceptionalVolume u)^(1/3:ℝ)≤
        (b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k)^(1/3:ℝ) := by
      calc
        _≤(b^N*geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k)^(1/3:ℝ) :=
          Real.rpow_le_rpow hchildV.le hv (by norm_num)
        _=_ := by
          rw [mul_div_assoc,mul_div_assoc,Real.mul_rpow hbn
            (div_nonneg (div_nonneg hparentV.le hI.le) (pow_nonneg hNQ.le k))]
    have hzero : 0≤‖partEnergy true u.η χ₀ Qfix m u.t
        (finiteColumns (Fintype.piFinset u.pools)) (coefficient u ((R*I)*(Q^k)) j.2.1.val)
        W Kerror Tsec Z ξ (sourceRadius u)‖/geometryExceptionalVolume u :=
      div_nonneg (norm_nonneg _) hchildV.le
    let U := (if reflected then 1/(src.D.absNorm:ℝ)
      else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((geometryExceptionalVolume s/(I.absNorm:ℝ))/
        ((τ.modulus.absNorm:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ))^2*
          Z^(if reflected then max (3*geometryExponents s R seed (Z^M) Z ξ j.1.val 1-
            5*geometryExponents s R seed (Z^M) Z ξ j.1.val 0-
            geometryExponents s R seed (Z^M) Z ξ j.1.val 3) 0/6 else
            max (3*geometryExponents s R seed (Z^M) Z ξ j.1.val 0-
            5*geometryExponents s R seed (Z^M) Z ξ j.1.val 1-
            geometryExponents s R seed (Z^M) Z ξ j.1.val 3) 0/6)))
    let A := (max 1 b)^N*((actualAllocations s.pools I).card:ℝ)
    let F := (frozenControl B.val s.M)^2
    let Pf := profileFactor Sp u p0 J Qfix Kfix
    let Ppaid := CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix*
      p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6
    let Vc := (geometryExceptionalVolume u)^(1/3:ℝ)
    let Vb := (b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k)^(1/3:ℝ)
    let Dpaid := Ck*Z^(2*ε+2*δ+2*Bcap*θ-2*max (inputCap Z u) 0/3)*
      Kerror^(5/6:ℝ)*((∏i,u.lo i)*wlo*wlo)^(-2/3:ℝ)/(j.2.1.val.absNorm:ℝ)
    let E := ‖partEnergy true u.η χ₀ Qfix m u.t (finiteColumns (Fintype.piFinset u.pools))
      (coefficient u ((R*I)*(Q^k)) j.2.1.val) W Kerror Tsec Z ξ (sourceRadius u)‖/geometryExceptionalVolume u
    have hside : 0≤(if reflected then 1/(src.D.absNorm:ℝ)
      else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)) := by split_ifs <;> positivity
    have hU : 0≤ U := by
      dsimp only [U]
      exact mul_nonneg (mul_nonneg hside
        (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le))
        (div_nonneg (div_nonneg hparentV.le hI.le)
          (mul_nonneg (mul_nonneg hτ.le (sq_nonneg _))
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    have hA : 0≤ A :=
      mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
        (Nat.cast_nonneg _)
    have hD : 0≤ Dpaid := by
      dsimp only [Dpaid]
      exact div_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg hCk (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) _)) hlower)
        (Nat.cast_nonneg _)
    have hPf : 0≤ Pf := profileFactor_nonneg Sp u p0 J Qfix Kfix hKfix
    have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (geometryExceptionalVolume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j B≤ U*A*F := by
      convert hw using 1 <;> dsimp only [U,A,F,geometryExceptionalVolume] <;> ring
    have he0 : E≤ Dpaid*Pf*Vc := by
      convert he using 1 <;> dsimp only [E,Dpaid,Pf,Vc,geometryExceptionalVolume] <;> ring
    have hp0 : F*Pf≤ Ppaid := hp'
    have hv0 : Vc≤ Vb := hvol
    have hq := mul_le_mul hp0 hv0 (Real.rpow_nonneg hchildV.le _) 
      ((mul_nonneg (sq_nonneg (frozenControl B.val s.M)) hPf).trans hp0)
    have hwcost := mul_le_mul_of_nonneg_right hw0 hcost
    have hpaid := mul_le_mul hwcost he0 hzero
      (mul_nonneg (mul_nonneg (mul_nonneg hU hA) (sq_nonneg _)) hcost)
    have hfinal : (U*A*F*localErrorCost p (k-1))*(Dpaid*Pf*Vc)≤
        (U*A*Dpaid*localErrorCost p (k-1))*(Ppaid*Vb) := by
      convert mul_le_mul_of_nonneg_left hq
        (mul_nonneg (mul_nonneg (mul_nonneg hU hA) hD) hcost) using 1 <;> ring
    hpaid.trans hfinal

end Main

/-- Actual supported equal-support labels retain their reciprocal radical.
The independent first-projector union is paid by its reciprocal norm. -/
theorem eventual_exceptional_radical_projector_payment (B L ε : ℝ)
    (hB : 0≤ B) (hL : 0≤ L) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in Filter.atTop,2≤ Z ∧
      ∀ (T factor : ℝ),0< T → T≤ Z^B → 0≤ factor →
      ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,T≤((commonRadical l.1.1 l.1.2).absNorm:ℝ) ∧
        ((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤2*T) →
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) →
      (∀D∈Ds,(D.absNorm:ℝ)≤ Z^L) →
      (∑l∈labels,∑D∈Ds,factor/
        (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ)))≤
        C*factor*Z^(2*ε)/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := actual_first_low_label_count (B+1) ε (by linarith) hε
  obtain ⟨D,hD,hprojector⟩ := eventual_projector_reciprocal L ε hL hε
  refine ⟨2*C*D,by positivity,?_⟩
  filter_upwards [hprojector,Filter.eventually_ge_atTop (2:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro T factor hT hTZ hf seed hs hs0 labels hsup heq hseed hnorm hrad Ds hDs hcap
  have hzpos := zero_lt_one.trans hz.1
  have hpow : Z^B≤ Z^(B+1) := Real.rpow_le_rpow_of_exponent_le hz.1.le (by linarith)
  have h2T : 2*T≤ Z^(B+1) := by
    calc
      _≤ Z*Z^B := mul_le_mul hZ hTZ hT.le hzpos.le
      _=_ := by rw [Real.rpow_add hzpos,Real.rpow_one]; ring
  have hp : Real.logb Z (2*T)≤ B+1 :=
    (Real.logb_le_iff_le_rpow hz.1 (by positivity)).mpr h2T
  have hradcap (l : FirstSourceLabel) (hl : l∈labels) :
      ((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^(Real.logb Z (2*T)) := by
    rw [Real.rpow_logb hzpos hz.1.ne' (by positivity : 0<2*T)]
    exact (hrad l hl).2
  have hc := hcount Z hz.1.le (Real.logb Z (2*T)) hp seed hs hs0 labels
    hsup heq hseed (fun l hl=>⟨(hnorm l hl).1.trans hpow,(hnorm l hl).2.trans hpow⟩) hradcap
  rw [Real.rpow_add hzpos,Real.rpow_logb hzpos hz.1.ne' (by positivity : 0<2*T)] at hc
  have hd := hz.2 Ds hDs hcap
  have hseedN := norm_pos seed hs0
  calc
    _≤∑_l∈labels,∑D∈Ds,factor/(T*(D.absNorm:ℝ)) := by
      apply Finset.sum_le_sum
      intro l hl
      apply Finset.sum_le_sum
      intro D hmem
      apply div_le_div_of_nonneg_left hf
        (mul_pos hT (norm_pos D (hDs D hmem).ne_zero))
      exact mul_le_mul_of_nonneg_right (hrad l hl).1 (Nat.cast_nonneg _)
    _=(labels.card:ℝ)*(factor/T)*(∑D∈Ds,1/(D.absNorm:ℝ)) := by
      simp only [div_eq_mul_inv,mul_inv_rev,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,one_mul]
      rw [←Finset.sum_mul]
      ring
    _≤(C*(2*T)*Z^ε/(seed.absNorm:ℝ))*(factor/T)*(D*Z^ε) := by
      have hc' : (labels.card:ℝ)≤ C*(2*T)*Z^ε/(seed.absNorm:ℝ) := by
        simpa only [mul_assoc] using hc
      have hfactor := div_nonneg hf hT.le
      have hsum : 0≤∑x∈Ds,1/(x.absNorm:ℝ) :=
        Finset.sum_nonneg (fun x _=>div_nonneg zero_le_one (Nat.cast_nonneg _))
      exact mul_le_mul (mul_le_mul_of_nonneg_right hc' hfactor) hd hsum
        (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hC.le (by positivity))
          (Real.rpow_nonneg hzpos.le _)) hseedN.le) hfactor)
    _=(2*C*D)*factor*Z^(2*ε)/(seed.absNorm:ℝ) := by
      rw [show Z^(2*ε)=Z^ε*Z^ε by rw [←Real.rpow_add hzpos]; congr 1; ring]
      field_simp [hT.ne',hseedN.ne']

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_reference_bound
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_paid

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_exceptional_radical_projector_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_paid

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalAggregate -/
