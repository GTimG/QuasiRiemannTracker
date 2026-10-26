/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual canonical initial and modified first-label exceptional caps. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalRadicalAggregateFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open ActualEisensteinCubic
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional ConcretePrimeRowBridge
open Cycle61InitialMass Record1252270103Second OAI.SevenEighths.Record1252270103Source
open QRH.Record1252270103Low InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized ForcedCost Pool Admission.FirstFamily
open High.GlobalPhysical SecondSectorDatum
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local notation "source"=>High.CoupledFirst.geometryFirstSource

open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
open CenteredMomentSecondHeightFamily

open Low.SelectedExceptionalNormalizedMasked
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondWindowBudget

theorem eventually_initial_family_aggregate {α:Type*}[Fintype α]
    (N:ℕ)(Bface lam cap:ℝ)(hB:Bface≤1)(hlam:1≤lam)(hcap:cap≤1)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)
    (hH:RayOrthogonality.globalUnits rayM≤H)
    (Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (η η₀:Character)(R₀:Ideal O)(hR:R₀≠0)
    (Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (amp ell mesh loss ξ reserve:ℝ)(depth:ℕ)
    (hmesh:0≤mesh)(hgap:mesh<ell)(hell:ell<amp)(hloss:0<loss)
    (hξ:0≤ξ)(hξ1:ξ≤1)(hreserve:0≤reserve)(hdepth:(2:ℝ)/ell≤depth)
    (W:𝓢(ℝ,ℂ))(decay:ℕ)(ε εL δ epsMass:ℝ)(hε:0<ε)(hεL:0<εL)(hδ:0<δ)(hεm:0<epsMass):
    ∃J:Finset α→ℕ,∃T:Finset α→Finset (ℕ×ℕ),(∀A,(0,0)∈T A) ∧
    ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
    ∃C₀ K₀ Cphys:Finset α→ℝ,∃A Hmass:ℝ,
      (∀S,0<C₀ S ∧ 0<K₀ S ∧ 0≤Cphys S) ∧ 0<A ∧ 0<Hmass ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{Label:Type*}[Fintype Label],
    ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
      (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
    Fintype.card α≤N→(∀i,0≤w i)→(∀i,w i≤mesh)→
    (globalFace Bface lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1→
    1≤Y₂→Y₂≤X₁→Y₂≤X₂→
    let s:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(reflected:Bool)(modifier:Tuple α→ℂ)(bin:ℤ×(Fin 5→ℤ))
      (column:Label→FirstColumnIndex (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)),
    ∀(V:Fin 4→ℝ→ℂ),
    ∀hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin) V,
    let hseed:∀l,Squarefree (column l).2.1.val:=fun l=>
      live_projector_squarefree s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin V (column l) (hLive l)
    let C:=fun l=>columnIdeal reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    ∀(alloc:∀l,actualAllocations s.pools (C l))(ht:Label→ℝ)(amplitude:Label→ℝ)
      (χ₀:Label→RayCharacter), (∀l,0≤amplitude l)→
    let m:=fixedBadMask*idealGenerator R₀
    let τ:=fun l=>columnCharacter reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let labels:=fun l=>firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let K:=fun l=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (labels l)
    let Tsec:=fun l=>firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (labels l)
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let f:=allocatedFamily s W (p.profile 0) (p.profile 1) Z R₀ C (fun l=>(column l).2.1.val)
      alloc τ ht P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
      K Tsec (fun _=>volume s) amplitude ξ
      (fun l=>first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve (zero_lt_one.trans hZ) (labels l)) χ₀ m
    ‖∑q,f.phase Q q*(f.block Q q).value W‖≤
      A*Hmass*Z^(epsMass+δ+4*εL)*
        ∑l,firstCost f N Q J T C₀ K₀ Cphys ε (fun l=>Y₂/((C l).absNorm:ℝ)) l/
          ((column l).2.1.val.absNorm:ℝ) := by
  obtain ⟨J,T,hT,hp⟩:=eventually_initial_family_radical (α:=α) N Bface lam cap hB hlam hcap
    rayM H hH Wslot hW hsW η η₀ R₀ hR Sbad hbad amp ell mesh loss ξ reserve depth
    hmesh hgap hell hloss hξ hξ1 hreserve hdepth W decay ε εL (499/1000)
    hε hεL (by norm_num) (by norm_num)
  obtain ⟨A,Hmass,hA,hHmass,hpayment⟩:=eventually_family_payment N 2 3 1 4 δ epsMass
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ hεm
  refine ⟨J,T,hT,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,K₀,Cphys,hpos,hp⟩:=hp Q hQ0 hQ hQ72
  refine ⟨C₀,K₀,Cphys,A,Hmass,hpos,hA,hHmass,?_⟩
  filter_upwards [hp,hpayment,eventually_initial_caps N Bface lam cap hB hlam hcap,
    eventually_ge_atTop ((2:ℝ)^(2*N)),
    eventually_initial_first_family_polynomialCaps N Bface lam cap hB hlam hcap
      rayM H hH Wslot hW hsW η η₀ R₀ hR Sbad hbad amp ell mesh loss ξ reserve depth
      hmesh hgap hell hloss hξ hξ1 hreserve hdepth W] with Z hp hpayment hbase hNpow hcaps
  refine ⟨hp.1,?_⟩
  intro hZ Label instLabel θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hN hw hwm hadm hy₂ hl₁ hl₂ s reflected modifier bin column V hLive hseed C alloc ht amplitude χ₀ ha m τ labels K Tsec P f
  have hb:=hbase.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hN hw hadm hy₂ hl₁ hl₂
  have hc:=hcaps.2 hZ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hN hw hwm hadm hy₂ hl₁ hl₂ reflected modifier bin column V hLive alloc ht amplitude χ₀ m Q
  have hn:=hp.2 hZ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hN hw hwm hadm hy₂ hl₁ hl₂ reflected modifier bin column V hLive alloc ht amplitude χ₀
  apply hn.trans
  apply hpayment.2 (fun l=>liveIndices (alloc l).val) W f Q J T C₀ K₀ Cphys ε εL
    (fun l=>Y₂/((C l).absNorm:ℝ)) decay hN hεL.le (fun A=>(hpos A).2.1.le)
    (fun A=>(hpos A).2.2) ha (fun _=>volume_pos s)
  · intro l
    norm_num [f,allocatedFamily,child,s,initialInput]
  · intro l x hx
    exact (p.support 0 hx).1
  · intro l x hx
    exact (p.support 1 hx).1
  · intro l
    exact (child_source_radius_le s (C l) R₀ (alloc l) (τ l) (ht l)
      (fun _=>by norm_num [s,initialInput]) (fun i=>Real.one_le_rpow hZ.le (hw i))
      (by norm_num [s,initialInput]) (by norm_num [s,initialInput])).trans hb.2.1
  · intro l
    change 0≤frequencyRadius (Tsec l) Z ξ
    unfold frequencyRadius
    apply mul_nonneg _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    dsimp only [Tsec,firstMainFourierScale]
    exact div_nonneg (sq_nonneg _) (first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) (labels l)).le
  · intro l
    change frequencyRadius (Tsec l) Z ξ≤1*Z^(3:ℝ)
    rw [one_mul]
    exact modified_main_frequency_cap reflected s modifier R₀ 1 Z Z ξ (3*amp) reserve N
      (zero_lt_one.trans hZ) hZ hξ hξ1 (by have := (hmesh.trans_lt hgap).trans hell;linarith)
      hreserve le_rfl hNpow bin (column l)
  · intro l
    exact (hseed l).ne_zero
  · intro q
    exact (hc q).residual_cap

open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentCommonExceptionalCost ExceptionalRadical

lemma child_frozenProfile {ι:Type*}[Fintype ι](s:Input ι)(X R:Ideal O)
    (B:actualAllocations s.pools X)(τ:Character)(t:ℝ):
    frozenProfile (child s X R B τ t)≤frozenProfile s:=by
  have hp:(∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i:=by
    rw [Finset.prod_coe_sort]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hc:Fintype.card (liveIndices B.val)≤Fintype.card ι:=by
    rw [Fintype.card_coe];exact Finset.card_le_univ _
  unfold frozenProfile
  change (∏i:liveIndices B.val,s.M i.val)*(max 1 s.upper)^Fintype.card (liveIndices B.val)≤_
  exact mul_le_mul hp (pow_le_pow_right₀ (le_max_left _ _) hc)
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (Finset.prod_nonneg fun i _=>(s.M_ge_one i).trans' zero_le_one)

/-- One finite control and degree dominate every original surviving subset.
The parent slot costs stay explicit here and are bounded uniformly on the
canonical initial input by initial_cost_bounds and the constant slot bound. -/
theorem finite_profile_height_envelope {α:Type*}[Fintype α]
    (J:Finset α→ℕ)(T:Finset α→Finset (ℕ×ℕ))(C₀ K₀ Cphys:Finset α→ℝ)
    (hC:∀A,0≤C₀ A)(hK:∀A,0≤K₀ A)(hphys:∀A,0≤Cphys A)(Q:Ideal O):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(s:Input α)(X R:Ideal O)(B:actualAllocations s.pools X)(τ:Character)(t:ℝ)
      (p:Profiles (1/4) (9/4))(Z ε raw:ℝ),0<Z→
    let sc:=child s X R B τ t
    let A:=liveIndices B.val
    Cphys A*(frozenProfile sc)^2*
      centeredProfileFactor sc (T A) (p.profile 0) (p.profile 1) ballProfile Q
        Z ε (499/1000) raw 2 (C₀ A) (K₀ A)*
      (heightEnvelope t^(J A)*profileMoment (J A))^2≤
      C*(frozenProfile s)^2*forcedProfileCost s*(slotControl s.toData)^2*
        (p.control S)^2*(Z^ε*(max 1 raw)^(-(499/1000:ℝ)))^2*(1+‖t‖)^degree:=by
  let S:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let D:ℕ:=Finset.univ.sup J
  let E:Finset α→ℝ:=fun A=>Cphys A*K₀ A*
    (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (2:ℝ)^(1/6:ℝ)*(C₀ A)^2*SchwartzMap.seminorm ℝ 0 0 ballProfile*
    ((1+2*Real.pi)^(2*J A)*profileMoment (J A))^2
  have hE:∀A,0≤E A:=by
    intro A
    have h1:=hphys A;have h2:=hK A;have h3:0≤SchwartzMap.seminorm ℝ 0 0 ballProfile:=apply_nonneg _ _
    dsimp [E];positivity
  let C:=1+∑A,E A
  have hCpos:0<C:=by
    have hh:0≤∑A,E A:=Finset.sum_nonneg (fun A _=>hE A)
    dsimp [C];linarith
  refine ⟨2*D,S,C,hCpos,?_⟩
  intro s X R B τ t p Z ε raw hZ sc A
  have hAs:T A⊆S:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨A,Finset.mem_univ _,hx⟩
  have hAD:J A≤D:=Finset.le_sup (Finset.mem_univ A)
  have hEC:E A≤C:=by
    have hh:=Finset.single_le_sum (fun A _=>hE A) (Finset.mem_univ A)
    dsimp [C];linarith
  have hheight:=CenteredMomentEnergyFirstPhysicalNormalization.heightEnvelope_pow_le (J A) t
  have hheight':(heightEnvelope t^(J A)*profileMoment (J A))^2≤
      ((1+2*Real.pi)^(2*J A)*profileMoment (J A))^2*(1+‖t‖)^(2*D):=by
    have hm:=mul_le_mul_of_nonneg_right hheight (profileMoment_nonneg (J A))
    have hs:=pow_le_pow_left₀ (mul_nonneg (pow_nonneg (heightEnvelope_pos t).le (J A)) (profileMoment_nonneg (J A))) hm 2
    apply hs.trans
    calc
      _=((1+2*Real.pi)^(2*J A)*profileMoment (J A))^2*(1+‖t‖)^(2*J A):=by rw [pow_mul];ring
      _≤_:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.mul_le_mul_left 2 hAD)) (sq_nonneg _)
  have hfp:=child_frozenProfile s X R B τ t
  have hforced:=child_forcedProfileCost s X R B τ t
  have hslot:=ForcedCost.child_slotControl s X R B τ t
  have hcontrol:=CenteredMomentEnergyBandMonotonicity.profile_control_mono p hAs
  have hseminorm:0≤SchwartzMap.seminorm ℝ 0 0 ballProfile:=apply_nonneg _ _
  have hf0:=frozenProfile_nonneg sc
  have hfo0:=forcedProfileCost_nonneg sc
  have hsl0:=slotControl_nonneg sc.toData
  have hpc:=p.control_nonneg (T A)
  have hpcS:=p.control_nonneg S
  have hca:=hC A
  have hka:=hK A
  have hpa:=hphys A
  have hparent:=forcedProfileCost_nonneg s
  have hparentSlot:=slotControl_nonneg s.toData
  have hpiece:Cphys A*(frozenProfile sc)^2*
      centeredProfileFactor sc (T A) (p.profile 0) (p.profile 1) ballProfile Q Z ε (499/1000) raw 2 (C₀ A) (K₀ A)*
      (heightEnvelope t^(J A)*profileMoment (J A))^2≤
      E A*(frozenProfile s)^2*forcedProfileCost s*(slotControl s.toData)^2*
        (p.control S)^2*(Z^ε*(max 1 raw)^(-(499/1000:ℝ)))^2*(1+‖t‖)^(2*D):=by
    unfold centeredProfileFactor
    change _≤_
    calc
      _≤Cphys A*(frozenProfile s)^2*
          (K₀ A*forcedProfileCost s*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
          (2:ℝ)^(1/6:ℝ)*(C₀ A*(p.control S)*Z^ε*(max 1 raw)^(-(499/1000:ℝ))*slotControl s.toData)^2*
          SchwartzMap.seminorm ℝ 0 0 ballProfile)*
          (((1+2*Real.pi)^(2*J A)*profileMoment (J A))^2*(1+‖t‖)^(2*D)):=by
        change Cphys A*frozenProfile sc^2*
          (K₀ A*forcedProfileCost sc*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
          (2:ℝ)^(1/6:ℝ)*(C₀ A*p.control (T A)*Z^ε*(max 1 raw)^(-(499/1000:ℝ))*slotControl sc.toData)^2*
          SchwartzMap.seminorm ℝ 0 0 ballProfile)*
          (heightEnvelope t^(J A)*profileMoment (J A))^2≤_
        gcongr
      _=_:=by dsimp [E];ring!
  exact hpiece.trans (by gcongr)


/-- On canonical initial inputs, the finite envelope has one fixed constant
before Z, the user profiles, every first label and its actual Mellin height. -/
theorem initial_profile_height_envelope {α:Type*}[Fintype α]
    (N:ℕ)(hN:Fintype.card α≤N)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
    (Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (J:Finset α→ℕ)(T:Finset α→Finset (ℕ×ℕ))(C₀ K₀ Cphys:Finset α→ℝ)
    (hC:∀A,0≤C₀ A)(hK:∀A,0≤K₀ A)(hphys:∀A,0≤Cphys A)(Q:Ideal O):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(Z:ℝ)(hZ:0<Z)(η η₀:Character)(R₀:Ideal O)
      (θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t:ℝ)(p:Profiles (1/4) (9/4))
      (X₁ X₂ Y₁ Y₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
    let s:=initialInput rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v t p (by norm_num)
      X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(X R:Ideal O)(B:actualAllocations s.pools X)(τ:Character)(ht ε raw:ℝ),
    let sc:=child s X R B τ ht
    let A:=liveIndices B.val
    Cphys A*(frozenProfile sc)^2*
      centeredProfileFactor sc (T A) (p.profile 0) (p.profile 1) ballProfile Q
        Z ε (499/1000) raw 2 (C₀ A) (K₀ A)*
      (heightEnvelope ht^(J A)*profileMoment (J A))^2≤
      C*(p.control S)^2*(Z^ε*(max 1 raw)^(-(499/1000:ℝ)))^2*(1+‖ht‖)^degree:=by
  obtain ⟨degree,S,C,hCpos,hbound⟩:=finite_profile_height_envelope J T C₀ K₀ Cphys hC hK hphys Q
  let L:=initialSlotBound Wslot hW hsW
  let F:=L^N*(2:ℝ)^N
  let P:=(L^N)^2*(2:ℝ)^N
  let V:=L^N*(max 1 (256*L))^N
  have hL:0<L:=zero_lt_one.trans_le (initialSlotBound_ge_one Wslot hW hsW)
  have hF:0<F:=by dsimp [F];positivity
  have hP:0<P:=by dsimp [P];positivity
  have hV:0<V:=by dsimp [V];positivity
  refine ⟨degree,S,C*F^2*P*V^2,by positivity,?_⟩
  intro Z hZ η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod s X R B τ ht ε raw sc A
  have hcost:=initial_cost_bounds rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod N hN
  have hf:frozenProfile s≤F:=by
    change (∏_i:α,L)*(max 1 (2:ℝ))^Fintype.card α≤_
    simp only [Finset.prod_const,Finset.card_univ,max_eq_right (by norm_num : (1:ℝ)≤2)]
    exact mul_le_mul (pow_le_pow_right₀ (initialSlotBound_ge_one Wslot hW hsW) hN)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN) (by positivity) (by positivity)
  apply (hbound s X R B τ ht p Z ε raw hZ).trans
  have hfp:=frozenProfile_nonneg s
  have hpc:=forcedProfileCost_nonneg s
  have hsc:=slotControl_nonneg s.toData
  have hp0:=p.control_nonneg S
  have hpCap:forcedProfileCost s≤P:=hcost.2
  have hsCap:slotControl s.toData≤V:=hcost.1
  gcongr

/-- Uniform first-label-only exceptional family bound, before all moving data. -/
theorem eventually_initial_family_uniform {α:Type*}[Fintype α]
    (N:ℕ)(hN:Fintype.card α≤N)(Bface lam cap:ℝ)(hB:Bface≤1)(hlam:1≤lam)(hcap:cap≤1)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)
    (hH:RayOrthogonality.globalUnits rayM≤H)
    (Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (η η₀:Character)(R₀:Ideal O)(hR:R₀≠0)
    (Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (amp ell mesh loss ξ reserve:ℝ)(depth:ℕ)
    (hmesh:0≤mesh)(hgap:mesh<ell)(hell:ell<amp)(hloss:0<loss)
    (hξ:0≤ξ)(hξ1:ξ≤1)(hreserve:0≤reserve)(hdepth:(2:ℝ)/ell≤depth)
    (W:𝓢(ℝ,ℂ))(decay:ℕ)(ε εL δ epsMass:ℝ)(hε:0<ε)(hεL:0<εL)(hδ:0<δ)(hεm:0<epsMass):
    ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃Ctotal:ℝ,0<Ctotal ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{Label:Type*}[Fintype Label],
    ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
      (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
    (∀i,0≤w i)→(∀i,w i≤mesh)→
    (globalFace Bface lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1→
    1≤Y₂→Y₂≤X₁→Y₂≤X₂→
    let s:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(reflected:Bool)(modifier:Tuple α→ℂ)(bin:ℤ×(Fin 5→ℤ))
      (column:Label→FirstColumnIndex (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)),
    ∀(V:Fin 4→ℝ→ℂ),
    ∀hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin) V,
    let hseed:∀l,Squarefree (column l).2.1.val:=fun l=>
      live_projector_squarefree s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin V (column l) (hLive l)
    let C:=fun l=>columnIdeal reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    ∀(alloc:∀l,actualAllocations s.pools (C l))(ht:Label→ℝ)(amplitude:Label→ℝ)
      (χ₀:Label→RayCharacter), (∀l,0≤amplitude l)→
    let m:=fixedBadMask*idealGenerator R₀
    let τ:=fun l=>columnCharacter reflected s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let labels:=fun l=>firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin (column l)
    let K:=fun l=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (labels l)
    let Tsec:=fun l=>firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (labels l)
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let f:=allocatedFamily s W (p.profile 0) (p.profile 1) Z R₀ C (fun l=>(column l).2.1.val)
      alloc τ ht P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
      K Tsec (fun _=>volume s) amplitude ξ
      (fun l=>first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve (zero_lt_one.trans hZ) (labels l)) χ₀ m
    ‖∑q,f.phase Q q*(f.block Q q).value W‖≤
      Ctotal*(p.control S)^2*Z^(epsMass+δ+4*εL+2*ε)*
        ∑l,(amplitude l/volume s)*(K l/lowerFactor N 1 (1/4))*volume (f.input l)*
          (4*frequencyRadius (Tsec l) Z ξ)^(1/6:ℝ)*
          (max 1 (Y₂/((C l).absNorm:ℝ)))^(-2*(499/1000:ℝ))*(1+‖ht l‖)^degree/
          ((column l).2.1.val.absNorm:ℝ) := by
  obtain ⟨J,T,hT,hfull⟩:=eventually_initial_family_aggregate (α:=α) N Bface lam cap hB hlam hcap
    rayM H hH Wslot hW hsW η η₀ R₀ hR Sbad hbad amp ell mesh loss ξ reserve depth
    hmesh hgap hell hloss hξ hξ1 hreserve hdepth W decay ε εL δ epsMass hε hεL hδ hεm
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,K₀,Cphys,A,Hmass,hpos,hA,hHm,hfull⟩:=hfull Q hQ0 hQ hQ72
  obtain ⟨degree,S,Cenv,hCe,henv⟩:=initial_profile_height_envelope (α:=α) N hN rayM H hH Wslot hW hsW
    J T C₀ K₀ Cphys (fun A=>(hpos A).1.le) (fun A=>(hpos A).2.1.le) (fun A=>(hpos A).2.2) Q
  refine ⟨degree,S,A*Hmass*Cenv,by positivity,?_⟩
  filter_upwards [hfull] with Z hfull
  refine ⟨hfull.1,?_⟩
  intro hZ Label instLabel θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hw hwm hadm hy₂ hl₁ hl₂ s reflected modifier bin column V hLive hseed C alloc ht amplitude χ₀ ha m τ labels K Tsec P f
  have hZ0:=zero_lt_one.trans hZ
  have hn:=hfull.2 hZ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hN
    hw hwm hadm hy₂ hl₁ hl₂ reflected modifier bin column V hLive alloc ht amplitude χ₀ ha
  let price:Label→ℝ:=fun l=>(amplitude l/volume s)*(K l/lowerFactor N 1 (1/4))*volume (f.input l)*
    (4*frequencyRadius (Tsec l) Z ξ)^(1/6:ℝ)*
    (max 1 (Y₂/((C l).absNorm:ℝ)))^(-2*(499/1000:ℝ))*(1+‖ht l‖)^degree/
    ((column l).2.1.val.absNorm:ℝ)
  have hp (l:Label):firstCost f N Q J T C₀ K₀ Cphys ε (fun l=>Y₂/((C l).absNorm:ℝ)) l/
      ((column l).2.1.val.absNorm:ℝ)≤Cenv*(p.control S)^2*Z^(2*ε)*price l:=by
    have hh:=henv Z hZ0 η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
      (C l) R₀ (alloc l) (τ l) (ht l) ε (Y₂/((C l).absNorm:ℝ))
    have hrad:0≤frequencyRadius (Tsec l) Z ξ:=by
      unfold frequencyRadius
      apply mul_nonneg _ (Real.rpow_nonneg hZ0.le _)
      dsimp only [Tsec,firstMainFourierScale]
      exact div_nonneg (sq_nonneg _) (first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve hZ0 (labels l)).le
    have hKp:0<K l:=first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve hZ0 (labels l)
    have hl:=lowerFactor_pos N (1:ℝ) (1/4) (by norm_num) (by norm_num)
    have hv:=volume_pos s
    have hvc:=volume_pos (f.input l)
    have hap:=ha l
    have hmul:0≤(amplitude l/volume s)*(K l/lowerFactor N 1 (1/4))*volume (f.input l)*
        (4*frequencyRadius (Tsec l) Z ξ)^(1/6:ℝ)/((column l).2.1.val.absNorm:ℝ):=by positivity
    have hpaid:=mul_le_mul_of_nonneg_left hh hmul
    have hex:(Z^ε*(max 1 (Y₂/((C l).absNorm:ℝ)))^(-(499/1000:ℝ)))^2=
        Z^(2*ε)*(max 1 (Y₂/((C l).absNorm:ℝ)))^(-2*(499/1000:ℝ)):=by
      rw [mul_pow,pow_two,←Real.rpow_add hZ0,pow_two,
        ←Real.rpow_add (zero_lt_one.trans_le (le_max_left (1:ℝ) _))]
      congr 1 <;> ring
    rw [hex] at hpaid
    convert hpaid using 1 <;> dsimp only [firstCost,price,f,allocatedFamily] <;> ring!
  apply hn.trans
  calc
    _≤A*Hmass*Z^(epsMass+δ+4*εL)*∑l,Cenv*(p.control S)^2*Z^(2*ε)*price l:=by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _=>hp l)
      positivity
    _=_:=by
      rw [←Finset.mul_sum,show Z^(epsMass+δ+4*εL+2*ε)=Z^(epsMass+δ+4*εL)*Z^(2*ε) by
        rw [Real.rpow_add hZ0]]
      ring

end
end QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.eventually_initial_family_aggregate

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.finite_profile_height_envelope

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.initial_profile_height_envelope

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.eventually_initial_family_uniform
