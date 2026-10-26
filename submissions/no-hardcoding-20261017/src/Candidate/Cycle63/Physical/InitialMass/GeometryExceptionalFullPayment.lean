import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalClosure
import Candidate.Cycle63.Physical.InitialMass.GeometryAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryAllocationMass

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentFirstCanonicalFamily CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondHeightFamily CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstMixedRoot CenteredMomentFirstExceptionalChildPaid
open CenteredMomentSecondExceptionalFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocationCost CenteredMomentSourceMass CenteredMomentLogDyadic
open CenteredMomentSecondEnergySplit CenteredMomentAmplificationErrorEnergy
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildSourceCaps
open CenteredMomentPrimeElements
open CenteredMomentPrimePool
open CenteredMomentFirstPhysicalSource CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance fullExceptionalSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Every original allocation is summed, and cancelled frozen coefficients
contribute zero before the whole exceptional part energy is normalized. -/
def geometryExceptionalMainRowMass (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (M Z ξ sigma reserve t : ℝ) (hZ : 1<Z)
    (N : ℕ) (b : ℝ) (bin : ℤ×(Fin 5→ℤ)) (Qfix : Ideal O)
    (χ₀ : RayCharacter) (m : O)
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin)) : ℝ :=
  let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let l := geometryFirstLabel s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  ∑B : actualAllocations s.pools I,
    if frozenCoefficient B.val I R s.ν s.W s.P≠0 then
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
        (Real.logb Z (geometryExceptionalVolume s))
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
        (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j B*
      (‖partEnergy true τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset (child s I R B τ t).pools))
        (coefficient (child s I R B τ t) (R*I) j.2.1.val) W
        (firstMainRadius reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve l)
        (firstMainFourierScale reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve b N l)
        Z ξ (sourceRadius (child s I R B τ t))‖/geometryExceptionalVolume (child s I R B τ t))
    else 0

private theorem full_error_reference_orientation (reflected : Bool)
    (τ : Character) (l : FirstSourceLabel) (K X Z ξ sigma reserve r : ℝ) (p : O) (k : ℕ) :
    geometryExceptionalErrorReference τ
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val})
      K X Z sigma (frequencyLoss Z 32 ξ) reserve r p k=
    let I := if reflected then l.1.2 else l.1.1
    let H := if reflected then l.1.1 else l.1.2
    (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6))*
      localErrorCost p (k-1)*(X/(I.absNorm:ℝ)/(normValue p)^k)^(1/3:ℝ)*
      (errorCommonRadius Z (Real.logb Z (H.absNorm:ℝ))
        (nominalLog l.1.1 l.1.2
          (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val}) K X Z)
        (Real.logb Z (I.absNorm:ℝ)) sigma (frequencyLoss Z 32 ξ) reserve p k)^(5/6:ℝ)*
      Z^(-2*max r 0/3) := by
  cases reflected
  · simp only [geometryExceptionalErrorReference,Bool.false_eq_true,↓reduceIte]
    ring
  · simp only [geometryExceptionalErrorReference,↓reduceIte]
    rw [nominalLog_swap l.1.1 l.1.2,active_span_swap l.1.1 l.1.2]
    ring

omit [DecidableEq ι] in
theorem actual_geometry_full_error_reference
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (M Z ξ amp reserve t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    (Mprime : Ideal O) [NeZero Mprime] (Hprime : Subgroup (O⧸Mprime)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈elementPool (primePool Mprime Hprime Sbad (1/2) 1 (Z^amp)))
    (i : Fin 3)
    (Bp : actualAllocations (child s
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) R B
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) t).pools
      ((Ideal.span {p})^(errorIndex i+1)))
    (υ : Character) (v plainLoss : ℝ)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₂) :
    let src := geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    geometryExceptionalErrorReference τ I (if reflected then src.C else src.D)
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      (Z^M) (geometryExceptionalVolume s) Z (3*amp) (frequencyLoss Z 32 ξ) reserve
      (inputCap Z (twiceChild s I R B τ t (Ideal.span {p}) (errorIndex i+1) Bp υ v))
      p (errorIndex i+1)≤
      Z^(Real.logb Z (geometryExceptionalVolume s)-
        (M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
  have hk : errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7 := by
    fin_cases i <;> norm_num [errorIndex]
  have hp' : p∈elementPool (primePool Mprime Hprime Sbad (1/2) 1 (Z^((3*amp)/3))) := by
    simpa only [show (3*amp)/3=amp by ring] using hp
  have hklog : Real.logb Z (Z^M)=M := Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hm := actual_geometry_column_modulus reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  cases reflected
  · have hh := actual_error_twice_exceptional_reference s.η
      (geometryColumnCharacter false s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
      src.C src.D
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      src.hC src.hD src.sameSupport src.inactive rfl s R B (Z^M) Z (3*amp)
      (frequencyLoss Z 32 ξ) reserve t plainLoss
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm
      Mprime Hprime Sbad hbad p hp' (errorIndex i+1) hk Bp υ v
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    exact hh
  · have hm' : (geometryColumnCharacter true s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus=
        s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
          Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.D src.C=>q.val)
            (swapSubset src.C src.D src.inactive)*activeConductor src.D src.C} := by
      rw [swapped_modulus_factor]
      exact hm
    have hh := actual_error_twice_exceptional_reference s.η
      (geometryColumnCharacter true s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
      src.D src.C
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      src.hD src.hC src.sameSupport.symm (swapSubset src.C src.D src.inactive)
      (by rw [swapSubset_generator]) s R B (Z^M) Z (3*amp)
      (frequencyLoss Z 32 ξ) reserve t plainLoss
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm'
      Mprime Hprime Sbad hbad p hp' (errorIndex i+1) hk Bp υ v
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    exact hh

private theorem full_main_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D Control bro q volumeRoot kr mr Rpow : ℝ)
    (hpaid : E≤S*F*q*A*(Ck*Pz*mr*kr*lower/D)*(Cprof*Control*bro*volumeRoot))
    (hside : S≤Shell) (hlower : lower≤L) (href : q*volumeRoot*kr*mr≤Rpow)
    (hS : 0≤S) (hShell : 0≤Shell) (hF : 0≤F) (hA : 0≤A)
    (hP : 0≤Pz) (hl : 0≤lower) (hL : 0≤L) (hD : 0≤D)
    (hc : 0≤Control) (hb : 0≤bro) (hq : 0≤q) (hi : 0≤volumeRoot)
    (hk : 0≤kr) (hm : 0≤mr) :
    E≤Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*Control*bro*Rpow := by
  let rest := S*F*A*Pz*(lower/D)*Control*bro*(q*volumeRoot*kr*mr)
  have hrest : 0≤rest := by dsimp only [rest]; positivity
  calc
    E≤(Ck*Cprof)*rest := by convert hpaid using 1; dsimp only [rest]; ring
    _≤max 1 (Ck*Cprof)*rest := mul_le_mul_of_nonneg_right (le_max_right _ _) hrest
    _≤max 1 (Ck*Cprof)*(Shell*F*A*Pz*(L/D)*Control*bro*Rpow) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_left _ _))
      dsimp only [rest]
      gcongr
    _=_ := by ring

private theorem full_main_paid_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D c height mass bro q root kr m₁ m₂ Rpow : ℝ)
    (hpaid : E≤(S*F*q)*A*(Ck*Pz*m₁*m₂*kr*lower/D)*
      ((Cprof*c*height*mass)*(bro*root)))
    (hside : S≤Shell) (hlower : lower≤L) (href : q*root*kr*m₁*m₂≤Rpow)
    (hS : 0≤S) (hShell : 0≤Shell) (hF : 0≤F) (hA : 0≤A)
    (hP : 0≤Pz) (hl : 0≤lower) (hL : 0≤L) (hD : 0≤D)
    (hc : 0≤c*height*mass) (hb : 0≤bro) (hq : 0≤q) (hi : 0≤root)
    (hk : 0≤kr) (hm : 0≤m₁*m₂) :
    E≤Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*(c*height*mass)*bro*Rpow := by
  exact full_main_fold_algebra E S Shell F A Ck Cprof Pz lower L D
    (c*height*mass) bro q root kr (m₁*m₂) Rpow
    (by convert hpaid using 1; ring) hside hlower
    (by convert href using 1; ring) hS hShell hF hA hP hl hL hD hc hb hq hi hk hm

set_option linter.defProp false in
/-- The complete supported main family derives its allocation costs from
the saved whole exceptional estimate. The original projector and radical
are paid jointly before all four dyads and both rays are counted. -/
def actual_geometry_main_exceptional_full
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0<slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :=
  let closed := actual_geometry_main_exceptional_closed wlo whi hwlo hwhi lo hi W
    ε δ θ hε hδ hθ η N b bs hb hbs
  let J := closed.1
  let Sp := closed.2.1
  let Ck := closed.2.2.1
  let halloc := actualAllocations_uniform_small_power (N+2) (εalloc/2) (half_pos hea)
  let Da := Classical.choose halloc
  let hDa := Classical.choose_spec halloc
  let hcolumns := eventual_actual_zero_column_payment (ι:=ι) 2 0 3
    (((N:ℝ)+2)*3) ξ εcount (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hξ hec
  let Cd := Classical.choose hcolumns
  let hCd := Classical.choose_spec hcolumns
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let saved := closed.2.2.2 Qfix hQ hQt hQ72
    let Kfix := saved.1
    (Kfix,Cd,Da,PLift.up (And.intro saved.2.down.1 (And.intro hCd.1 (And.intro hDa.1
      (Filter.Eventually.mono (saved.2.down.2.and hCd.2)
        (fun Z hz=>And.intro hz.1.1
          (fun (hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤N) (hend : Endpoints b bs bs s)
            (hlower : slotlo≤s.lower) (hsP : ∀i,1≤s.P i)
            (p : Profiles wlo whi) (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤Z^(2:ℝ)) (hsourcepos : 0<sourceRadius s)
            (hsource : sourceRadius s≤Z^(3:ℝ))
            (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤Z) (M sigma reserve t plainLoss : ℝ)
            (hM : 0≤M) (hKM : Z^M≤Z) (hsigma : 0≤sigma) (hreserve : 0≤reserve)
            (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₁)
            (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₂)
            (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₁)
            (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₂)
            (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
            (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
            (reflected : Bool) (bin : ℤ×(Fin 5→ℤ))
            (χ₀ : RayCharacter) (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
          let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
            (fun _=>logAnnulus)
          by
          have hZpos : 0<Z := zero_lt_one.trans hZ
          let Hshell := Z^((bin.2 1:ℝ)*Real.logb Z 2)
          have hH : 0<Hshell := Real.rpow_pos_of_pos hZpos _
          have hphysical (j : rows) : Hshell≤
              ((geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1).D.absNorm:ℝ) ∧
              ((geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1).D.absNorm:ℝ)≤2*Hshell := by
            have hr := actual_geometry_fiber_range s R seed (Z^M) Z ξ 3 hZ hs hz₁ hz₂
              hsource bin j.val.1 1
            have hn := actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂
              hsource j.val.1.val 1
            have hl := Real.rpow_le_rpow_of_exponent_le hZ.le hr.1
            have hu := Real.rpow_le_rpow_of_exponent_le hZ.le hr.2.le
            rw [geometryExponents,Real.rpow_logb hZpos hZ.ne' (zero_lt_one.trans_le hn.1)] at hl hu
            have he : Z^(((bin.2 1:ℝ)+1)*Real.logb Z 2)=2*Hshell := by
              rw [add_mul,one_mul,Real.rpow_add hZpos,
                Real.rpow_logb hZpos hZ.ne' (by norm_num : (0:ℝ)<2)]
              exact mul_comm _ _
            exact ⟨hl,hu.trans_eq he⟩
          have hfixed : 0<fixedPresentationCost := fixedPresentationCost_pos
          let Control := p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6
          let Shell := if reflected then 1/Hshell
            else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
          let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
            N b J Qfix Kfix)
          let factor := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
            coef*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Da^2
          let exponent := 2*ε+2*δ+2*41*θ+sigma/3+
            Real.logb Z (geometryExceptionalVolume s)-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
            4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
          let cost := fun j : rows=>geometryExceptionalMainRowMass reflected s R seed W
            M Z ξ sigma reserve t hZ N b bin Qfix χ₀ m j.val
          have hShell : 0≤Shell := by dsimp only [Shell]; split_ifs <;> positivity
          have hLower : 0≤geometryExceptionalLowerConstant N slotlo wlo :=
            Real.rpow_nonneg (by positivity) _
          have hControl : 0≤Control := by dsimp only [Control]; positivity
          have hfactor : 0≤factor := by dsimp only [factor,coef]; positivity
          have hc : ∀j : rows,0≤cost j := by
            intro j
            unfold cost geometryExceptionalMainRowMass
            apply Finset.sum_nonneg
            intro B _
            split_ifs
            · exact mul_nonneg (geometryAllocationWeight_nonneg ..)
                (div_nonneg (norm_nonneg _) (CenteredMomentExceptionalAmplitudePair.volume_pos _).le)
            · exact le_rfl
          have hcost : ∀j : rows,cost j≤factor*
              Z^(exponent-geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)/
                (j.val.2.1.val.absNorm:ℝ) := by
            intro j
            let l := geometryFirstLabel s R seed (Z^M) Z ξ hK bin j.val
            let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.val
            let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin j.val
            let src := geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1
            let X := geometryExceptionalVolume s
            let Pz := Z^(2*ε+2*δ+2*41*θ+sigma/3)
            let Rpow := Z^(Real.logb Z X-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
              4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3)
            let rad := ((commonRadical src.C src.D).absNorm:ℝ)
            let Dproj := (j.val.2.1.val.absNorm:ℝ)
            let G := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
              coef*Pz*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Rpow
            have hG : 0≤G := by dsimp only [G,coef,Pz,Rpow]; positivity
            have hrad : 0<rad := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero _ _)
            have hDproj : 0<Dproj := CenteredMomentFirstScale.norm_pos _
              (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
                (fun _=>logAnnulus) j.val j.property).ne_zero
            have hpoint (B : actualAllocations s.pools I)
                (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0) :
                geometryAllocationWeight reflected s R seed (Z^M) Z ξ M (Real.logb Z X) hK bin
                  (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j.val B*
                (‖partEnergy true τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset (child s I R B τ t).pools))
                  (coefficient (child s I R B τ t) (R*I) j.val.2.1.val) W
                  (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)
                  (firstMainFourierScale reflected (Z^M) X Z ξ sigma reserve b N l)
                  Z ξ (sourceRadius (child s I R B τ t))‖/geometryExceptionalVolume (child s I R B τ t))≤
                ((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
              let u := child s I R B τ t
              have hXpos : 0<X := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
              have hIpos : 0<(I.absNorm:ℝ) :=
                CenteredMomentFirstScale.norm_pos _ (allocation_ne s I B)
              have hτpos : 0<(τ.modulus.absNorm:ℝ) :=
                CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
              have hbase : 0≤(∏i,u.lo i)*wlo*wlo := mul_nonneg
                (mul_nonneg (Finset.prod_nonneg (fun i _=>(u.lo_pos i).le)) hwlo.le) hwlo.le
              let den := (τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
                Z^(max (3*Real.logb Z (I.absNorm:ℝ)-
                  5*Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
                  Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6)
              let qfac := (X/(I.absNorm:ℝ))/den
              let mr := Z^(-sigma/3)*Z^(-2*max (inputCap Z u) 0/3)
              let kr := (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)^(5/6:ℝ)
              let lower := ((∏i,u.lo i)*wlo*wlo)^(-2/3:ℝ)
              let side := if reflected then 1/(src.D.absNorm:ℝ)
                else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)
              have hpayed := hz.1.2 hZ s hlo hhi hη hcard hend hsP p hW₁ hW₂ R seed hR hs
                hz₁ hz₂ hV hsource hRN M ξ sigma reserve t hKM hξ hξ₁ hsigma hreserve
                a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected bin (⟨j,B⟩ : GeometryLowFirstIndex
                  reflected s R seed (Z^M) Z ξ hK bin) hne χ₀ m hm hml hm2
              have hlogs :
                  (if reflected then max (3*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 1-
                    5*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 0-
                    geometryExponents s R seed (Z^M) Z ξ j.val.1.val 3) 0/6 else
                    max (3*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 0-
                    5*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 1-
                    geometryExponents s R seed (Z^M) Z ξ j.val.1.val 3) 0/6)=
                  max (3*Real.logb Z (I.absNorm:ℝ)-
                    5*Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
                    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6 := by
                cases reflected <;> rfl
              dsimp only at hpayed
              rw [hlogs] at hpayed
              have href := actual_geometry_main_exceptional_radius_bound reflected s R seed
                M Z ξ sigma reserve t hZ bin j.val B plainLoss hX₁ hX₂ hY₁ hY₂
              have hlow := actual_geometry_exceptional_lower_factor u N slotlo wlo
                ((live_card_le B.val).trans hcard) hslot hlower hwlo
              have hside : side≤Shell := by
                dsimp only [side,Shell]
                split_ifs
                · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical j).1
                · exact mul_le_mul_of_nonneg_left (hphysical j).2 (sq_nonneg _)
              have hqfac : 0≤qfac := by dsimp only [qfac,den]; positivity
              have hside0 : 0≤side := by dsimp only [side]; split_ifs <;> positivity
              let Enamed := geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
                (Real.logb Z X) hK bin (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q))
                N b j.val B*
                (‖partEnergy true τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset u.pools))
                  (coefficient u (R*I) j.val.2.1.val) W
                  (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)
                  (firstMainFourierScale reflected (Z^M) X Z ξ sigma reserve b N l)
                  Z ξ (sourceRadius u)‖/geometryExceptionalVolume u)
              have hh := full_main_paid_fold_algebra Enamed side Shell
                (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/rad)
                ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)) Ck
                (CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
                Pz lower (geometryExceptionalLowerConstant N slotlo wlo) Dproj
                (p.control Sp^2) ((1+‖t‖)^(2*J)) ((∏i,s.M i)^6)
                ((b^N)^(1/3:ℝ)) qfac ((X/(I.absNorm:ℝ))^(1/3:ℝ)) kr
                (Z^(-sigma/3)) (Z^(-2*max (inputCap Z u) 0/3)) Rpow
                hpayed hside hlow href
                hside0 hShell
                (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le)
                (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
                  (Nat.cast_nonneg _))
                (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hbase _)
                hLower hDproj.le hControl
                (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hb) _) _)
                hqfac (Real.rpow_nonneg (div_nonneg hXpos.le hIpos.le) _)
                (Real.rpow_nonneg
                  (first_main_radius_pos reflected (Z^M) X Z ξ sigma reserve hZpos l).le _)
                (mul_nonneg (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hZpos.le _))
              convert hh using 1; dsimp only [Enamed,G,coef,Control,u]; ring
            have hrow : cost j≤((actualAllocations s.pools I).card:ℝ)^2*G/(rad*Dproj) := by
              calc
                _≤∑_B : actualAllocations s.pools I,((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
                  unfold cost geometryExceptionalMainRowMass
                  apply Finset.sum_le_sum
                  intro B _
                  split_ifs with hne
                  · exact hpoint B hne
                  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hG)
                      (mul_nonneg hrad.le hDproj.le)
                _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]; ring
            have hI0 : I≠0 := by
              dsimp only [I,geometryColumnIdeal]
              split_ifs <;> exact (by first | exact src.hD.1 | exact src.hC.1)
            have hIcap : (I.absNorm:ℝ)≤Z^(3:ℝ) := by
              dsimp only [I,geometryColumnIdeal]
              split_ifs
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 1).2
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 0).2
            have hcardalloc := hDa.2 (ι:=ι⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
              s.pools I hI0
            have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardalloc 2
            rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),
              show εalloc/2*(2:ℕ)=εalloc by norm_num] at hcard2
            have hcardZ : ((actualAllocations s.pools I).card:ℝ)^2≤Da^2*Z^(3*εalloc) := by
              apply hcard2.trans
              rw [Real.rpow_mul (zero_lt_one.trans hZ).le]
              exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hIcap hea.le) (sq_nonneg _)
            apply hrow.trans
            have hrpow : Z^(geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)=rad :=
              Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hrad
            have hpow : Z^(3*εalloc)*Pz*Rpow=Z^exponent := by
              dsimp only [Pz,Rpow,exponent,X]
              rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
              congr 1
              ring
            calc
              _≤(Da^2*Z^(3*εalloc))*G/(rad*Dproj) := by gcongr
              _=factor*Z^exponent/(rad*Dproj) := by
                dsimp only [factor,G]
                rw [←hpow]
                ring
              _=factor*Z^(exponent-geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)/Dproj := by
                rw [Real.rpow_sub (zero_lt_one.trans hZ),hrpow]
                ring
          have hfull := hz.2.2 s R seed (Z^M) hK bin hs hs0 hz₁ hz₂ hsourcepos hsource hV
            (by simpa only [Real.rpow_zero] using
              (inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hM))) rows
            (fun j _=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
              (fun _=>logAnnulus) j (by assumption))
            (fun j _=>actual_geometry_projector_cap s N R seed (Z^M) Z ξ 3 hK hcard hZ.le
              (by norm_num) hpool bin j)
            factor exponent cost hfactor hc hcost
          have hpost (P : Finset (Ideal O)) (β loss Ccap : ℝ)
              (hbβ : Cycle63.Optimization.firstCellTop≤β ∧ β≤Cycle63.Optimization.slotTop) (hCcap : 0≤Ccap)
              (hσ : sigma/3=Cycle63.Arithmetic.amp β)
              (hprime : Z^(Cycle63.Arithmetic.amp β-loss)≤(P.card:ℝ)) :
              (56/(P.card:ℝ))*((Ccap+6*Cycle63.Arithmetic.amp β)/(Cycle63.Arithmetic.amp β/2))*
                (∑j : rows,cost j)≤
              16800*(Ccap+1)*(Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ))*Z^loss := by
            let E := Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ)
            have hE : 0≤E := div_nonneg
              (mul_nonneg (mul_nonneg hCd.1.le hfactor) (Real.rpow_nonneg hZpos.le _))
              (Nat.cast_nonneg _)
            have hp : (0:ℝ)<P.card := (Real.rpow_pos_of_pos hZpos _).trans_le hprime
            have hamp : 0<Cycle63.Arithmetic.amp β := Cycle63.Arithmetic.amp_pos hbβ
            have hpref : 0≤(56/(P.card:ℝ))*
                ((Ccap+6*Cycle63.Arithmetic.amp β)/(Cycle63.Arithmetic.amp β/2)) :=
              mul_nonneg (div_nonneg (by norm_num) hp.le)
                (div_nonneg (add_nonneg hCcap (mul_nonneg (by norm_num) hamp.le))
                  (half_pos hamp).le)
            have hsplit : Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)=
                E*Z^(Cycle63.Arithmetic.amp β) := by
              have hpow : Z^(exponent+3*εcount)=
                  Z^(exponent+3*εcount-sigma/3)*Z^(Cycle63.Arithmetic.amp β) := by
                rw [←Real.rpow_add hZpos,←hσ]
                congr 1
                ring
              rw [hpow]
              dsimp only [E]
              ring
            calc
              _≤(56/(P.card:ℝ))*((Ccap+6*Cycle63.Arithmetic.amp β)/(Cycle63.Arithmetic.amp β/2))*
                  (Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)) :=
                mul_le_mul_of_nonneg_left hfull hpref
              _=_ := by rw [hsplit]
              _≤_ := geometry_main_prime_payment P Z β loss Ccap E hZpos hbβ hCcap hE hprime
          exact And.intro hfull hpost))))))))

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_exceptional_full

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_full_error_reference
