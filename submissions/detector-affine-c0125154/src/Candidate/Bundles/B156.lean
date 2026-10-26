/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B109
import Candidate.Bundles.B115
import Candidate.Bundles.B117
import Candidate.Bundles.B137
import Candidate.Bundles.B138
import Candidate.Bundles.B142
import Candidate.Bundles.B145
import Candidate.Bundles.B146
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorZero; sha256 8a4cd5869e4ee5c1671a1a711949d11fa74fdd48cc3ae357355722938ca5fc77 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                            
                                                       
                                                        
                                                                      

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcretePrimeRowBridge Cycle61Moment
open CenteredMomentLogDyadic
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAmplificationAllocationCost
open CenteredMomentFirstAnnularInput CenteredMomentCommonProfile
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements RayFourExpansion EisensteinSchwartzPoisson Cycle61SecondZero
local notation "O" => HeckeFamily.O
local instance errorZeroDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _

def firstErrorZeroRadius (reflected : Bool) (Z M V a δ reserve : ℝ)
    (l : FirstSourceLabel) (q : O) (k : ℕ) : ℝ :=
  errorCommonRadius Z (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
    (nominalLog l.1.1 l.1.2 (firstProjectorRadical l.1.1 l.1.2 l.2.val) (Z^M) V Z)
    (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) (3*a) δ reserve q k

def errorZeroSaving (reflected : Bool) (Z M A δ reserve padding ε s₀ : ℝ)
    (l : FirstSourceLabel) (q : O) (k : ℕ) : ℝ :=
  -M*(8754683599/120632400000)+δ+reserve+
    ε*(A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      errorRemoval q Z k+padding)-s₀

/-- The physical nominal labels stay in their original order in both
orientations; extraction retains its literal divisor and removal gain. -/
theorem actual_first_label_error_zero (N : ℕ) (Cs bs lo hi ε : ℝ)
    (hCs : 1≤ Cs) (hbs : 1≤ bs) (hlo : 0< lo) (hhi : 0≤ hi) (hε : 0<ε) :
    ∃ C₀ : ℝ, 0< C₀ ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀s : Input ι, Fintype.card ι≤ N → (∀i,s.M i≤ Cs) → s.upper≤ bs →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(reflected : Bool)(l : FirstSourceLabel),Supported l.1.1 → Supported l.1.2 →
    CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2 →
    ∀(R seed : Ideal O),seed≠0 →
    ∀(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0 →
    ∀(q : O),q≠0 → ∀k : ℕ,k=1 ∨ k=6 ∨ k=7 →
    (∀i,∀I∈(child s (if reflected then l.1.2 else l.1.1) R B χ t).slots i,
      IsCoprime (Ideal.span {q}) I) →
    ∀(Bp : actualAllocations (child s (if reflected then l.1.2 else l.1.1) R B χ t).pools
      ((Ideal.span {q})^k))(υ : Character)(v : ℝ)(W : 𝓢(ℝ,ℂ))
      (Z beta M A a δ reserve padding s₀ b₁ b₂ : ℝ),1< Z →
    3401/100000≤ beta ∧ beta≤1/25 → 0≤ M →
    A≤ M*Cycle61.Arithmetic.totalA beta → a≤ M*Cycle61.Arithmetic.amp beta → 0≤ a →
    1≤ b₁ → 1≤ b₂ → Endpoints bs b₁ b₂ s →
    geometry N bs b₁ b₂≤ Z^padding → volume s≤ Z^A → Z^s₀≤(seed.absNorm:ℝ) →
    let C := if reflected then l.1.2 else l.1.1
    let u := twiceChild s C R B χ t (Ideal.span {q}) k Bp υ v
    Z^(-firstZeroReference reflected Z A a l)*
      (localErrorCost q (k-1)*(‖originalSecondZero u ((R*C)*(Ideal.span {q})^k) seed W
        (firstErrorZeroRadius reflected Z M (volume s) a δ reserve l q k)‖/volume u))≤
      C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        Z^(errorZeroSaving reflected Z M A δ reserve padding ε s₀ l q k) := by
  obtain ⟨C₀,hC₀,hbound⟩ := uniform_radius_certificates N Cs bs hi ε hCs hbs hε
  refine ⟨C₀,hC₀,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ reflected l hC hD heq R seed hseed B χ t hB q hq k hk
    hslot Bp υ v W Z beta M A a δ reserve padding s₀ b₁ b₂ hZ hb hM hA ha ha0
    hb₁ hb₂ he hgeo hvol hseedN C u
  let c := Real.logb Z (C.absNorm:ℝ)
  let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
  let Rw := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
  let E := firstProjectorRadical l.1.1 l.1.2 l.2.val
  let e := Real.logb Z (E.absNorm:ℝ)
  have hselected : C≠0 := by cases reflected <;> first | exact hC.1 | exact hD.1
  have hother : (if reflected then l.1.1 else l.1.2)≠0 := by
    cases reflected <;> first | exact hD.1 | exact hC.1
  have hE : E≠0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mp (Nat.ne_of_gt
      (firstCommonSubsetNorm_pos _ _ hC l.2.val))
  have hz := zero_lt_one.trans hZ
  have hQ : Ideal.span {q}≠0 := Ideal.span_singleton_eq_bot.not.mpr hq
  have hcn : Z^c≤(C.absNorm:ℝ) := by
    rw [Real.rpow_logb hz hZ.ne' (norm_pos C hselected)]
  have hqn : Z^(errorRemoval q Z k)≤((Ideal.span {q}).absNorm:ℝ)^k := by
    unfold errorRemoval
    rw [mul_comm,Real.rpow_mul hz.le,Real.rpow_natCast,
      Real.rpow_logb hz hZ.ne' (normValue_pos q hq)]
    exact le_rfl
  have hv := actual_twice_volume_cap N bs b₁ b₂ hbs hb₁ hb₂ s hn he C R B χ t hB
    (Ideal.span {q}) hQ k hslot Bp υ v Z A c (errorRemoval q Z k) padding hZ hgeo hvol hcn hqn
  have hnom := Cycle61NominalRadius.actual_nominal_le l.1.1 l.1.2 E hC.1 hD.1 hE heq
    (volume s) Z M A (volume_pos s) hZ hvol
  have hnom' : nominalLog l.1.1 l.1.2 E (Z^M) (volume s) Z≤2*A-c-d+Rw+e-M := by
    dsimp only [c,d,C,Rw,e] at *
    cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true] at * <;> linarith
  have hh := hbound hv.1 lo hlo hhi u p (fun i=>hm i.val.val) hs hp₁ hp₂
    ((R*C)*(Ideal.span {q})^k) seed hseed W Z beta M A a c d 0 Rw e
    (nominalLog l.1.1 l.1.2 E (Z^M) (volume s) Z) 0 δ reserve
    (A-c-errorRemoval q Z k+padding) s₀ hZ hb hM hA ha
    (ideal_log_nonneg C hselected Z hZ) (ideal_log_nonneg _ hother Z hZ)
    (by norm_num) (by simpa using hnom') hv.2.2.1 hseedN
  have href : -firstZeroReference reflected Z A a l = -a-(A-c+Rw+e+0) := by
    dsimp only [firstZeroReference,c,C,Rw,e,E]
    ring
  rw [href]
  simpa only [firstErrorZeroRadius,errorZeroSaving,
    original_zero_radiusTerm,c,d,C,Rw,e,E,add_zero,radiusTerm] using hh.2 q hq k hk ha0



/-- The active allocation domain is retained exactly as in the error split. -/
def extractedZeroSum {ι : Type*}[Fintype ι]
    (u : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(P : Finset (Ideal O))
    (radius : elementPool P→ Fin 3→ℝ)(υ : elementPool P→ Fin 3→ RayCharacter→ Character) : ℝ :=
  let Label := (q : elementPool P) × (i : Fin 3) × (_ψ : RayCharacter) ×
    actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1))
  let E := fun l : Label=>(Ideal.span {l.1.val})^(errorIndex l.2.1+1)
  let source := fun l : Label=>child u (E l) R
    (errorActiveAllocation u (E l) l.2.2.2) (υ l.1 l.2.1 l.2.2.1) u.t
  ∑l : Label,(16*(errorIndex l.2.1+2:ℝ)*localErrorCost l.1.val (errorIndex l.2.1)/
    volume (source l))*‖originalSecondZero (source l) (R*E l) seed W (radius l.1 l.2.1)‖

lemma extracted_zero_sum_eq {ι : Type*}[Fintype ι]
    (u : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(P : Finset (Ideal O))
    (radius : elementPool P→ Fin 3→ℝ)(υ : elementPool P→ Fin 3→ RayCharacter→ Character) :
    extractedZeroSum u R seed W P radius υ=
      ∑q : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
        ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1)),
          let v := child u ((Ideal.span {q.val})^(errorIndex i+1)) R
            (errorActiveAllocation u ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) u.t
          16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)*
            (‖originalSecondZero v (R*(Ideal.span {q.val})^(errorIndex i+1)) seed W (radius q i)‖/
              volume v) := by
  unfold extractedZeroSum
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro ψ hψ
  apply Finset.sum_congr rfl
  intro Bp hBp
  ring


def firstExtractedZeroSum {ι : Type*}[Fintype ι]
    (s : Input ι)(reflected : Bool)(l : FirstSourceLabel)(R seed : Ideal O)
    (B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(W : 𝓢(ℝ,ℂ))(Z M a δ reserve : ℝ)
    (P : Finset (Ideal O))(υ : elementPool P→ Fin 3→ RayCharacter→ Character) : ℝ :=
  let C := if reflected then l.1.2 else l.1.1
  extractedZeroSum (child s C R B χ t) (R*C) seed W P
    (fun q i=>firstErrorZeroRadius reflected Z M (volume s) a δ reserve l q.val (errorIndex i+1)) υ

/-- Genuine plain allocation counting pays the extracted allocations and
rays. The remaining prime sum keeps every extraction removal gain. -/
theorem actual_first_label_error_zero_sum (N : ℕ)(Cs bs lo hi ε : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hlo : 0< lo)(hhi : 0≤ hi)(hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι],
    ∀s : Input ι,Fintype.card ι≤ N → (∀i,s.M i≤ Cs) → s.upper≤ bs →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(reflected : Bool)(l : FirstSourceLabel),Supported l.1.1 → Supported l.1.2 →
    CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2 →
    ∀(R seed : Ideal O),seed≠0 →
    ∀(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0 →
    ∀(W : 𝓢(ℝ,ℂ))(Z beta M A a δ reserve padding s₀ b₁ b₂ : ℝ),1< Z →
    3401/100000≤ beta ∧ beta≤1/25 → 0≤ M →
    A≤ M*Cycle61.Arithmetic.totalA beta → a≤ M*Cycle61.Arithmetic.amp beta → 0≤ a →
    1≤ b₁ → 1≤ b₂ → Endpoints bs b₁ b₂ s →
    geometry N bs b₁ b₂≤ Z^padding → volume s≤ Z^A → Z^s₀≤(seed.absNorm:ℝ) →
    ∀P : Finset (Ideal O),(∀q : elementPool P,Prime (Ideal.span {q.val})) →
    (∀q : elementPool P,∀i,∀I∈(child s (if reflected then l.1.2 else l.1.1) R B χ t).slots i,
      IsCoprime (Ideal.span {q.val}) I) →
    ∀υ : elementPool P→ Fin 3→ RayCharacter→ Character,
    firstExtractedZeroSum s reflected l R seed B χ t W Z M a δ reserve P υ≤
      K*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        ∑q : elementPool P,∑i : Fin 3,
          Z^(firstZeroReference reflected Z A a l+
            errorZeroSaving reflected Z M A δ reserve padding ε s₀ l q.val (errorIndex i+1)) := by
  obtain ⟨C₀,hC₀,hzero⟩ := actual_first_label_error_zero N Cs bs lo hi ε hCs hbs hlo hhi hε
  have hray : 0<(Fintype.card RayCharacter:ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨1024*(Fintype.card RayCharacter:ℝ)*C₀,by positivity,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ reflected l hC hD heq R seed hseed B χ t hB W
    Z beta M A a δ reserve padding s₀ b₁ b₂ hZ hb hM hA ha ha0 hb₁ hb₂ he hgeo hvol hseedN
    P hprime hslot υ
  let C := if reflected then l.1.2 else l.1.1
  let u := child s C R B χ t
  let F := C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖
  let power := fun (q : elementPool P)(i : Fin 3)=>Z^(firstZeroReference reflected Z A a l+
    errorZeroSaving reflected Z M A δ reserve padding ε s₀ l q.val (errorIndex i+1))
  have hpair (q : elementPool P)(i : Fin 3) :
      (∑ψ : RayCharacter,
        ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1)),
          let v := child u ((Ideal.span {q.val})^(errorIndex i+1)) (R*C)
            (errorActiveAllocation u ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) u.t
          16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)*
            (‖originalSecondZero v ((R*C)*(Ideal.span {q.val})^(errorIndex i+1)) seed W
              (firstErrorZeroRadius reflected Z M (volume s) a δ reserve l q.val (errorIndex i+1))‖/
                volume v))≤1024*(Fintype.card RayCharacter:ℝ)*(F*power q i) := by
    have hq : q.val≠0 := by
      intro hq
      exact (hprime q).ne_zero (by rw [hq];simp)
    have hk := error_extracted_index_cases i
    have hcount := actual_error_allocations_card (activeInput u).pools (Ideal.span {q.val})
      (hprime q) (errorIndex i+1) hk (by
        intro j I hI
        have hI' := error_active_pools_subset u (Sum.inl j) hI
        exact ⟨u.pools_ne (Sum.inl j) I hI',hslot q j I hI'⟩)
    have hc : (Fintype.card (actualAllocations (activeInput u).pools
        ((Ideal.span {q.val})^(errorIndex i+1))):ℝ)≤8 := by
      simpa only [Fintype.card_coe] using (show ((actualAllocations (activeInput u).pools
        ((Ideal.span {q.val})^(errorIndex i+1))).card:ℝ)≤8 by exact_mod_cast hcount)
    have hi : 0≤16*(errorIndex i+2:ℝ) ∧ 16*(errorIndex i+2:ℝ)≤128 := by
      rcases errorIndex_cases i with h|h|h <;> rw [h] <;> norm_num
    have hpoint (ψ : RayCharacter)
        (Bp : actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1))) :
        let v := child u ((Ideal.span {q.val})^(errorIndex i+1)) (R*C)
          (errorActiveAllocation u ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) u.t
        16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)*
          (‖originalSecondZero v ((R*C)*(Ideal.span {q.val})^(errorIndex i+1)) seed W
            (firstErrorZeroRadius reflected Z M (volume s) a δ reserve l q.val (errorIndex i+1))‖/
              volume v)≤128*(F*power q i) := by
      have hh := hzero s hn hm hs p hp₁ hp₂ reflected l hC hD heq R seed hseed B χ t hB
        q.val hq (errorIndex i+1) hk (hslot q) (errorActiveAllocation u ((Ideal.span {q.val})^(errorIndex i+1)) Bp)
        (υ q i ψ) u.t W Z beta M A a δ reserve padding s₀ b₁ b₂ hZ hb hM hA ha ha0
        hb₁ hb₂ he hgeo hvol hseedN
      have hh' := reference_power_remove Z _ _ _ _ (zero_lt_one.trans hZ) hh
      have hmul := mul_le_mul_of_nonneg_left hh' hi.1
      apply (show _≤16*(errorIndex i+2:ℝ)*(F*power q i) by
        simpa only [twiceChild,u,C,F,power,Nat.add_sub_cancel,mul_assoc] using hmul).trans
      exact mul_le_mul_of_nonneg_right hi.2 (by dsimp only [F,power];positivity)
    calc
      _≤∑ψ : RayCharacter,∑Bp : actualAllocations (activeInput u).pools
          ((Ideal.span {q.val})^(errorIndex i+1)),128*(F*power q i) :=
        Finset.sum_le_sum (fun ψ _=>Finset.sum_le_sum (fun Bp _=>hpoint ψ Bp))
      _=(Fintype.card RayCharacter:ℝ)*
          (Fintype.card (actualAllocations (activeInput u).pools
            ((Ideal.span {q.val})^(errorIndex i+1))):ℝ)*(128*(F*power q i)) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        ring
      _≤(Fintype.card RayCharacter:ℝ)*8*(128*(F*power q i)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
          (by dsimp only [F,power];positivity)
      _=_ := by ring
  unfold firstExtractedZeroSum
  rw [extracted_zero_sum_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply (hpair q i).trans_eq
  dsimp only [F,power]
  ring


def errorZeroPrimeWeight (Z ε : ℝ)(P : Finset (Ideal O)) : ℝ :=
  ∑q : elementPool P,∑i : Fin 3,Z^(-ε*errorRemoval q.val Z (errorIndex i+1))

lemma error_zero_power_factor (reflected : Bool)(l : FirstSourceLabel)
    (Z M A a ξ δ reserve padding ε s₀ : ℝ)(q : O)(k : ℕ)(hZ : 0< Z) :
    Z^(firstZeroReference reflected Z A a l+
      errorZeroSaving reflected Z M A δ reserve padding ε s₀ l q k)=
    Z^(δ-frequencyLoss Z 32 ξ)*
      Z^(firstZeroReference reflected Z A a l+
        firstZeroSaving reflected Z M A ξ reserve padding ε s₀ l)*
      Z^(-ε*errorRemoval q Z k) := by
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  dsimp only [errorZeroSaving,firstZeroSaving]
  ring

/-- The nominal projector is the original physical projector, also on
reflection; no nominal capacity or swapped active radical is inserted. -/
lemma geometry_error_zero_radius {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(R seed : Ideal O)(Z M ξ a δ reserve : ℝ)(hK : 0< Z^M)
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key))(q : O)(k : ℕ) :
    let g := geometryBranch reflected s R seed (Z^M) Z ξ hK key j
    errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z) g.cLog (3*a) δ reserve q k=
      firstErrorZeroRadius reflected Z M (volume s) a δ reserve
        (geometryFirstLabel s R seed (Z^M) Z ξ hK key j) q k := by
  dsimp only [geometryBranch,geometryFirstLabel,geometryColumnIdeal,firstErrorZeroRadius]
  rw [primeSubsetGenerator,span_idealGenerator]
  rfl

/-- All first common allocations are paid by their genuine normalized
mass. The prime removal sum and the physical first scalar stay literal. -/
theorem actual_geometry_error_zero_family (N : ℕ)(Cs bs lo hi ε εmass : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hlo : 0< lo)(hhi : 0≤ hi)(hε : 0<ε)(hem : 0<εmass) :
    ∃K : ℝ,0< K ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι],
    ∀s : Input ι,Fintype.card ι≤ N → (∀i,s.M i≤ Cs) → s.upper≤ bs →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(W : 𝓢(ℝ,ℂ))(reflected : Bool)(R seed : Ideal O)
      (Z beta M A a ξ δ reserve padding b₁ b₂ : ℝ)(hZ : 1< Z),
    3401/100000≤ beta ∧ beta≤1/25 → 0≤ M →
    A≤ M*Cycle61.Arithmetic.totalA beta → a≤ M*Cycle61.Arithmetic.amp beta → 0≤ a →
    1≤ b₁ → 1≤ b₂ → Endpoints bs b₁ b₂ s →
    geometry N bs b₁ b₂≤ Z^padding → volume s≤ Z^A →
    ∀P : Finset (Ideal O),(∀q : elementPool P,Prime (Ideal.span {q.val})) →
    (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀key : ℤ×(Fin 5→ℤ),
    ∀weight : Cycle61JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ,
    ∀rows : Finset (FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)),∀t : ℝ,
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let l := fun j : rows=>geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val
    ∀υ : (j : rows)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character,
    (∑j : rows,∑B : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B*
        firstExtractedZeroSum s reflected (l j) R j.val.2.1.val B
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t W
          Z M a δ reserve P (υ j B))≤
      K*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*errorZeroPrimeWeight Z ε P*
        Z^(δ-frequencyLoss Z 32 ξ)*
        ∑j : rows,‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hK key weight j.val‖^2*
          ((C j).absNorm:ℝ)^(εmass-1)*
          Z^(firstZeroReference reflected Z A a (l j)+firstZeroSaving reflected Z M A ξ reserve
            padding ε (Real.logb Z (j.val.2.1.val.absNorm:ℝ)) (l j)) := by
  obtain ⟨C₀,hC₀,hzero⟩ := actual_first_label_error_zero_sum N Cs bs lo hi ε hCs hbs hlo hhi hε
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs bs εmass hCs hem
  refine ⟨D*C₀,mul_pos hD hC₀,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ W reflected R seed Z beta M A a ξ δ reserve padding b₁ b₂
    hZ hb hM hA ha ha0 hb₁ hb₂ he hgeo hvol P hprime hslot key weight rows t hK C l υ
  let F := C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*errorZeroPrimeWeight Z ε P*
    Z^(δ-frequencyLoss Z 32 ξ)
  let power := fun j : rows=>Z^(firstZeroReference reflected Z A a (l j)+
    firstZeroSaving reflected Z M A ξ reserve padding ε (Real.logb Z (j.val.2.1.val.absNorm:ℝ)) (l j))
  have hpr : 0≤ errorZeroPrimeWeight Z ε P := by
    unfold errorZeroPrimeWeight
    exact Finset.sum_nonneg (fun q _=>Finset.sum_nonneg
      (fun i _=>Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hK key weight j.val‖^2*
    ((C j).absNorm:ℝ)^(εmass-1)
  have hC (j : rows) : C j≠0 := by
    cases reflected
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1).hC.1
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1).hD.1
  have hterm (j : rows)(B : actualAllocations s.pools (C j)) :
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B*
        firstExtractedZeroSum s reflected (l j) R j.val.2.1.val B
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t W
          Z M a δ reserve P (υ j B)≤
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B*(F*power j) := by
    by_cases hB : frozenCoefficient B.val (C j) R s.ν s.W s.P≠0
    · let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1
      have hseed := actual_first_divisor_ne_zero src j.val.2.1
      have hseedN : Z^(Real.logb Z (j.val.2.1.val.absNorm:ℝ))≤(j.val.2.1.val.absNorm:ℝ) := by
        rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (norm_pos _ hseed)]
      have hh := hzero s hn hm hs p hp₁ hp₂ reflected (l j) src.hC src.hD src.sameSupport
        R j.val.2.1.val hseed B (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val)
        t hB W Z beta M A a δ reserve padding (Real.logb Z (j.val.2.1.val.absNorm:ℝ)) b₁ b₂
        hZ hb hM hA ha ha0 hb₁ hb₂ he hgeo hvol hseedN P hprime
        (fun q=>actual_child_full_slot_coprime s _ (hslot q) _ R B _ t) (υ j B)
      have heq : (∑q : elementPool P,∑i : Fin 3,Z^(firstZeroReference reflected Z A a (l j)+
          errorZeroSaving reflected Z M A δ reserve padding ε
            (Real.logb Z (j.val.2.1.val.absNorm:ℝ)) (l j) q.val (errorIndex i+1)))=
          Z^(δ-frequencyLoss Z 32 ξ)*power j*errorZeroPrimeWeight Z ε P := by
        simp_rw [error_zero_power_factor reflected (l j) Z M A a ξ δ reserve padding ε
          (Real.logb Z (j.val.2.1.val.absNorm:ℝ)) _ _ (zero_lt_one.trans hZ)]
        simp only [errorZeroPrimeWeight,Finset.mul_sum,power]
      rw [heq] at hh
      have hh' : firstExtractedZeroSum s reflected (l j) R j.val.2.1.val B
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t W
          Z M a δ reserve P (υ j B)≤ F*power j := by
        apply hh.trans_eq
        dsimp only [F]
        ring
      exact mul_le_mul_of_nonneg_left hh'
        (geometryAllocationWeight_nonneg reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B)
    · have hw : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B=0 := by
        simp only [geometryAllocationWeight,C,hB,ite_false]
      rw [hw,zero_mul,zero_mul]
  calc
    _≤∑j : rows,∑B : actualAllocations s.pools (C j),
        geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B*(F*power j) :=
      Finset.sum_le_sum (fun j _=>Finset.sum_le_sum (fun B _=>hterm j B))
    _≤∑j : rows,(D*mass j)*(F*power j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [←Finset.sum_mul]
      have hmj : (∑B : actualAllocations s.pools (C j),
          geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B)≤ D*mass j := by
        simpa only [mass,C,mul_assoc] using
          hmass s hn hm reflected R seed (Z^M) Z ξ M A hK key weight j.val (hC j)
      exact mul_le_mul_of_nonneg_right hmj (by dsimp only [F,power];positivity)
    _=_ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [F,power,mass]
      ring


/-- This optional collapse uses genuine ideal counting and pays the prime
cutoff explicitly. The uncollapsed family theorem retains removal gains. -/
theorem error_zero_prime_weight_le (P : Finset (Ideal O))(Z ε U : ℝ)
    (hZ : 1< Z)(hε : 0≤ε)(hU : 0≤ U)
    (hp : ∀Q∈P,Prime Q)(hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hcap : ∀Q∈P,(Q.absNorm:ℝ)≤ Z^U) :
    errorZeroPrimeWeight Z ε P≤384*Z^U := by
  have hz := zero_lt_one.trans hZ
  have hcount : (P.card:ℝ)≤128*Z^U :=
    DescentFiberCost.finite_ideal_count_real P (Z^U)
      (Real.one_le_rpow hZ.le hU) (fun Q hQ=>(hp Q hQ).ne_zero) hcap
  have hpoint (q : elementPool P)(i : Fin 3) : Z^(-ε*errorRemoval q.val Z (errorIndex i+1))≤1 := by
    have hdata := elementPool_data P hp hbad q.val q.property
    have hQ : Ideal.span {q.val}≠0 := hdata.2.2.2.1.1
    have hw : 0≤ errorRemoval q.val Z (errorIndex i+1) := by
      unfold errorRemoval
      exact mul_nonneg (Nat.cast_nonneg _) (ideal_log_nonneg _ hQ Z hZ)
    simpa only [neg_mul] using
      (Real.rpow_le_rpow_of_exponent_le hZ.le (neg_nonpos.mpr (mul_nonneg hε hw))).trans_eq
        (Real.rpow_zero Z)
  calc
    _≤∑q : elementPool P,∑i : Fin 3,(1:ℝ) :=
      Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun i _=>hpoint q i))
    _=3*(P.card:ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
        Fintype.card_coe,elementPool_card P hp hbad]
      ring
    _≤3*(128*Z^U) := mul_le_mul_of_nonneg_left hcount (by norm_num)
    _=_ := by ring


/-- Full physical first-column payment, with an honest prime-count cost.
The reflected physical D contributes its reciprocal dyad factor. -/
theorem eventual_actual_geometry_error_zero {ι : Type*}[Fintype ι][DecidableEq ι]
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
      Real.logb Z (volume s)≤ M*Cycle61.Arithmetic.totalA beta →
      a≤ M*Cycle61.Arithmetic.amp beta → Real.logb Z (volume s)≤ Amax →
      1≤ b₁ → 1≤ b₂ → Endpoints bs b₁ b₂ s → geometry N bs b₁ b₂≤ Z^padding →
      Squarefree seed → seed≠0 → 0< sourceRadius s → sourceRadius s≤ Z^B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^a) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let l := fun j : rows=>geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let factor := if reflected then 1/geometryDCompensator key else
      2*(geometrySupportConstant N slotlo lo lo)^2*geometryDCompensator key
    ∀υ : (j : rows)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character,
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val alloc*
        firstExtractedZeroSum s reflected (l j) R j.val.2.1.val alloc
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t Φ
          Z M a δ reserve P (υ j alloc))≤
      Czero*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*factor*
        Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount+a+
          δ-frequencyLoss Z 32 ξ)/(seed.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hfamily⟩ := actual_geometry_error_zero_family N Cs bs lo hi εzero εmass
    hCs hbs hlo hhi hez hem
  obtain ⟨C,hC,hpayment⟩ := eventual_actual_geometry_zero_mass_payment (ι:=ι)
    Amax 0 B (((N:ℝ)+2)*U) ξ εcount hAmax (by norm_num) hB (by positivity) hξ hec
    N slotlo lo lo hslotlo hlo hlo
  refine ⟨384*K₀*C,by positivity,?_⟩
  filter_upwards [hpayment] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed W Φ hn hm hs hl p hp₁ hp₂ beta M a δ reserve padding t b₁ b₂ hZ hb hM ha0
    hA ha hA' hb₁ hb₂ he hgeo hseed hseed0 hsource hcap hpool P hp hbad hpcap hslot
    reflected key hK A rows Cj l weight factor υ
  have hs₁ : ∀x,s.W₁ x≠0→ lo≤ x := by
    intro x hx;rw [hp₁] at hx;exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→ lo≤ x := by
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
  have hpweight := error_zero_prime_weight_le P Z εzero a hZ hez.le ha0 hp hbad hpcap
  have hpnonneg : 0≤ errorZeroPrimeWeight Z εzero P := by
    unfold errorZeroPrimeWeight
    exact Finset.sum_nonneg (fun q _=>Finset.sum_nonneg
      (fun i _=>Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  have hH := (geometryDCompensator_pos key).le
  have hfactor : 0≤ factor := by dsimp only [factor];split <;> positivity
  apply hzero.trans
  apply (mul_le_mul_of_nonneg_left hmass (by positivity :
    0≤ K₀*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*errorZeroPrimeWeight Z εzero P*
      Z^(δ-frequencyLoss Z 32 ξ))).trans
  calc
    _≤ K₀*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*(384*Z^a)*
        Z^(δ-frequencyLoss Z 32 ξ)*
        (C*factor*Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)/
          (seed.absNorm:ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpweight (by positivity))
          (by positivity)) (by positivity)
    _=_ := by
      have hpow : Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount+a+
          δ-frequencyLoss Z 32 ξ)=
          Z^(zeroPaymentExponent Z M A a ξ reserve padding εzero εmass B+3*εcount)*
            Z^a*Z^(δ-frequencyLoss Z 32 ξ) := by
        rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
        congr 1
        ring
      rw [hpow]
      ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_label_error_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_label_error_zero_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_zero_radius
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_zero_family
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_zero_prime_weight_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_zero

#print axioms OAI.SevenEighths.Cycle61InitialMass.extracted_zero_sum_eq
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_zero_power_factor

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorZero -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorRemainder; sha256 ffd5402b9f85c436f2742176f0e5eda571e3db9f4afbe555cdad582ff2377773 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                     
                                                     
                                                            
                                                       
                                                                      
                                                                          

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
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
      Real.logb Z (volume s)≤ M*Cycle61.Arithmetic.totalA beta →
      a≤ M*Cycle61.Arithmetic.amp beta → Real.logb Z (volume s)≤ Amax →
      1≤ b₁ → 1≤ b₂ → Endpoints bs b₁ b₂ s → geometry N bs b₁ b₂≤ Z^padding →
      Squarefree seed → seed≠0 → 0< sourceRadius s → sourceRadius s≤ Z^B →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^a) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let l := fun j : rows=>geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let factor := if reflected then 1/geometryDCompensator key else
      2*(geometrySupportConstant N slotlo lo lo)^2*geometryDCompensator key
    ∀υ : (j : rows)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character,
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
  have hs₁ : ∀x,s.W₁ x≠0→ lo≤ x := by
    intro x hx;rw [hp₁] at hx;exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→ lo≤ x := by
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
    exact Finset.sum_nonneg (fun q _=>Finset.sum_nonneg
      (fun i _=>Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  apply hzero.trans
  apply (mul_le_mul_of_nonneg_left hmass (by positivity :
    0≤ K₀*(p.control {(0,0)})^2*‖paperRadialFourier Φ 0‖*errorZeroPrimeWeight Z εzero P*
      Z^(δ-frequencyLoss Z 32 ξ))).trans_eq
  ring




def jointErrorRetained {First : Type*}[Fintype First]
    (α : First→ Type*)[∀f,Fintype (α f)](s : (f : First)→ Input (α f))
    (g : First→ FirstBranchGeometry)(w : First→ℝ)(Φ : 𝓢(ℝ,ℂ))(Z sigma ξ reserve : ℝ)
    (P : Finset (Ideal O))(υ : First→ elementPool P→ Fin 3→ RayCharacter→ Character)
    (Fourier : First→ elementPool P→ Fin 3→ℝ) : ℂ :=
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
    (α : First→ Type*)[∀f,Fintype (α f)](s : (f : First)→ Input (α f))
    (g : First→ FirstBranchGeometry)(w : First→ℝ)(hw : ∀f,0≤ w f)
    (Z sigma ξ reserve : ℝ)(hZ : 0< Z)(P : Finset (Ideal O))
    (υ : First→ elementPool P→ Fin 3→ RayCharacter→ Character)
    (Fourier : First→ elementPool P→ Fin 3→ℝ) :
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
      Real.logb Z (volume s)≤ M*Cycle61.Arithmetic.totalA beta →
      a≤ M*Cycle61.Arithmetic.amp beta →
      1≤ b₁ → 1≤ b₂ → Endpoints b b₁ b₂ s → geometry N b b₁ b₂≤ Z^padding →
      Squarefree seed → seed≠0 → 0< sourceRadius s → sourceRadius s≤ Z^B →
      |Real.logb Z (volume s)|≤ B → (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^a) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let First := (j : rows) × actualAllocations s.pools (C j)
    let first := fun f : First=>child s (C f.1) R f.2
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key f.1.val) t
    let g := fun f : First=>geometryBranch reflected s R seed (Z^M) Z ξ hK key f.1.val
    let w := fun f : First=>geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b f.1.val f.2
    ∀υ : First→ elementPool P→ Fin 3→ RayCharacter→ Character,
    let Fourier := fun f : First=>fun (q : elementPool P)(i : Fin 3)=>
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
      ‖jointErrorRetained (fun f : First=>liveIndices f.2.val) first g w ballProfile
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
  have hnonneg : ∀f : First,0≤ w f := fun f=>geometryAllocationWeight_nonneg reflected s R seed
    (Z^M) Z ξ M A hK key weight N b f.1.val f.2
  have hh := actual_joint_error_split_grouped (fun f : First=>liveIndices f.2.val) first g w hnonneg
    Z (3*a) ξ reserve (zero_lt_one.trans hZ) P υ Fourier
  let radius := fun f (q : elementPool P)(i : Fin 3)=>errorCommonRadius Z (g f).d
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
    have he : radius ⟨j,alloc⟩=fun q i=>firstErrorZeroRadius reflected Z M (volume s) a
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_zero_prime_weight
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_error_split_grouped
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_remainder

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorRemainder -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAmplifiedRemainder; sha256 bfa637b771f457fe92e741ec8dbaba207c3b6733aec53ed14ea3e416cd9d2091 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                          
                                       
                                          
                                                        

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentPrimeElements
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice
open Cycle61SecondZero
local notation "O" => HeckeFamily.O

/-- The actual prime average costs only the three extracted branches.
The prime pool is not replaced by a polynomial counting estimate. -/
theorem actual_error_zero_prime_average (P : Finset (Ideal O)) (Z ε : ℝ)
    (hne : P.Nonempty) (hZ : 1< Z) (hε : 0≤ε)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes) :
    (56/(P.card:ℝ))*errorZeroPrimeWeight Z ε P≤168 := by
  have hn : (0:ℝ)< P.card := by exact_mod_cast hne.card_pos
  have hpoint (q : elementPool P) (i : Fin 3) :
      Z^(-ε*errorRemoval q.val Z (errorIndex i+1))≤1 := by
    have hdata := elementPool_data P hp hbad q.val q.property
    have hQ : Ideal.span {q.val}≠0 := hdata.2.2.2.1.1
    have hw : 0≤ errorRemoval q.val Z (errorIndex i+1) := by
      unfold errorRemoval
      exact mul_nonneg (Nat.cast_nonneg _) (ideal_log_nonneg _ hQ Z hZ)
    simpa only [neg_mul] using
      (Real.rpow_le_rpow_of_exponent_le hZ.le (neg_nonpos.mpr (mul_nonneg hε hw))).trans_eq
        (Real.rpow_zero Z)
  have hw : errorZeroPrimeWeight Z ε P≤3*(P.card:ℝ) := by
    calc
      _≤∑q : elementPool P,∑i : Fin 3,(1:ℝ) :=
        Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun i _=>hpoint q i))
      _=3*(P.card:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
          Fintype.card_coe,elementPool_card P hp hbad]
        ring
  calc
    _≤(56/(P.card:ℝ))*(3*(P.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _=168 := by field_simp; norm_num

/-- A strict zero-frequency saving remains even after cancelling the
entire error prime pool. The small analytic losses are explicit. -/
theorem geometry_zero_exponent_saving (Z M A a ξ reserve padding ε εmass B count β : ℝ)
    (hM : 0≤ M) (hb : 3401/100000≤β ∧ β≤1/25)
    (ha : a≤ M*Cycle61.Arithmetic.amp β)
    (hloss : frequencyLoss Z 32 ξ+reserve+ε*(A+padding)+B*εmass+3*count≤ M/100) :
    zeroPaymentExponent Z M A a ξ reserve padding ε εmass B+3*count≤-M/20 := by
  have hamp := mul_le_mul_of_nonneg_left (Cycle61.Arithmetic.amp_bounds hb).2 hM
  unfold zeroPaymentExponent
  linarith


/-- The three extracted branches retain a uniform strict saving after the
full prime average and arithmetic-label sums. The factor 1872 is the exact
sum of their existing multiplicities, rather than a new label count. -/
theorem geometry_error_branches_saving (Z Mmin εaffine M loss : ℝ)
    (hZ : 1≤ Z) (hMmin : 0< Mmin) (hM : Mmin≤ M)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    Z^loss*(∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*
      Z^(-M*Cycle61FinalError.branchReserve (errorIndex i+1)))≤
      1872*Z^(-M*(7/60000000:ℝ)) := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hres (k : ℕ) : (7/30000000:ℝ)≤ Cycle61FinalError.branchReserve k := by
    unfold Cycle61FinalError.branchReserve
    split_ifs <;> norm_num
  have hpoint (i : Fin 3) :
      Z^loss*(16*(errorIndex i+2:ℝ)^2*
        Z^(-M*Cycle61FinalError.branchReserve (errorIndex i+1)))≤
      (16*(errorIndex i+2:ℝ)^2)*Z^(-M*(7/60000000:ℝ)) := by
    have he := geometry_paid_loss Mmin εaffine M
      (Cycle61FinalError.branchReserve (errorIndex i+1)) loss hMmin hM (hres _) hloss
    calc
      _ = (16*(errorIndex i+2:ℝ)^2)*
          Z^(-M*Cycle61FinalError.branchReserve (errorIndex i+1)+loss) := by
        rw [Real.rpow_add hz]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ he) (by positivity)
  calc
    _ = ∑i : Fin 3,Z^loss*(16*(errorIndex i+2:ℝ)^2*
        Z^(-M*Cycle61FinalError.branchReserve (errorIndex i+1))) := Finset.mul_sum ..
    _ ≤ ∑i : Fin 3,(16*(errorIndex i+2:ℝ)^2)*Z^(-M*(7/60000000:ℝ)) :=
      Finset.sum_le_sum (fun i _=>hpoint i)
    _ = _ := by rw [←Finset.sum_mul]; norm_num [Fin.sum_univ_succ,errorIndex]


/-- Width-one amplification pays the main-source amplifier power exactly.
The coefficient is uniform across the 600 admissible cells. -/
theorem geometry_main_prime_payment (P : Finset (Ideal O)) (Z β loss Ccap E : ℝ)
    (hZ : 0< Z) (hb : 3401/100000≤β ∧ β≤1/25)
    (hC : 0≤ Ccap) (hE : 0≤ E)
    (hpool : Z^(Cycle61.Arithmetic.amp β-loss)≤(P.card:ℝ)) :
    (56/(P.card:ℝ))*((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2))*
      (E*Z^(Cycle61.Arithmetic.amp β))≤16800*(Ccap+1)*E*Z^loss := by
  have ha := Cycle61.Arithmetic.amp_bounds hb
  have hap := Cycle61.Arithmetic.amp_pos hb
  have hp : (0:ℝ)< P.card := (Real.rpow_pos_of_pos hZ _).trans_le hpool
  have hfac : (Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2)≤
      300*(Ccap+1) := by
    apply (div_le_iff₀ (half_pos hap)).mpr
    have hmul := mul_le_mul_of_nonneg_left ha.1 hC
    nlinarith
  have hratio : Z^(Cycle61.Arithmetic.amp β)/(P.card:ℝ)≤ Z^loss := by
    apply (div_le_iff₀ hp).mpr
    calc
      _=Z^(Cycle61.Arithmetic.amp β-loss)*Z^loss := by
        rw [←Real.rpow_add hZ]; congr 1; ring
      _≤ Z^loss*(P.card:ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpool
          (Real.rpow_nonneg hZ.le loss)
  calc
    _=56*((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2))*E*
        (Z^(Cycle61.Arithmetic.amp β)/(P.card:ℝ)) := by ring
    _≤56*(300*(Ccap+1))*E*Z^loss := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by norm_num)) hE
      · exact hratio
      · positivity
      · positivity
    _=_ := by ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_zero_prime_average
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_zero_exponent_saving

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_branches_saving

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_main_prime_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAmplifiedRemainder -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryPuncture; sha256 3df4d4aef084a345758627612c46cd2c823f0973728269c03b688cfecf5cedc3 -/
section
                                                   
                                                          

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O

/-- Cancel the first selected ideal before taking a uniform puncture cap.
This keeps the source exponent independent of the slot count. -/
theorem actual_common_child_puncture_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(hC : C≠0)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (E : Ideal O)(hE : (E.absNorm:ℝ)≤ sourceRadius (child s C R B χ t)) :
    ((R*C*E).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b bs bs*volume s := by
  have hc : 0<(C.absNorm:ℝ) := norm_pos C hC
  have h := (le_div_iff₀ hc).mp (hE.trans
    (actual_common_child_source_cap N b bs hb hbs s hcard he C R B χ t hne))
  have hr := mul_le_mul_of_nonneg_left h (show 0≤(R.absNorm:ℝ) by positivity)
  simpa only [map_mul,Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hr

/-- Both literal selected ideals in every second block have the same cap;
the choice of reflection introduces no additional source exponent. -/
theorem actual_second_block_puncture_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(hC : C≠0)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (seed : Ideal O)(hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K T Z ξ : ℝ)(hK : 0< K)
    (q : ActualSecondBlockIndex (child s C R B χ t) (R*C) seed K T Z ξ)
    (reflected : Bool) :
    let d:=actualSecondBlockDatum (liveIndices B.val) (child s C R B χ t)
      (R*C) seed hseed hz₁ hz₂ K T Z ξ hK q
    (((R*C)*(if reflected then d.D else d.C)).absNorm:ℝ)≤
      (R.absNorm:ℝ)*geometry N b bs bs*volume s := by
  intro d
  have hg:=actual_retained_block_gates (liveIndices B.val) (child s C R B χ t)
    (R*C) seed hseed hz₁ hz₂ K T Z ξ hK q
  apply actual_common_child_puncture_cap N b bs hb hbs s hcard he C R hC B χ t hne
  cases reflected
  · exact hg.2.2.1
  · exact hg.2.2.2

/-- The extracted prime power cancels together with the first selected
ideal. All prime powers are retained until this exact cancellation. -/
theorem actual_twice_child_puncture_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O)(hQ : Q≠0)(k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B χ t).pools (Q^k))
    (υ : Character)(v : ℝ)(E : Ideal O)
    (hE : (E.absNorm:ℝ)≤ sourceRadius (twiceChild s C R B χ t Q k Bp υ v)) :
    ((((R*C)*(Q^k))*E).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b bs bs*volume s := by
  have hc : 0<(C.absNorm:ℝ) := norm_pos C (allocation_ne s C B)
  have hq : 0<(Q.absNorm:ℝ) := norm_pos Q hQ
  have hd : 0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := mul_pos hc (pow_pos hq k)
  have hh:=hE.trans (twice_caps N b bs bs hb hbs hbs s hcard he C R B χ t hne Q hQ k hslot Bp υ v).2.2.2
  rw [←mul_div_assoc] at hh
  have hp := mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mp hh)
    (show 0≤(R.absNorm:ℝ) by positivity)
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,mul_assoc,mul_comm,mul_left_comm] using hp

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_child_puncture_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_block_puncture_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_twice_child_puncture_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryPuncture -/
