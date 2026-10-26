import Candidate.Cycle63.Physical.InitialMass.GeometryHighSelected

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Joint finite-bin high density for the physical geometric rows. The outside
weight stays inside each selected shell; only the fixed bin count is charged. -/
theorem actual_geometry_binned_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a rawError allowance Kcontrol T width Bbox target reserve : ℝ) (i : ℕ),
      21/25 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ),
      (∀l∈labels,∀j,-Bbox≤x l j ∧ x l j≤Bbox) →
      (∀l∈labels,x l 2+width≤Q) →
      (∀l∈labels,coeff l≤Z^(x l 0)) →
      (∀l∈labels,highExponentValue (2*a-1) (x l)≤target-reserve) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^(x l 2) ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^(x l 1)) →
      (i:ℝ)≤Z^P.τ →
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(C₁ R₁ : κ→Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      Real.logb Z (preVolume s.toData)≤Araw → pad≤allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0≤w j) → (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*a-1)*x l 3+rawError) →
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-reserve+4*width+loss+rawError+allowance)) := by
  obtain ⟨bound,hbound,J,hselected⟩ := actual_geometry_selected_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hselected P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key a rawError allowance Kcontrol T width Bbox target reserve i ha ha' hKcontrol hT hwidthbin
    hinj labels x coeff hx hq hcoeff hpoint st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  have hZ : 1<Z := by linarith [he.1]
  have hzpos : 0<Z := by linarith
  have hδ : Cycle63.Arithmetic.q0≤2*a-1 ∧ 2*a-1≤3/4 := by
    norm_num [Cycle63.Arithmetic.q0]; constructor <;> linarith
  have hd0 : 0≤2*a-1 := by linarith
  let shell := fun l=>∑L∈Ds l,∑alloc∈(src l).toSource.active L,
    retainedAllocationCost (src l) L alloc (z l)
  have hshell0 (l : κ) : 0≤shell l := Finset.sum_nonneg (fun L _=>
    Finset.sum_nonneg (fun alloc _=>retained_allocation_cost_nonneg _ _ _ _))
  let Cbase := C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)
  have hbase : 0≤Cbase := by dsimp [Cbase]; positivity
  have hbin (bin₂ : Fin 4→ℤ)(hbin : bin₂∈labels.image (fun l=>exponentBin width (x l))) :
      (∑l∈labels.filter (fun l=>exponentBin width (x l)=bin₂),coeff l*shell l)≤
        (Cbase*Z^(loss+rawError+allowance))*Z^(highExponentValue (2*a-1) (exponentBinUpper width bin₂)) := by
    let rows := labels.filter (fun l=>exponentBin width (x l)=bin₂)
    let u := exponentBinUpper width bin₂
    have hrow' (l : κ)(hl : l∈rows) : l∈labels := (Finset.mem_filter.mp hl).1
    have hround (l : κ)(hl : l∈rows)(j : Fin 4) : x l j≤u j ∧ u j≤x l j+width := by
      have hh:=exponent_bin_enclosure width hwidthbin (x l) j
      rw [(Finset.mem_filter.mp hl).2] at hh
      exact hh
    obtain ⟨l₀,hl₀,hkey₀⟩ := Finset.mem_image.mp hbin
    have hl₀' : l₀∈rows := Finset.mem_filter.mpr ⟨hl₀,hkey₀⟩
    have hq' : u 2≤Q := (hround l₀ hl₀' 2).2.trans (hq l₀ hl₀)
    have hs := he.2 reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
      (u 2) (u 1) a ((2*a-1)*u 3+rawError) allowance Kcontrol T i
      hq' (by linarith) ha' hKcontrol hT hinj rows st hQM hQη z hz hchar hpuncture hrow
      (fun l hl=>⟨(hzero l (hrow' l hl)).1.trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (hround l hl 2).1),(hzero l (hrow' l hl)).2⟩)
      (fun l hl=>hsupport l (hrow' l hl)) (fun l hl=>hnorm l (hrow' l hl))
      (fun l hl=>(hmissing l (hrow' l hl)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (hround l hl 1).1))
      hi hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁
      (fun l hl=>hf₁ l (hrow' l hl)) E R₂ pick t w σ v θ p Ds cap Araw
      hcap hmatches hscales hAraw hpadallow (fun l hl=>hf₂ l (hrow' l hl))
      (fun l hl=>hstateMask l (hrow' l hl)) (fun l hl=>hwidth l (hrow' l hl))
      (fun l hl=>hradial l (hrow' l hl)) (fun l hl=>hupper l (hrow' l hl))
      hw hwr hσlo hσhi
      (fun l hl=>hfreq l (hrow' l hl)) (fun l hl=>hplainfreq l (hrow' l hl))
      (fun l hl=>hW l (hrow' l hl)) (fun l hl=>hDs l (hrow' l hl))
      (fun l hl=>hdyad l (hrow' l hl)) (fun l hl=>hcontrol l (hrow' l hl)) (by
        intro l hl
        have hh:=hledger l (hrow' l hl)
        have hr:=mul_le_mul_of_nonneg_left (hround l hl 3).1 hd0
        linarith)
    calc
      _≤∑l∈rows,Z^(u 0)*shell l := Finset.sum_le_sum (fun l hl=>
        mul_le_mul_of_nonneg_right ((hcoeff l (hrow' l hl)).trans
          (Real.rpow_le_rpow_of_exponent_le hZ.le (hround l hl 0).1)) (hshell0 l))
      _=Z^(u 0)*(∑l∈rows,shell l) := (Finset.mul_sum _ _ _).symm
      _≤Z^(u 0)*(Cbase*Z^(u 1+u 2*unmarkedDensity (2*a-1)+loss+
          ((2*a-1)*u 3+rawError)+allowance)) := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hzpos.le _)
      _=_ := by
        dsimp only [highExponentValue,u]
        rw [mul_left_comm,←Real.rpow_add hzpos]
        rw [mul_assoc Cbase,←Real.rpow_add hzpos]
        congr 1
        congr 1
        ring
  have hh:=high_binned_sum labels x (fun l=>coeff l*shell l) width Bbox (2*a-1) Z
    (Cbase*Z^(loss+rawError+allowance)) target reserve hwidthbin hZ.le (by positivity) hδ hx hpoint hbin
  apply hh.trans_eq
  congr 1
  rw [mul_assoc,←Real.rpow_add hzpos]
  congr 1
  congr 1
  ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_binned_high_shell
