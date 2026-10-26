import Candidate.Cycle63.Marked.WholeCoreGates
import Candidate.Cycle63.Marked.DeletionRawPadded
import Candidate.Cycle63.Marked.DeletionRawSlots
import Candidate.Cycle63.Marked.WholeFamilyZeros

/- Original module: Candidate.Cycle63.Marked.WholePaddedCore. -/
section

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual padded core source count in physical slot widths. The finite
exception set, modulus padding, embedding cap, inverse conductor threshold,
and both buffered-maximum transports are proved inside this adapter. -/
theorem actual_whole_padded_core_weighted {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤ M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss : ℝ)
    (dmin dmax τ ε e κw ηw pad wmin : ℝ) (I : ℕ)
    (hpad : 0< pad) (hwmin : 0< wmin) (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0< bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hΔ0 : 0≤Δ) (hΔ : Δ≤1/1000) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃E : Finset FreeRow,∃meshmax : ℝ,0< meshmax ∧ ∃J : ℕ,∃C : ℝ,0< C ∧
      ∀ᶠU : ℝ in atTop,1< U ∧ ∀Y d : ℝ,dmin≤ d → d≤ dmax → U^d=Y*U^pad →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀u∈rows,u∉E) → (∀u∈rows,rowNorm u≤ Y) →
      (∀s∈slots,wmin≤ w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤ hi) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤ I →
      17/25≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ meshmax → binWidth≤(2*a-1)/2 →
      (∀s∈slots,w s≤ mesh*d) →
      0≤ height → 2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ≤ height →
      (∀s∈slots,|v s|≤ height) → (∀u∈rows,|t u|≤ height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*U^τ)< a+2*e) →
      (∀u : rows,a≤ zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*U^τ)) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH η η₀ W U w σ v t θ u s‖
        ≤(U^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH η η₀ W U w σ v t θ u s‖)^2)≤
        C*(1+height)^J*
        (U^((2*a-1+2*binWidth)*(∑s∈slots,w s)-(224/1755)*min (∑s∈slots,w s) ((13/400)*d)+
          dmax*(156*ε+mesh+εm+ηloss)+pad*VariableSupply.density (2*a-1))*
          Y^VariableSupply.density (2*a-1)) := by
  obtain ⟨E,hE⟩ := whole_core_exception_set M H hH η η₀ bad hbad0 hbadTop hbad72
  obtain ⟨meshmax,hm,J,C,hC,hcount⟩ := actual_whole_max_weighted (Slot:=Slot) M H hH
    η η₀ bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth ηloss
    dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he'
    hκw hκw' hηw hbudget hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨E,meshmax,hm,J,C,hC,?_⟩
  filter_upwards [hcount,eventually_whole_core_norm_caps M H hH η η₀ pad hpad,
    eventually_whole_core_inverse_large M H hH η η₀ wmin hwmin]
    with U hcount hnorms hlarge
  refine ⟨hcount.1,?_⟩
  intro Y d hd hd' hbase rows slots w σ v t θ hrows hrow hw hlo hhi
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht
    hχ hnext hcurrent hQ
  have hUp : 0< U := zero_lt_one.trans hcount.1
  have hdp : 0< d := hdmin.trans_le hd
  have hscale (s : Slot) : (U^d)^(w s/d)=U^(w s) := by
    rw [←Real.rpow_mul hUp.le,mul_div_cancel₀ _ hdp.ne']
  have hYs : 0< Y*U^pad := hbase ▸ Real.rpow_pos_of_pos hUp d
  have hY : 0< Y := (mul_pos_iff.mp hYs).elim (fun h=>h.1)
    (fun h=>False.elim ((not_lt_of_ge (Real.rpow_nonneg hUp.le _)) h.2))
  have he := hcount.2 d hd hd' rows slots (fun s=>w s/d) σ v t θ
    (fun s hs=>div_pos (hwmin.trans_le (hw s hs)) hdp) hlo hhi
    (fun u hu=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).1)
    (fun u hu=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.1)
    (fun u hu=>(hE u).mp (hrows u hu))
    (fun s hs j=>by rw [hscale];exact hlarge.2 (w s) (hw s hs) j)
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin'
    (fun s hs=>(div_le_iff₀ hdp).mpr (hwm s hs)) hh hf hv ht hχ hnext hcurrent
    (fun u hu j=>by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.2 j)
    (fun u hu s hs=>by rw [wholeCleanSlot_rescale M H hH η η₀ W U d hUp hdp.ne',hscale];exact hQ u hu s hs)
  simp only [wholeCleanSlot_rescale M H hH η η₀ W U d hUp hdp.ne',←Finset.sum_div] at he
  have heq : VariableSupply.density (2*a-1)+(2*a-1)*((∑s∈slots,w s)/d)-
      (224/1755)*min ((∑s∈slots,w s)/d) (13/400)+
      156*ε+mesh+εm+2*binWidth*((∑s∈slots,w s)/d)+ηloss =
      VariableSupply.density (2*a-1)+(2*a-1+2*binWidth)*((∑s∈slots,w s)/d)-
        (224/1755)*min ((∑s∈slots,w s)/d) (13/400)+(156*ε+mesh+εm+ηloss) := by
    ring
  rw [heq] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Deletion26.rescaled_marked_power_padded U Y d d dmax pad
    (VariableSupply.density (2*a-1)) (2*a-1+2*binWidth) (∑s∈slots,w s)
    (224/1755) (13/400) (156*ε+mesh+εm+ηloss) hcount.1.le hY hdp le_rfl hd' hbase
    (by norm_num) (by norm_num) (by positivity)

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.actual_whole_padded_core_weighted
end

/- Original module: Candidate.Cycle63.Marked.DeletionRawCleanSlots. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentSecondHeightFamily HeckePrimeAnnular Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- The arbitrary fixed positive deletion tolerance used to compare the
raw masked row and the independently masked common detector core. -/
theorem eventually_annular_deletion_tolerance (W : ℝ→ℂ) (a b lo hi Bmask wmin err : ℝ)
    (ha : 0< a) (hWs : Function.support W⊆Icc a b) (hW : Continuous W)
    (hBmask : 0≤ Bmask) (hwmin : 0< wmin) (herr : 0< err) :
    ∀ᶠU : ℝ in atTop,1< U ∧
      ∀(χ ν : Character)(R : Ideal O),R≠0 → (R.absNorm : ℝ)≤ U^Bmask →
      ∀pool : Finset (Ideal O),(∀I∈pool,Prime I) →
      ∀w σ v t : ℝ,wmin≤ w → lo≤σ → σ≤ hi →
      let β:=heightCoefficient (fun I=>idealCoeff ν I*annularWeight W (U^w) σ v I) t
      ‖naturalSlot (excluded χ R) pool β (U^w)-naturalSlot χ pool β (U^w)‖≤ err := by
  obtain ⟨C,hC,hdel⟩ := annular_slot_deletion W a b lo hi Bmask (wmin/4)
    ha hWs hW hBmask (by positivity)
  have hlarge := (tendsto_rpow_atTop (show 0< wmin/4 by positivity)).eventually
    (eventually_ge_atTop (C/err))
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hlarge hU
  refine ⟨hU,?_⟩
  intro χ ν R hR hRN pool hp w σ v t hw hσlo hσhi β
  apply (hdel U hU.le χ ν R hR hRN pool hp w σ v t hσlo hσhi).trans
  have hUp : 0< U := zero_lt_one.trans hU
  calc
    C*U^(-w/2+wmin/4)≤ C*U^(-(wmin/4)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)) hC.le
    _ ≤ err := by
      rw [Real.rpow_neg hUp.le,←div_eq_mul_inv]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hUp _)).mpr
      exact (div_le_iff₀ herr).mp hlarge |>.trans_eq (mul_comm _ _)

/-- The actual raw slot and the clean common core slot differ by at most
one half. Both the moving geometric holes and the fixed anchor mask are
removed explicitly; no coprimality condition between those masks is used. -/
theorem eventually_raw_clean_slot_comparison (A : Ideal O) (hA : A≠0)
    (W : ℝ→ℂ) (a b lo hi Bmask Broot wmin : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (hW : Continuous W)
    (hBmask : 0≤ Bmask) (hBroot : 0≤ Broot) (hwmin : 0< wmin) :
    ∀ᶠU : ℝ in atTop,1< U ∧
      ∀(η ν χ : Character)(u : FreeRow)(B : NZIdeal)(R : Ideal O),R≠0 →
      (R.absNorm : ℝ)≤ U^Bmask → (B.val.absNorm : ℝ)≤ U^Broot →
      (∀I,idealCoeff χ I=idealCoeff
        (excluded (naturalRow η (sixthFrequencyEquiv (u,B)).val
          (sixthFrequencyEquiv (u,B)).property).character R) I) →
      ∀pool : Finset (Ideal O),(∀I∈pool,Prime I) →
      ∀w σ v t : ℝ,wmin≤ w → lo≤σ → σ≤ hi →
      let β:=heightCoefficient (fun I=>idealCoeff ν I*annularWeight W (U^w) σ v I) t
      ‖naturalSlot χ pool β (U^w)-
        naturalSlot (naturalRow (excluded η A) u.val u.property.1).character pool β (U^w)‖≤1/2 := by
  filter_upwards [eventually_annular_deletion_tolerance W a b lo hi (Broot+Bmask) wmin (1/4)
      ha hWs hW (add_nonneg hBroot hBmask) hwmin (by norm_num),
    eventually_annular_deletion_tolerance W a b lo hi 1 wmin (1/4)
      ha hWs hW (by norm_num) hwmin (by norm_num),
    eventually_ge_atTop (A.absNorm:ℝ)] with U hraw hanchor hAN
  refine ⟨hraw.1,?_⟩
  intro η ν χ u B R hR hRN hBN hcoeff pool hp w σ v t hw hσlo hσhi β
  let F := naturalRow η u.val u.property.1
  let Fr := naturalRow η (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property
  have hg : ConcretePrimeRowBridge.idealGenerator B.val≠0 :=
    ConcretePrimeRowBridge.idealGenerator_ne_zero B.val B.property
  have hrawcoeff (I : Ideal O) : idealCoeff χ I=idealCoeff (excluded F.character (B.val*R)) I := by
    rw [hcoeff I]
    have hh:=naturalRow_sixth_masked_ideal F (ConcretePrimeRowBridge.idealGenerator B.val) hg Fr R hR I
    rwa [ConcretePrimeRowBridge.span_idealGenerator] at hh
  have hclean := naturalSlot_congr_ideal
    (naturalRow (excluded η A) u.val u.property.1).character (excluded F.character A)
    (natural_excluded_base_coefficients η A hA u.val u.property.1) pool β (U^w)
  rw [naturalSlot_congr_ideal χ _ hrawcoeff,hclean]
  have h1:=hraw.2 F.character ν (B.val*R) (mul_ne_zero B.property hR)
    (holes_with_root_norm B.val R U Broot Bmask (zero_lt_one.trans hraw.1) hBN hRN)
    pool hp w σ v t hw hσlo hσhi
  have h2:=hanchor.2 F.character ν A hA (by simpa using hAN)
    pool hp w σ v t hw hσlo hσhi
  have ht:=dist_triangle (naturalSlot (excluded F.character (B.val*R)) pool β (U^w))
    (naturalSlot F.character pool β (U^w)) (naturalSlot (excluded F.character A) pool β (U^w))
  simp only [dist_eq_norm] at ht
  rw [norm_sub_rev (naturalSlot F.character pool β (U^w))] at ht
  linarith

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.eventually_annular_deletion_tolerance
#print axioms OAI.SevenEighths.Deletion26.eventually_raw_clean_slot_comparison
end

/- Original module: Candidate.Cycle63.Marked.WholeRawGates. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily ProbePhysical LocalMoment Cycle63Moment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def wholeRawSlot {Slot : Type} (η₀ : Character) (W : ℝ→ℂ) (U : ℝ)
    (w σ v : Slot→ℝ) (t : NonzeroFrequency→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (χ : NonzeroFrequency→Character) (u : NonzeroFrequency) (s : Slot) : ℂ :=
  naturalSlot (χ u) (primePool M H 2 (U^(w s)))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I) (t u)) (U^(w s))

/-- A lower maximum in the actual whole family supplies the literal
oriented zero row consumed by the unconditional large-root estimate. -/
theorem whole_maximum_to_actual_zero_row (η η₀ χ : Character) (u : NonzeroFrequency)
    (R : Ideal O) (hR : R≠0)
    (hcoeff : ∀K,idealCoeff χ K=idealCoeff (excluded (naturalRow η u.val u.property).character R) K)
    (hχ : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1)
    (a T height : ℝ) (ha : 33/40≤ a) (hmax : a≤ zeroMaximum (wholeSourceFamily M H hH η₀ χ) hχ T)
    (hT : T≤ height) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases (cleanWholeBase M H hH η η₀)).data
      (fun _=>false) a height u := by
  obtain ⟨hc,he⟩ := whole_family_clean_maximum M H hH η η₀ χ u.val u.property R hR hcoeff hχ
  have hm := hmax.trans_eq (he T).symm
  obtain ⟨j,s,hz,ht,hs⟩ := maximum_attained _ hc T (by linarith)
  apply natural_zero_to_literal_dictionary _ (fun _=>false) a height ha u
  refine ⟨j,s,?_,?_,?_,ht.trans hT⟩
  · simpa only [Bool.false_eq_true,ite_false,naturalRawFamily,cleanWholeBase] using hz
  · exact Or.inr (hc j)
  · rw [hs];exact hm

/-- Each row of a sixth-root fiber is an actual member of the original
raw finite population. -/
theorem sixth_fiber_raw_mem (R : Finset NonzeroFrequency) (B : NZIdeal)
    (u : FreeRow) (hu : u∈sixthFreeFiber R B) : sixthFrequencyEquiv (u,B)∈R := by
  obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨hp,hpB⟩ := Finset.mem_filter.mp hp
  have he : p=(u,B) := Prod.ext hpu hpB
  subst p
  exact (mem_sixthPairs R (u,B)).mp hp

/-- Actual raw norm bounds give the unpadded sixth-free core window. -/
theorem sixth_fiber_core_norm (R : Finset NonzeroFrequency) (B : NZIdeal) (U : ℝ)
    (hrow : ∀u∈R,rawFrequencyNorm u≤ U) (u : FreeRow) (hu : u∈sixthFreeFiber R B) :
    rowNorm u≤ U/(B.val.absNorm : ℝ)^6 := by
  have hh:=hrow _ (sixth_fiber_raw_mem R B u hu)
  rw [raw_sixth_norm] at hh
  have hB : 0<(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  exact (le_div_iff₀ (pow_pos hB _)).mpr hh

/-- The same actual row character has a literal free-core presentation,
with the sixth root added to its original moving hole ideal. -/
theorem sixth_core_mask_coefficients (η χ : Character) (u : FreeRow) (B : NZIdeal)
    (R : Ideal O) (hR : R≠0)
    (hcoeff : ∀K,idealCoeff χ K=idealCoeff
      (excluded (naturalRow η (sixthFrequencyEquiv (u,B)).val
        (sixthFrequencyEquiv (u,B)).property).character R) K) :
    ∀K,idealCoeff χ K=idealCoeff (excluded (naturalRow η u.val u.property.1).character (B.val*R)) K := by
  intro K
  rw [hcoeff K]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero B.val B.property
  have hh:=Deletion26.naturalRow_sixth_masked_ideal (naturalRow η u.val u.property.1)
    (ConcretePrimeRowBridge.idealGenerator B.val) hg
    (naturalRow η (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property) R hR K
  rwa [ConcretePrimeRowBridge.span_idealGenerator] at hh

/-- A uniform individual amplitude cap yields the full raw max-product
envelope, retaining the sum of physical widths exactly. -/
theorem max_product_power_envelope {Slot : Type*} (slots : Finset Slot) (Q : Slot→ℂ)
    (U δ bw : ℝ) (w : Slot→ℝ) (hU : 1≤ U) (hδ : 0≤δ/2+bw)
    (hw : ∀s∈slots,0≤ w s) (hQ : ∀s∈slots,‖Q s‖≤(U^(w s))^(δ/2+bw)) :
    (∏s∈slots,max 1 ‖Q s‖)^2≤ U^((δ+2*bw)*(∑s∈slots,w s)) := by
  have hUp : 0< U := zero_lt_one.trans_le hU
  have hmax (s : Slot) (hs : s∈slots) : max 1 ‖Q s‖≤(U^(w s))^(δ/2+bw) := by
    apply max_le _ (hQ s hs)
    exact Real.one_le_rpow (Real.one_le_rpow hU (hw s hs)) hδ
  have hprod := pow_le_pow_left₀ (Finset.prod_nonneg (fun s _=>le_trans zero_le_one (le_max_left _ _)))
    (Finset.prod_le_prod₀ (fun _ _=>le_trans zero_le_one (le_max_left _ _)) hmax) 2
  apply hprod.trans_eq
  simp_rw [←Real.rpow_mul hUp.le]
  rw [←Real.rpow_sum_of_pos hUp,←Real.rpow_natCast,←Real.rpow_mul hUp.le]
  congr 1
  rw [←Finset.sum_mul]
  ring

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.whole_maximum_to_actual_zero_row
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.sixth_core_mask_coefficients
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.max_product_power_envelope
end
