import Candidate.Uneven.MixedBootstrapNaturalBatch
import Candidate.Cycle63.Marked.DeletionFiniteExceptions
import Candidate.Cycle63.Marked.NaturalSlotPhase
import Candidate.Uneven.BootstrapCore
import Candidate.Cycle63.Marked.WholeCoreGates
import Candidate.Uneven.MixedBootstrapWholeBuffered
import Candidate.Cycle63.Marked.DeletionRawPadded

/- Original module: Candidate.Uneven.MixedBootstrapNaturalCoreGates. -/
section
/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.MixedBootstrapNaturalBases
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open Cycle63Moment Cycle63MarkedPlain CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The exceptional free cores are one fixed finite set, chosen before
the scale, every root ideal, and every moving amplitude or zero label. -/
theorem whole_core_exception_set (ηcoarse η₀ : Character) (u₀ : O) (hu₀ : u₀≠0) (R₀ : Ideal O) (bad : WholeSourceIndex M H→Ideal O)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)}) :
    ∃E : Finset FreeRow,∀u : FreeRow,u∉E ↔ ∀j,initialKeep (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j)
      (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val :=
  Deletion26.fixed_initial_exception_union (base M H hH ηcoarse η₀ u₀ hu₀ R₀)
    (fun j=> internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) hbad0 hbadTop hbad72

/-- A fixed positive padding absorbs all natural conductor constants.
The original row norm alone supplies the embedding and clean modulus caps. -/
theorem eventually_whole_core_norm_caps (ηcoarse η₀ : Character) (u₀ : O) (hu₀ : u₀≠0) (R₀ : Ideal O) (pad : ℝ) (hpad : 0< pad) :
    ∀ᶠ U : ℝ in atTop,1< U ∧ ∀(Y : ℝ)(u : FreeRow),rowNorm u≤ Y →
      ((Ideal.span {u.val}).absNorm:ℝ)≤ Y*U^pad ∧
      ‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤ Y*U^pad ∧
      ∀j,(naturalRow (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u.val u.property.1).character.modulus.absNorm≤ Y*U^pad := by
  let D := FixedUnmarkedDictionary.ofBases (base M H hH ηcoarse η₀ u₀ hu₀ R₀)
  obtain ⟨K,hK,hmod⟩ := D.natural_conductor_bound
  have hlarge : ∀ᶠU : ℝ in atTop,K≤ U^pad :=
    (tendsto_rpow_atTop hpad).eventually (eventually_ge_atTop K)
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hKU hU
  refine ⟨hU,?_⟩
  intro Y u hu
  have hY : 0≤ Y := (zero_le_one.trans (rowNorm_ge_one u)).trans hu
  have hnorm : rowNorm u≤ Y*U^pad :=
    hu.trans (le_mul_of_one_le_right hY (hK.trans hKU))
  refine ⟨hnorm,?_,?_⟩
  · simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,rowNorm] using hnorm
  · intro j
    apply (hmod u j).trans
    calc
      K*rowNorm u ≤ K*Y := mul_le_mul_of_nonneg_left hu (zero_le_one.trans hK)
      _ ≤ _ := by nlinarith

/-- A positive lower physical width eventually puts every slot beyond
all fixed deleted detector conductors, uniformly over the whole dictionary. -/
theorem eventually_whole_core_inverse_large (ηcoarse η₀ : Character) (u₀ : O) (hu₀ : u₀≠0) (R₀ : Ideal O) (wmin : ℝ) (hwmin : 0< wmin) :
    ∀ᶠU : ℝ in atTop,1< U ∧ ∀w : ℝ,wmin≤ w → ∀j : WholeSourceIndex M H,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase
        (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)< U^w := by
  let K : ℝ := ∑j : WholeSourceIndex M H,
    ((DetectorDictionaryInverseRawInitialGates.deletedBase
      (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)
  have hlarge : ∀ᶠU : ℝ in atTop,K< U^wmin :=
    (tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop K)
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hlarge hU
  refine ⟨hU,?_⟩
  intro w hw j
  have hj : ((DetectorDictionaryInverseRawInitialGates.deletedBase
      (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)≤ K :=
    by
      dsimp only [K]
      exact Finset.single_le_sum (f := fun j : WholeSourceIndex M H=>
        ((DetectorDictionaryInverseRawInitialGates.deletedBase
          (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ))
        (fun _ _=> by positivity) (Finset.mem_univ j)
  exact (hj.trans_lt hlarge).trans_le (Real.rpow_le_rpow_of_exponent_le hU.le hw)


end
end OAI.SevenEighths.MixedBootstrapNaturalBases
end

/- Original module: Candidate.Uneven.BootstrapRescale. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem rescaled_power_padded
    (U Y D Dmax pad d q S loss : ℝ)
    (hU : 1 ≤ U) (hY : 0< Y) (hD : 0< D) (hDmax : D ≤ Dmax)
    (hbase : U^D=Y*U^pad) (hloss : 0 ≤ loss) :
    (U^D)^(count d (S/D)+q*(S/D)+loss) ≤
      U^(q*S-physicalGain d S D+Dmax*loss+pad*Saturated.rho d)*Y^(Saturated.rho d) := by
  have hUp : 0< U := zero_lt_one.trans_le hU
  have hYeq : Y=U^(D-pad) := by
    rw [Real.rpow_sub hUp]
    apply (eq_div_iff (Real.rpow_pos_of_pos hUp pad).ne').mpr
    exact hbase.symm
  have hgain : D*physicalGain d (S/D) 1=physicalGain d S D := FiniteGain.gain_rescale hD
  have hexp : D*(count d (S/D)+q*(S/D)+loss)=
      q*S-physicalGain d S D+D*loss+D*Saturated.rho d := by
    have hcancel : D*(S/D)=S := mul_div_cancel₀ _ hD.ne'
    unfold count
    linear_combination q*hcancel-hgain
  rw [←Real.rpow_mul hUp.le,hexp,hYeq,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_right hDmax hloss
  linarith

theorem root_power_transport {d U Y D q pad S A r loss : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50) (hU : 1 ≤ U) (hY : 1 ≤ Y)
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq : q ≤ 1) (hpad : 0 ≤ pad) (hloss : 0 ≤ loss)
    (hbase : Y=U^(D*q)) :
    U^(A-physicalGain d S (D*q+pad))*Y^r ≤
      U^(A+(3/200)*D-physicalGain d S D)*Y^(r+loss-3/200) := by
  have hUp : 0< U := zero_lt_one.trans_le hU
  have hg := physicalGain_root hd0 hd hS hD hq0 hq hpad
  calc
    _ ≤ U^(A-physicalGain d S (D*q+pad))*Y^(r+loss) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by positivity)
    _ ≤ _ := by
      rw [hbase,←Real.rpow_mul hUp.le,←Real.rpow_mul hUp.le,
        ←Real.rpow_add hUp,←Real.rpow_add hUp]
      apply Real.rpow_le_rpow_of_exponent_le hU
      nlinarith only [hg]

theorem exception_envelope {d U Y D S A r : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50) (hU : 1 ≤ U) (hY : 1 ≤ Y)
    (hD : 0 ≤ D) (hr : 3/200 ≤ r) :
    U^A ≤ U^(A+(3/200)*D-physicalGain d S D)*Y^(r-3/200) := by
  have hg := physicalGain_cap (S:=S) hd0 hd hD
  calc
    _ ≤ U^(A+(3/200)*D-physicalGain d S D) :=
      Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    _ ≤ _ := le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hY (by linarith))

end Sil.Uneven.Bootstrap
end

/- Original module: Candidate.Uneven.MixedBootstrapWholePadded. -/
section
/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI.SevenEighths.MixedBootstrapPlain
open OAI.SevenEighths.Cycle63MarkedPlain
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
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤  H)

/-- Actual padded core source count in physical slot widths. The finite
exception set, modulus padding, embedding cap, inverse conductor threshold,
and both buffered-maximum transports are proved inside this adapter. -/
theorem actual_whole_padded_core_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j ≤  M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j) ≤  Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ Δ εm binWidth ηloss : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2  ≤  bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hΔ0 : 0 ≤  Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ) ≤  HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta  ≤  7/8) :
    ∃E : Finset FreeRow,∃J : ℕ,∀(dmin dmax τ ε e κw ηw pad wmin : ℝ) (I : ℕ)
    (hpad : 0< pad) (hwmin : 0< wmin) (hdmin : 0< dmin) (hdmax : dmin ≤  dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε ≤ 1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw ≤ 1) (hηw : 0 ≤  ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw ≤  ε/2),
      ∃C : ℝ,0< C ∧
      ∀ᶠU : ℝ in atTop,1< U ∧ ∀Y d : ℝ,dmin ≤  d → d ≤  dmax → U^d=Y*U^pad →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀u∈rows,u∉E) → (∀u∈rows,rowNorm u ≤  Y) →
      (∀s∈slots,wmin ≤  w s) → (∀s∈slots,(33/50:ℝ) ≤  σ s) → (∀s∈slots,σ s ≤  (33/50:ℝ)) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow (excluded F₀.character R₀) u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i ≤  I →
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      0 ≤  mesh → mesh ≤  markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈slots,w s ≤  mesh*d) →
      0 ≤  height → 2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ ≤  height →
      (∀s∈slots,|v s| ≤  height) → (∀u∈rows,|t u| ≤  height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*U^τ)< a+2*e) →
      (∀u : rows,a ≤  zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*U^τ)) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH (excluded F₀.character R₀) η₀ W U w σ v t θ u s‖
         ≤ (U^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH (excluded F₀.character R₀) η₀ W U w σ v t θ u s‖)^2) ≤ 
        C*(1+height)^J*
        (U^((2*a-1+2*binWidth)*(∑s∈slots,w s)-Sil.Uneven.Bootstrap.physicalGain (2*a-1) (∑s∈slots,w s) d+
          dmax*(402*ε+mesh+εm+ηloss)+pad*Sil.Uneven.Saturated.rho (2*a-1))*
          Y^Sil.Uneven.Saturated.rho (2*a-1)) := by
  obtain ⟨E,hE⟩ := MixedBootstrapNaturalBases.whole_core_exception_set M H hH ηcoarse η₀ u₀ hu₀ R₀ bad hbad0 hbadTop hbad72
  obtain ⟨J,hcount⟩ := actual_whole_max_weighted_fixedmesh (Slot:=Slot) M H hH
    ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ bad hbadM hbad0 hbadTop hbad72 Sbad hbad setup W bΦ Δ εm binWidth ηloss
    hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hβhi
  refine ⟨E,J,?_⟩
  intro dmin dmax τ ε e κw ηw pad wmin I hpad hwmin hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩ := hcount dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,MixedBootstrapNaturalBases.eventually_whole_core_norm_caps M H hH ηcoarse η₀ u₀ hu₀ R₀ pad hpad,
    MixedBootstrapNaturalBases.eventually_whole_core_inverse_large M H hH ηcoarse η₀ u₀ hu₀ R₀ wmin hwmin]
    with U hcount hnorms hlarge
  refine ⟨hcount.1,?_⟩
  intro Y d hd hd' hbase rows slots w σ v t θ hrows hrow hw hlo hhi
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hmeshaux hbin' hwm hh hf hv ht
    hχ hnext hcurrent hQ
  have hUp : 0< U := zero_lt_one.trans hcount.1
  have hdp : 0< d := hdmin.trans_le hd
  have hscale (s : Slot) : (U^d)^(w s/d)=U^(w s) := by
    rw [←Real.rpow_mul hUp.le,mul_div_cancel₀ _ hdp.ne']
  have hYs : 0< Y*U^pad := hbase ▸ Real.rpow_pos_of_pos hUp d
  have hY : 0< Y := (mul_pos_iff.mp hYs).elim (fun h=> h.1)
    (fun h=> False.elim ((not_lt_of_ge (Real.rpow_nonneg hUp.le _)) h.2))
  have he := hcount.2 d hd hd' rows slots (fun s=> w s/d) σ v t θ
    (fun s hs=> div_pos (hwmin.trans_le (hw s hs)) hdp) hlo hhi
    (fun u hu=> by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).1)
    (fun u hu=> by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.1)
    (fun u hu=>(hE u).mp (hrows u hu))
    (fun s hs j=> by rw [hscale];exact hlarge.2 (w s) (hw s hs) j)
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hmeshaux hbin'
    (fun s hs=>(div_le_iff₀ hdp).mpr (hwm s hs)) hh hf hv ht hχ hnext hcurrent
    (fun u hu j=> by rw [hbase];exact (hnorms.2 Y u (hrow u hu)).2.2 j)
    (fun u hu s hs=> by rw [wholeCleanSlot_rescale M H hH (excluded F₀.character R₀) η₀ W U d hUp hdp.ne',hscale];exact hQ u hu s hs)
  simp only [wholeCleanSlot_rescale M H hH (excluded F₀.character R₀) η₀ W U d hUp hdp.ne',←Finset.sum_div] at he
  have heq : Sil.Uneven.Bootstrap.count (2*a-1) ((∑s∈slots,w s)/d)+(2*a-1)*((∑s∈slots,w s)/d)+
      402*ε+mesh+εm+2*binWidth*((∑s∈slots,w s)/d)+ηloss =
      Sil.Uneven.Bootstrap.count (2*a-1) ((∑s∈slots,w s)/d)+(2*a-1+2*binWidth)*((∑s∈slots,w s)/d)+(402*ε+mesh+εm+ηloss) := by
    ring
  rw [heq] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Sil.Uneven.Bootstrap.rescaled_power_padded U Y d dmax pad
    (2*a-1) (2*a-1+2*binWidth) (∑s∈slots,w s) (402*ε+mesh+εm+ηloss)
    hcount.1.le hY hdp hd' hbase (by positivity)

end
end OAI.SevenEighths.MixedBootstrapPlain
end
