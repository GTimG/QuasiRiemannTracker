import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.ActualNaturalBatch
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.RawSlotUniformity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.RawCleanSlots
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.MaxRescale

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Record12518109GainWholeRaw
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState
open DetectorDictionaryInverseRawInitialGates Cycle61Moment
open Record12518109Natural Record12518109GainActual Record12518109GainDeletion
open Record12518109Gain
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The uniform root-hole comparison lands in the actual whole-family
batch at residual scale Z^q. Physical prime scales remain exactly Z^w. -/
theorem eventually_whole_raw_max_comparison
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (W : ℝ→ℂ) (lo hi Bmask Broot wmin : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀q : ℝ,∀hq : 0<q,
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      ∀hw : (∀s∈slots,wmin≤w s),
      ∀hσlo : (∀s∈slots,lo≤σ s),∀hσhi : (∀s∈slots,σ s≤hi),
      ∀hrow : (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤Z^q),
      ∀hnorm : (∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤Z^q),
      ∀hkeep : (∀u∈rows,∀j,initialKeep (cleanWholeBase M H hH η η₀ j)
        (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val),
      ∀hlarge : (∀s∈slots,∀j,
        ((deletedBase (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)<
          (Z^q)^(w s/q)),
      ∀(B : NZIdeal)(R : FreeRow→Ideal O),
      (B.val.absNorm:ℝ)≤Z^Broot →(∀u∈rows,R u≠0) →
      (∀u∈rows,((R u).absNorm:ℝ)≤Z^Bmask) →
      let batch := wholeNaturalBatch M H hH η η₀ bad W lo hi (Z^q) hWs rows slots
        (fun s=>w s/q) σ v t θ (fun s hs=>div_pos (hwmin.trans_le (hw s hs)) hq)
        hσlo hσhi hrow hnorm hkeep hlarge;
      let rawQ := fun u s=>naturalSlot
        (excluded (naturalRow (excluded η (wholeAnchorMask M H hH η₀))
          (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property).character (R u))
        (primePool M H 2 (Z^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (t u+v s) I) (Z^(w s));
      (∑u∈rows,∏s∈slots,max 1 (‖rawQ u s‖^2))≤
        (4:ℝ)^slots.card*(∑u∈rows,∏s∈slots,max 1 (‖batch.Q u s‖^2)) := by
  filter_upwards [eventually_raw_max_family_comparison (Slot:=Slot) W 1 2 lo hi Bmask Broot wmin
    (by norm_num) hWs hW.continuous hBmask hBroot hwmin] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro q hq rows slots w σ v t θ hw hσlo hσhi hrow hnorm hkeep hlarge B R hBN hR hRN batch rawQ
  have hp : ∀s∈slots,∀I∈primePool M H 2 (Z^(w s)),Prime I := by
    intro s hs I hI
    exact (Finset.mem_filter.mp hI).2.1
  have he := hZ.2 (excluded η (wholeAnchorMask M H hH η₀))
    (fun s=>relativeCharacter M H hH η₀ (θ s)) B R rows slots hR hRN hBN
    (fun s=>primePool M H 2 (Z^(w s))) hp w σ v t hw hσlo hσhi
  dsimp only [batch,rawQ,wholeNaturalBatch]
  simpa only [prime_scale_rescale Z q _ (by linarith : 0≤Z) hq] using he

/-- Original raw base to clean fixed-conductor core, including the fixed
anchor deletion in the proved error. -/
theorem eventually_whole_original_raw_max_comparison
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (W : ℝ→ℂ) (lo hi Bmask Broot wmin : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀q : ℝ,∀hq : 0<q,
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      ∀hw : (∀s∈slots,wmin≤w s),
      ∀hσlo : (∀s∈slots,lo≤σ s),∀hσhi : (∀s∈slots,σ s≤hi),
      ∀hrow : (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤Z^q),
      ∀hnorm : (∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤Z^q),
      ∀hkeep : (∀u∈rows,∀j,initialKeep (cleanWholeBase M H hH η η₀ j)
        (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val),
      ∀hlarge : (∀s∈slots,∀j,
        ((deletedBase (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)<
          (Z^q)^(w s/q)),
      ∀(B : NZIdeal)(R : FreeRow→Ideal O),
      (B.val.absNorm:ℝ)≤Z^Broot →(∀u∈rows,R u≠0) →
      (∀u∈rows,((R u).absNorm:ℝ)≤Z^Bmask) →
      let batch := wholeNaturalBatch M H hH η η₀ bad W lo hi (Z^q) hWs rows slots
        (fun s=>w s/q) σ v t θ (fun s hs=>div_pos (hwmin.trans_le (hw s hs)) hq)
        hσlo hσhi hrow hnorm hkeep hlarge;
      let rawQ := fun u s=>naturalSlot
        (excluded (naturalRow η
          (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property).character (R u))
        (primePool M H 2 (Z^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (t u+v s) I) (Z^(w s));
      (∑u∈rows,∏s∈slots,max 1 (‖rawQ u s‖^2))≤
        (4:ℝ)^slots.card*(∑u∈rows,∏s∈slots,max 1 (‖batch.Q u s‖^2)) := by
  filter_upwards [eventually_raw_clean_slot_comparison (wholeAnchorMask M H hH η₀)
    (wholeAnchorMask_ne_zero M H hH η₀) W 1 2 lo hi Bmask Broot wmin
    (by norm_num) hWs hW.continuous hBmask hBroot hwmin] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro q hq rows slots w σ v t θ hw hσlo hσhi hrow hnorm hkeep hlarge B R hBN hR hRN batch rawQ
  apply raw_max_fiber_comparison rows slots rawQ batch.Q
  intro u hu s hs
  have hp : ∀I∈primePool M H 2 (Z^(w s)),Prime I := fun I hI=>(Finset.mem_filter.mp hI).2.1
  have he := hZ.2 η (relativeCharacter M H hH η₀ (θ s))
    (excluded (naturalRow η (sixthFrequencyEquiv (u,B)).val
      (sixthFrequencyEquiv (u,B)).property).character (R u)) u B (R u)
    (hR u hu) (hRN u hu) hBN (fun _=>rfl) (primePool M H 2 (Z^(w s))) hp
    (w s) (σ s) (t u+v s) 0 (hw s hs) (hσlo s hs) (hσhi s hs)
  dsimp only [batch,rawQ,wholeNaturalBatch]
  simpa only [heightCoefficient_zero,prime_scale_rescale Z q _ (by linarith : 0≤Z) hq] using he

end
end OAI.SevenEighths.Record12518109GainWholeRaw
