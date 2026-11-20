/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual P6 short factor and attaining rows, in the original finite sums. -/
import Candidate.C092.transport.TerminalActualInverseApplyProfiles
import Candidate.C092.transport.SourceInverseP6CloseCalibration
import Candidate.C092.transport.RegularColoredTerminalLeafGuards
set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualInverseApply
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.TerminalActualRow
local notation "O" => HeckeFamily.O

/-- No independent ordinary height is reset in the source energy. The
native sigma-zero profile merely moves that height into the smooth factor. -/
theorem actual_short_norm {U Bmask bΦ : ℝ} (s : NaturalState U Bmask bΦ)
    (u : FreeRow) (hu : s.radial.keep u.val) (W : ℝ→ℂ) (A B : ℝ)
    (hA : 0<A) (hs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (t Y : ℝ) (hY : 0<Y) :
    ‖original s.character s.mask 1 u.val (twistProfile W 0 t) 0 Y‖=
      ‖original s.character s.mask 1 u.val W t Y‖ := by
  rw [TerminalActualRow.original_short_norm s u hu W A B hA hs hW t Y hY,
    natural_plain_eq_original s _ W Y 0 t hY]

/-- This is the literal original energy equality on any retained finite
subclass, with arbitrary row-dependent opened profiles and heights. -/
theorem actual_short_energy {U Bmask bΦ : ℝ} (s : NaturalState U Bmask bΦ)
    (rows : Finset FreeRow) (hkeep : ∀u∈rows,s.radial.keep u.val)
    (W : FreeRow→ℝ→ℂ) (A B t : FreeRow→ℝ) (Y : ℝ) (hY : 0<Y)
    (hA : ∀u∈rows,0<A u) (hs : ∀u∈rows,Function.support (W u)⊆Icc (A u) (B u))
    (hW : ∀u∈rows,ContDiff ℝ ∞ (W u)) (long mark : FreeRow→ℂ) :
    (∑u∈rows,‖long u*original s.character s.mask 1 u.val (twistProfile (W u) 0 (t u)) 0 Y*mark u‖^2)=
    (∑u∈rows,‖long u*original s.character s.mask 1 u.val (W u) (t u) Y*mark u‖^2) := by
  apply Finset.sum_congr rfl
  intro u hu
  simp only [norm_mul,actual_short_norm s u (hkeep u hu) (W u) (A u) (B u)
    (hA u hu) (hs u hu) (hW u hu) (t u) Y hY]

/-- The actual source attainer is selected only after the frozen ticket
class. Calibration is eventual and precedes all original row arrays. -/
theorem actual_class_descriptor_cover {Slot Key : Type*} [Fintype Slot] [DecidableEq Key]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Icc (1:ℝ) 2)
    {buffer Cslot : ℝ} (hb : 0<buffer) (hC : 0<Cslot) :
    ∀ᶠ U : ℝ in atTop,1<U ∧ ∀(η η₀ : Character)
      (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ)
      (rows : Finset FreeRow) (key : rows→Key) (tag : Key),
      (∀j,0≤w j) →
      (∀u∈classRows rows key tag,0 < measured M H hH η η₀ W U (Cslot*U^buffer) θ w v t u) →
      ∀u∈classRows rows key tag,∃jd,u∈descriptorRows M H hH (classRows rows key tag)
        η η₀ W U (Cslot*U^buffer) (buffer/2) θ w v t jd := by
  filter_upwards [actual_calibrated_descriptor_cover (Slot:=Slot) M H hH W hW hWs hb hC] with U hU
  refine ⟨hU.1,?_⟩
  intro η η₀ θ w v t rows key tag hw hpositive
  exact hU.2 η η₀ θ w v t (classRows rows key tag) hw hpositive

#print axioms actual_short_norm
#print axioms actual_short_energy
#print axioms actual_class_descriptor_cover
end
end QRH.Cycle092.TerminalActualInverseApply
