import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Gate
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceFamily
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open ConcreteTraceCRT LowBranch CenteredMomentRetainedProfile

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def wholeHighDatum {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (s : Data ι) (second : Bool)
    (L : Ideal O) (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (ap bp : ℝ) :
    HighSourceDatum M H P η₀ Z (WholeSourceIndex M H) where
  state := st
  hQM := hQM
  hQη := hQη
  z := z
  hz := hz
  natural := naturalRow st.character z (st.row_ne_zero z hz)
  character := wholeSourceFamily M H hH η₀
    (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
  hcharacter := whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _
  member := Sum.inl ()
  Slot := ι
  source := s
  second := second
  projector := L
  allocation := alloc
  w := w
  σ := σ
  v := v
  θ := θ
  t := s.t
  W := ![s.W₁,s.W₂]
  X := Cycle63.Physical.postPlainScale L alloc
    (Cycle63.Physical.sourcePlainScales s.toSource second)
  r := fun j => Real.logb Z (clippedScale (Cycle63.Physical.postPlainScale L alloc
    (Cycle63.Physical.sourcePlainScales s.toSource second) j))/P.d
  A := fun _ => ap
  B := fun _ => bp

theorem whole_high_datum_low {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (s : Data ι) (second : Bool)
    (L : Ideal O) (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (ap bp a : ℝ) (i : ℕ)
    (hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0)
    (hupper : let D := wholeHighDatum M H hH P η₀ Z st hQM hQη z hz s second L alloc w σ v θ ap bp
      HeckeDetectorZeros.zeroMaximum D.character D.hcharacter (3*(i+1 : ℕ)*Z^P.τ) < a+2*P.e) :
    ActualLow M H hH st η₀ hQM hQη a P.e (3*(i+1 : ℕ)*Z^P.τ) z := by
  exact whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz a P.e _ hs hupper

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
