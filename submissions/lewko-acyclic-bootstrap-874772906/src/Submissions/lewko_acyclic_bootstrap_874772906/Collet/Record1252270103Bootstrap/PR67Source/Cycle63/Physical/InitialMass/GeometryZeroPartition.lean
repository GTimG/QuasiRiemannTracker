import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Families
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.FirstLevel
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter Set HeckeFamily HeckeDetectorZeros LocalMoment
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open ConcreteTraceCRT Cycle63Moment Cycle63Moment.LowBranch
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The actual whole family includes the plain character and all relative rays. -/
def geometryRowFamily {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (z : O) (hz : st.radial.keep z) : WholeSourceIndex M H→ Character :=
  wholeSourceFamily M H hH η₀
    (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)

theorem geometry_row_family_nonprincipal {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) :
    ∀j,(geometryRowFamily M H hH st η₀ z hz j).residue≠1 :=
  whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz
    (naturalRow st.character z (st.row_ne_zero z hz))

def geometryRowMaximum {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (T : ℝ) : ℝ :=
  zeroMaximum (geometryRowFamily M H hH st η₀ z hz)
    (geometry_row_family_nonprincipal M H hH st η₀ hQM hQη z hz) T

variable [Cycle63.AffineLedger] in
/-- Literal bin admission includes the zero-profile branch of the full row set. -/
def GeometryZeroBin {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e) : Prop :=
    1≤p.1.val ∧ p.1.val≤bufferCount e ∧
      let β:=bufferValue e p
      51/100≤β ∧ β≤7/8 ∧
      β≤geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T)<β+e ∧
      β≤geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T)<β+2*e ∧
      (β<((1+Cycle63.AffineLedger.q)/2) → ∀_hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0,
        ActualLow M H hH st η₀ hQM hQη (((1+Cycle63.AffineLedger.q)/2)) e (3*(p.1.val+1:ℕ)*T) z) ∧
      (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)=0 ∨
        ActualLow M H hH st η₀ hQM hQη (((1+Cycle63.AffineLedger.q)/2)) e (3*(p.1.val+1:ℕ)*T) z ∨ ((1+Cycle63.AffineLedger.q)/2)≤β)

variable [Cycle63.AffineLedger] in
/-- Every retained nonexceptional row has an actual buffered bin. Radial
zero terms remain explicit; all supported low rows enter ActualLow. -/
theorem actual_geometry_zero_partition {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    ∃p : BufferIndex e,GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p := by
  let χ:=geometryRowFamily M H hH st η₀ z hz
  let hn:=geometry_row_family_nonprincipal M H hH st η₀ hQM hQη z hz
  obtain ⟨i,k,hi,hin,hone,hcurrent,hround,hnext,_⟩ :=
    exists_actual_buffered_bin χ hn T e hT he (bufferCount e)
      (bufferCount_spec e he).1 (bufferCount_spec e he).2
  have hk : k≤bufferGridCount e := by
    have hkr : (k:ℝ)≤1/e := (le_div_iff₀ he).mpr (by nlinarith)
    exact_mod_cast hkr.trans (Nat.le_ceil (1/e))
  let p : BufferIndex e := (⟨i,by omega⟩,⟨k,by omega⟩)
  have hβ : bufferValue e p≤7/8 :=
    hcurrent.trans ((zeroMaximum_le_beta χ hn hβlo _).trans hβhi)
  have hmon : zeroMaximum χ hn ((3*i:ℕ)*T)≤zeroMaximum χ hn (3*(i+1:ℕ)*T) := by
    apply zeroMaximum_mono
    push_cast
    nlinarith
  have hlow (hb : bufferValue e p<((1+Cycle63.AffineLedger.q)/2))
      (hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0) :
      ActualLow M H hH st η₀ hQM hQη (((1+Cycle63.AffineLedger.q)/2)) e (3*(p.1.val+1:ℕ)*T) z := by
    apply whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz _ _ _ hs
    change zeroMaximum χ hn (3*(i+1:ℕ)*T)<((1+Cycle63.AffineLedger.q)/2)+2*e
    dsimp [bufferValue,p] at hb
    linarith
  refine ⟨p,hi,hin,?_,hβ,?_,?_,?_,?_,hlow,?_⟩
  · dsimp [bufferValue,p]; nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  · simpa only [geometryRowMaximum,bufferValue,p,Nat.cast_mul,Nat.cast_ofNat] using hcurrent
  · simpa only [geometryRowMaximum,bufferValue,p,Nat.cast_mul,Nat.cast_ofNat] using hround
  · have hm := hmon
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hm
    exact hcurrent.trans hm
  · exact hnext
  · by_cases hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)=0
    · exact Or.inl hs
    · rcases lt_or_ge (bufferValue e p) (((1+Cycle63.AffineLedger.q)/2):ℝ) with hb|hb
      · exact Or.inr (Or.inl (hlow hb hs))
      · exact Or.inr (Or.inr hb)

section Family
variable {κ : Type*} (rows : Finset κ)
variable {Z Bmask bΦ : ℝ} (st : rows→NaturalState Z Bmask bΦ) (η₀ : Character)
variable (hQM : ∀u,(st u).fixedModulus≤M) (hQη : ∀u,(st u).fixedModulus≤η₀.modulus)
variable (z : rows→O) (hz : ∀u,(st u).radial.keep (z u))
variable (e T : ℝ) (he : 0<e) (hT : 2<T)
variable (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)

end Family

/-- Small outer heights satisfy both column gates in every selected bin. -/
theorem geometry_small_outer_height (T t height : ℝ) (i : ℕ) (freq : ℝ)
    (hT : 0≤T) (hh : 0≤height) (hsmall : |t|+height≤T) (hf : |freq|≤height) :
    |t+freq|+T/2≤(3*i+2:ℕ)*T ∧ |t|+T/2≤(3*i+2:ℕ)*T := by
  have habs:=abs_add_le t freq
  have hn : (0:ℝ)≤(i:ℝ) := Nat.cast_nonneg _
  push_cast
  constructor <;> nlinarith [mul_nonneg hn hT]

/-- The fixed buffered index set fits the analytic truncated height range
at a threshold chosen before every moving natural state and row. -/
theorem eventually_geometry_zero_heights (e τ : ℝ) (hτ : 0<τ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ 2<Z^τ ∧
      ∀p : BufferIndex e,(p.1.val:ℝ)≤Z^τ := by
  filter_upwards [(tendsto_rpow_atTop hτ).eventually
      (eventually_gt_atTop (max (2:ℝ) (bufferCount e:ℝ))),eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,(lt_of_le_of_lt (le_max_left _ _) hz),?_⟩
  intro p
  have hp : p.1.val≤bufferCount e := by omega
  exact (by exact_mod_cast hp : (p.1.val:ℝ)≤bufferCount e).trans
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz))

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
