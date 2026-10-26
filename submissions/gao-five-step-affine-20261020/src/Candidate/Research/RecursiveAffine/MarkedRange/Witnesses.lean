import Candidate.Research.RecursiveAffine.MarkedRange.CountAssembly
import Candidate.Cycle63.Marked.Route.ActualWitnesses
import Candidate.Cycle63.Marked.Route.ActualWeightedCount
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle153MarkedWeighted
open Cycle63MarkedAssembly hiding count_from_four_powers binMean binCutoff adaptiveKey adaptiveFiber adaptiveFiber_fields adaptive_fiber_sum RawFiberMoments fiber_count weighted_bound_of_card weighted_row_sum label_bounds binCutoff_bounds
open Cycle63ActualWeighted
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Cycle153MarkedAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}
variable {base anchor : Label→ Character} {bad : Label→ Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

omit [Nonempty Label] [Fintype Slot] [DecidableEq Slot] in
/-- The adaptive detector witnesses are constructed from actual buffered zero
maxima, uniformly for every amplitude bin, including unused rounded bins. -/
theorem actual_adaptive_supported_witnesses
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃Z₀ : ℝ,∀Z : ℝ,Z₀≤Z → ∀d : ℝ,dmin≤d → d≤dmax →
      ∀{Row : Type}(χ : Row→Label→ Character)(hχ : ∀u j,(χ u j).residue≠1),
      ∀(a binWidth : ℝ)(i : ℕ),i≤I → Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤(2/3:ℝ) →
      0<binWidth → binWidth≤(2*a-1)/2 →
      (∀u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i:ℕ)*Z^τ)) →
      (∀u j,(χ u j).modulus.absNorm≤Z^d) →
      ∀(slots : Finset Slot)(widths : Slot→ℝ),(∀s∈slots,0≤widths s) →
      0<(∑s∈slots,widths s) →
      Nonempty (∀bin : BinLabel slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
          (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop : (2/3:ℝ)≤2/3 := le_rfl
  obtain ⟨Z₀,hsource⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row χ hχ a binWidth i hi ha0 ha hbin hbin' hnext hcurrent hmod
    slots widths hw hL
  have hbinWitness (bin : BinLabel slots ((2*a-1)/2) binWidth) :
      Nonempty (∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
    have hcut := Cycle153MarkedAssembly.binCutoff_bounds slots widths a binWidth ha0 ha hbin hbin' hw hL bin
    exact hsource Z hZ d hd hd' χ hχ a i hi (by linarith) (by linarith) hnext hcurrent hmod
      (binCutoff slots widths a binWidth bin) hcut.1 hcut.2
  exact ⟨fun bin=>Classical.choice (hbinWitness bin)⟩

end OAI.SevenEighths.Cycle153MarkedWeighted
