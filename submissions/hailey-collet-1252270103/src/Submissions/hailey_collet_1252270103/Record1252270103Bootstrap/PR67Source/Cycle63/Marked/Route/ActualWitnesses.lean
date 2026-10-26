import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.Route.ActualWeightedCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle63ActualWeighted
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Cycle63MarkedAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}
variable {base anchor : Label→ Character} {bad : Label→ Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

def NaturalBatch.retracted (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U)
    (u₀ : B.rows) : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U :=
  { B with
    family := fun u=>B.family (supportedRowRetraction B.rows u₀ u).val
    idealCoefficients := by
      intro u hu j I
      simpa only [supportedRowRetraction,dite_eq_left hu] using B.idealCoefficients u hu j I
    elementCoefficients := by
      intro u hu j n
      simpa only [supportedRowRetraction,dite_eq_left hu] using B.elementCoefficients u hu j n
    plainIdentity := by
      intro u hu j s hs
      simpa only [supportedRowRetraction,dite_eq_left hu] using B.plainIdentity u hu j s hs }

/-- Witnesses are required only on the actual finite row population. The
retraction gives the ambient interface without inventing zeros off that set. -/
def NaturalBatch.retracted_witnesses
    (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U) (u₀ : B.rows)
    {a ε T allowance binWidth : ℝ} {i : ℕ}
    (witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
      ∀u : B.rows,SupportedWitness (B.family u.val) U a ε
        (binCutoff B.slots B.widths a binWidth bin) T allowance i) :
    ∀bin : BinLabel (B.retracted u₀).slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness ((B.retracted u₀).family u) U a ε
        (binCutoff (B.retracted u₀).slots (B.retracted u₀).widths a binWidth bin) T allowance i :=
  fun bin u=>witness bin (supportedRowRetraction B.rows u₀ u)

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
      ∀(a binWidth : ℝ)(i : ℕ),i≤I → Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤Cycle63.Optimization.markedBinTop →
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
  have htop := Cycle63.Optimization.markedBinTop_bounds
  obtain ⟨Z₀,hsource⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row χ hχ a binWidth i hi ha0 ha hbin hbin' hnext hcurrent hmod
    slots widths hw hL
  have hbinWitness (bin : BinLabel slots ((2*a-1)/2) binWidth) :
      Nonempty (∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
    have hcut := binCutoff_bounds slots widths a binWidth ha0 ha hbin hbin' hw hL bin
    exact hsource Z hZ d hd hd' χ hχ a i hi (by linarith) (by linarith) hnext hcurrent hmod
      (binCutoff slots widths a binWidth bin) hcut.1 hcut.2
  exact ⟨fun bin=>Classical.choice (hbinWitness bin)⟩

end OAI.SevenEighths.Cycle63ActualWeighted

end
end Record1252270103Bootstrap.PR67
