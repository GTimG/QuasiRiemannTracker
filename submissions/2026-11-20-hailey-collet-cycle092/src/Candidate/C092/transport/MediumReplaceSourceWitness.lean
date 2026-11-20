/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine same-zero inverse/ordinary witnesses for arbitrary source regular cores.
No outer BaselineData or BaselineSourceData occurs in the theorem. -/
import Candidate.C092.transport.MediumReplaceSourceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeGlobal

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckePrimeRay HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeDetectorSupportedWitness ProbeHighRowFamily
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_MediumReplaceSourceWitness_55191c411bdb1fd3_001 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Source-side finite band selection and supported same-zero alternatives.
The chosen I is before the natural states and all row/relative labels. The
conductor is the actual d>=Mcap+Bmask+margin, not a renamed radial radius.
For a>51/100 the cutoff is chosen before either attaining kernel. -/
theorem regular_core_witnesses
    (bΦ Mcap Bmask margin dmin dmax τ ε e κ heightCost : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hcost : 0 ≤ heightCost)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*heightCost ≤ ε/2) :
    ∃ I : ℕ,0 < I ∧ ∀ η₀ : Character,∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
      ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus),
      ∀ (z : O) (hz : s.radial.keep z),
        s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      let F := naturalRow s.character z (s.row_ne_zero z hz)
      ∃ i k : ℕ,1 ≤ i ∧ i ≤ I ∧ k ≤ ⌊(49/100 : ℝ)/e⌋₊ ∧
      let a : ℝ := 51/100+e*k
      (51/100 : ℝ) ≤ a ∧ a ≤ 1 ∧
      zeroMaximum (family M H hH s η₀ F) (family_nonprincipal M H hH s η₀ hQM hQη hz F)
        (3*(i+1 : ℕ)*Z^τ) < a+2*e ∧
      a ≤ zeroMaximum (family M H hH s η₀ F) (family_nonprincipal M H hH s η₀ hQM hQη hz F)
        ((3*i : ℕ)*Z^τ) ∧
      ∀ cutoff : ℝ,1 ≤ cutoff → cutoff ≤ 3/2 → 51/100 < a →
        Nonempty (SupportedWitness (family M H hH s η₀ F) (Z^d) a ε cutoff
          (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨I,hI,hwidth⟩ := exists_source_cube_bin_number e he
  obtain ⟨Z₀,hwitness⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hcost hbudget
  refine ⟨I,hI,?_⟩
  intro η₀
  filter_upwards [family_conductor_eventually M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin,
    eventually_ge_atTop Z₀,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))] with Z hcond hlarge hT
  refine ⟨hcond.1,?_⟩
  intro d hd hd' hds s hs hQM hQη z hz hΦ
  dsimp only
  let F := naturalRow s.character z (s.row_ne_zero z hz)
  let χ := family M H hH s η₀ F
  have hχ := family_nonprincipal M H hH s η₀ hQM hQη hz F
  obtain ⟨i,k,hi,hiI,ha,hcurrent,hcurrent',hnext,hzero,hdisk⟩ :=
    exists_detector_buffered_bin χ (Z^τ) e hT he I hI hwidth
  have hbase : (51/100 : ℝ) ≤ 51/100+e*k := le_add_of_nonneg_right (mul_nonneg he.le (Nat.cast_nonneg _))
  have hmaxeq := detectorMaximum_eq_nonprincipal χ hχ
  have hcurrentZ : 51/100+e*k ≤ zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) := by
    rw [←hmaxeq]
    convert hcurrent using 1 <;> push_cast <;> ring
  have hnextZ : zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < 51/100+e*k+2*e := by
    rw [←hmaxeq]
    exact hnext
  refine ⟨i,k,hi,hiI,?_,hbase,ha,hnextZ,hcurrentZ,?_⟩
  · apply Nat.le_floor
    apply (le_div_iff₀ he).mpr
    linarith
  · intro cutoff hc hc' hapos
    have hQ : ∀ j,((χ j).modulus.absNorm : ℝ) ≤ Z^d := fun j =>
      (hcond.2 s hs z F hΦ j).trans (Real.rpow_le_rpow_of_exponent_le hcond.1.le hds)
    obtain ⟨ws⟩ := hwitness Z hlarge d hd hd' (fun _ : Unit => χ) (fun _ => hχ)
      (51/100+e*k) i hiI hapos ha (fun _ => hnextZ) (fun _ => hcurrentZ)
      (fun _ => hQ) cutoff hc hc'
    exact ⟨ws ()⟩

end QRH.Cycle092.MediumReplace.Source
#print axioms QRH.Cycle092.MediumReplace.Source.regular_core_witnesses
