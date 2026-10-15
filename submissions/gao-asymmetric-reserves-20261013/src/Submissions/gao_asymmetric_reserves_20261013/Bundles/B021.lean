/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B018
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B019
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPower
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.IdealOperations
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorNormalized

/- BEGIN ORIGINAL MODULE LocalMoment.HeightUniformDensity ; sha256 55de8050440d3e473ac32820cf5e57e7a8bf207bd9a9cf1811bc58f96fb78eee -/
section


/-! Uniformity in the independent height is retained through the bounded
window completion and the sixth-power convolution. These theorems require
an eventual estimate with its threshold chosen before the parameter.
They do not manufacture such uniformity from pointwise eventual estimates. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ConcretePrimeRowBridge

theorem uniform_free_density_weighted_of_eventually {α : Type*}
    (P : α → FreeRow → Prop) (C : ℝ) (ρ weight : α → ℝ)
    (hρ : ∀ p, 0 ≤ ρ p) (hw : ∀ p, 1 ≤ weight p)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) →
        (F.card : ℝ) ≤ C * weight p * Y ^ ρ p) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) →
        (F.card : ℝ) ≤ C' * weight p * Y ^ ρ p := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hevent
  let B : ℝ := max 1 Y₀
  let C' : ℝ := max C (128 * B)
  have hB : 1 ≤ B := le_max_left _ _
  have hC' : 0 < C' := lt_of_lt_of_le (by dsimp [B]; positivity) (le_max_right _ _)
  refine ⟨C', hC', le_max_left _ _, ?_⟩
  intro Y hY p F hF
  have hw0 : 0 ≤ weight p := zero_le_one.trans (hw p)
  by_cases hlarge : Y₀ ≤ Y
  · exact (hY₀ Y hlarge p F hF).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0)
        (Real.rpow_nonneg (by linarith) _))
  · have hc : (F.card : ℝ) ≤ 128 * B :=
      freeRow_count F B hB (fun u hu => (hF u hu).1.trans
        ((le_of_not_ge hlarge).trans (le_max_right _ _)))
    have hp : 1 ≤ Y ^ ρ p := Real.one_le_rpow hY (hρ p)
    have hcw : C' ≤ C' * weight p := by nlinarith [hw p]
    calc
      (F.card : ℝ) ≤ 128 * B := hc
      _ ≤ C' := le_max_right _ _
      _ ≤ C' * weight p := hcw
      _ ≤ C' * weight p * Y ^ ρ p := by
        exact le_mul_of_one_le_right (mul_nonneg hC'.le hw0) hp

/-- A common eventual threshold for all bins/heights remains common after
bounded-window completion and passage from free cores to all integer rows.
For application take `weight p = (1 + |height p|)^J`. -/
theorem raw_density_weighted_from_eventual_free
    {α ι : Type*} [Fintype ι]
    (data : α → ι → RowData) (a b T weight ρ : α → ℝ) (C ρ₀ : ℝ)
    (hρ₀ : 1 / 6 < ρ₀) (hρ : ∀ p, ρ₀ ≤ ρ p)
    (hw : ∀ p, 1 ≤ weight p)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧
        rawZeroBin (data p) (a p) (b p) (T p) ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ C * weight p * Y ^ ρ p) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : α, ∀ H : ℝ, 0 < H →
      ∀ R : Finset ProbePhysical.NonzeroFrequency,
      (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧
        rawZeroBin (data p) (a p) (b p) (T p) h) →
        (R.card : ℝ) ≤ K * weight p * H ^ ρ p := by
  let P : α → FreeRow → Prop := fun p u =>
    rawZeroBin (data p) (a p) (b p) (T p) ⟨u.val, u.property.1⟩
  obtain ⟨C', hC', _, hfree⟩ :=
    uniform_free_density_weighted_of_eventually P C ρ weight
      (fun p => by linarith [hρ p]) hw hevent
  obtain ⟨D, hD, hraw⟩ := raw_density_uniform_exponent ρ₀ hρ₀
  refine ⟨C' * D, mul_pos hC' hD, ?_⟩
  intro p H hH R hR
  have hcp : 0 ≤ C' * weight p :=
    mul_nonneg hC'.le (zero_le_one.trans (hw p))
  have hb := hraw (data p) (a p) (b p) (T p) (C' * weight p) (ρ p)
    hcp (hρ p) (fun Y hY F hF => hfree Y hY p F hF) H hH R hR
  convert hb using 1
  ring

#print axioms uniform_free_density_weighted_of_eventually
#print axioms raw_density_weighted_from_eventual_free

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.HeightUniformDensity -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyNormalized ; sha256 2a7b16ed73fe873328ef130b532f6a5f98e2ed7e09aa697d7fc9355c1deba300 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_normalized_nonfloor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤13/16+ζ → d-v≤μ →
      51/100< a → a≤1 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell (fun j y=>(W j y:ℂ)) Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) (fun j y=>(W j y:ℂ)) Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤ A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨C,hC,hbound⟩ :=
    actual_nonfloor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 counts
  have hellpos (j : Fin N) : 0< ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C*Cn,mul_pos hC hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only at hn ⊢
  intro hmom
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent hmom
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (3/16+Δ-saving) nu]
  ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyNormalized -/

/- BEGIN ORIGINAL MODULE Analytic.ActualBufferedCount ; sha256 91c897696ffc5d3e358d06621af3a19568cdf7309719fea09e58ceaed6ebd939 -/
section


/-!
Actual buffered-row counting, with witness construction and both moment
inputs discharged. The remaining hypotheses are literal arithmetic
coefficient identities, nonprincipality, conductor bounds and buffered
zero maxima for the finite row set being counted.
-/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRawFiber HeckeDetectorInverseFiberCount
open HeckeDetectorProfiles HeckeDetectorRowwisePolynomial
open ProbeHighRowFamily LocalMoment

local notation "O" => HeckeFamily.O

/-- A literal buffered-zero row set obeys the balanced density exponent.

Unlike a conditional moment interface, this theorem takes neither a
moment estimate nor a detector witness as input. Both are constructed
from the existing source theorems. The height is quantified after the
eventual row threshold.
-/
theorem actual_buffered_row_count {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : ∀ label, Q ≤ (η label).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm τ ε e κaux ηaux : ℝ) (I : ℕ)
    (hεm : 0 < εm) (hτ : 0 < τ) (hτzero : τ < 1/2)
    (hτheight : 4*τ < ηaux) (hε : 0 < ε) (hεsmall : ε ≤ 1/1000)
    (he : 0 < e) (hesmall : e < 1/1000)
    (hκ : 0 < κaux) (hκone : κaux ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κaux+2*ηaux ≤ ε/2) :
    ∃ J : ℕ, ∃ C K₀ : ℝ, 0 < C ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (rows : Finset FreeRow) (family : rows → Label → Character)
        (reverse : Label → Bool) (hχ : ∀ u j, (family u j).residue ≠ 1),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u : rows, ∀ j, ∀ R : Ideal O, idealCoeff (family u j) R =
        if reverse j then starRingEnd ℂ
          (idealCoeff ((momentData (η j)).character
            ⟨u.val.val, u.val.property.1⟩) R)
        else idealCoeff ((momentData (η j)).character
          ⟨u.val.val, u.val.property.1⟩) R) →
      ∀ (a height : ℝ) (i : ℕ), i ≤ I → 51/100 < a → a ≤ 7/8 →
      (∀ u, HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        (3*(i+1 : ℕ)*U^τ) < a+2*e) →
      (∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        ((3*i : ℕ)*U^τ)) →
      (∀ u j, (family u j).modulus.absNorm ≤ U) →
      0 ≤ height → 2*Real.pi*U^(τ/2)+(3*i : ℕ)*U^τ ≤ height →
      (rows.card : ℝ) ≤ (Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2 *
        fiberConstant (C*(1+height)^J) height K₀ *
          U^(unmarkedDensity (2*a-1)+156*ε+εm) := by
  obtain ⟨J, C, K₀, hC, hK, hcount⟩ := actual_unmarked_batch_count
    η Q hQtop hQ72 hQη hβ M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨U₀, hwitness⟩ := actual_supported_witness_family
    1 1 τ ε e κaux ηaux I (by norm_num) le_rfl hτ hτzero
    (by simpa only [one_mul] using hτheight) hε he hesmall hκ hκone hη hbudget
  refine ⟨J, C, K₀, hC, hK, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop U₀] with U hcount hU₀
  refine ⟨hcount.1, ?_⟩
  intro rows family reverse hχ hrow hcoeff a height i hi ha ha' hnext hcurrent hQ hh hf
  have hCheight : 0 ≤ C*(1+height)^J := by positivity
  have hconst := (fiberConstant_bounds (C*(1+height)^J) height K₀ hCheight hh hK).1
  by_cases hne : rows.Nonempty
  · have hcut := unmarkedCutoff_bounds (δ := 2*a-1) (by linarith) (by linarith)
    have hrow' : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U^(1 : ℝ) := by
      simpa only [Real.rpow_one] using hrow
    have hQ' : ∀ u j, (family u j).modulus.absNorm ≤ U^(1 : ℝ) := by
      simpa only [Real.rpow_one] using hQ
    have hw : Nonempty (∀ u : rows, SupportedWitness (family u) U a ε
        (unmarkedCutoff (2*a-1)) (U^τ) (U^(τ/2)) i) := by
      have hw0 := hwitness U hU₀ 1 le_rfl le_rfl family hχ a i hi
          (by linarith) (by linarith) hnext hcurrent hQ'
          (unmarkedCutoff (2*a-1)) hcut.1 hcut.2
      rw [Real.rpow_one, mul_one] at hw0
      exact hw0
    obtain ⟨w⟩ := hw
    obtain ⟨u₀, hu₀⟩ := hne
    let B := UnmarkedBatch.ofSupportedRows rows ⟨u₀, hu₀⟩ family w hrow
      (fun label => momentData (η label)) reverse hcoeff
    have hb := hcount.2 a ε (U^τ) (U^(τ/2)) height i (by linarith)
      (by linarith) hε.le hεsmall hh hf B rfl
    exact hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hconst)
      (Real.rpow_nonneg (zero_lt_one.trans hcount.1).le _)

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualBufferedCount -/

/- BEGIN ORIGINAL MODULE Analytic.ActualSourceRow ; sha256 e1ddc7762b0f813a5cd2100f136c44c2d722b5db90272a08ce25fcb8c2bb6187 -/
section




/-! Lift the signed reconstruction to the literal Hecke coefficients of the
source's chosen first pair. The parent dictionary is fixed before C and D.
Both canceled-prime masks and the unsupported-ideal zeros are retained. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open CenteredMomentFirstColumns HeckeFamily CenteredMomentFixedRay
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CompletedGauss RayFourExpansion

local notation "O" => ActualEisensteinCubic.O

def phaseParent (η φ : Character) (ξ : RayCharacter) : Character :=
  (η.product φ).product (primaryRayCharacter ξ)

def fixedParentDictionary (η : Character) : Finset Character :=
  (fixedPhaseDictionary ×ˢ fixedPhaseDictionary).image
    (fun p => (η.product p.1).product p.2)

theorem phaseParent_mem (η φ : Character) (hφ : φ ∈ fixedPhaseDictionary)
    (ξ : RayCharacter) : phaseParent η φ ξ ∈ fixedParentDictionary η := by
  apply Finset.mem_image.mpr
  refine ⟨(φ, primaryRayCharacter ξ), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨hφ, Finset.mem_image.mpr ⟨ξ, Finset.mem_univ _, rfl⟩⟩

theorem fixedParentDictionary_fixedQ (η τ : Character) (Q : Ideal O)
    (hQη : Q ≤ η.modulus) (hQ : Q ≤ Ideal.span {(72 : O)})
    (hτ : τ ∈ fixedParentDictionary η) : Q ≤ τ.modulus := by
  obtain ⟨⟨φ, ψ⟩, hmem, rfl⟩ := Finset.mem_image.mp hτ
  obtain ⟨hφ, hψ⟩ := Finset.mem_product.mp hmem
  change Q ≤ (η.modulus ⊓ φ.modulus) ⊓ ψ.modulus
  exact le_inf (le_inf hQη (fixedPhaseDictionary_fixedQ Q hQ φ hφ))
    (fixedPhaseDictionary_fixedQ Q hQ ψ hψ)

theorem phaseParent_rowWeight (η φ : Character) (ξ : RayCharacter)
    (w : O) (t : ℝ) (I : Ideal O) (hI : Supported I) :
    rowWeight (phaseParent η φ ξ) fixedBadMask 1 w t I =
      (rowWeight η fixedBadMask 1 1 t I * elementCoeff φ (primaryGenerator I) *
        rayCharacter ξ (primaryGenerator I)) * idealRowHom w I := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hp := (primaryGenerator_spec I hn).2
  have hφ : idealCoeff φ I = elementCoeff φ (primaryGenerator I) := by
    simpa only [hs] using idealCoeff_span φ hn
  have hξ : idealCoeff (primaryRayCharacter ξ) I = rayCharacter ξ (primaryGenerator I) := by
    have he : idealCoeff (primaryRayCharacter ξ) I =
        elementCoeff (primaryRayCharacter ξ) (primaryGenerator I) := by
      simpa only [hs] using idealCoeff_span (primaryRayCharacter ξ) hn
    rw [he, primaryRayCharacter_primary ξ _ (hs.symm ▸ hI) hp]
  rw [rowWeight_split, ← heightCoeff_eq_fixed_rowWeight _ t I hI,
    ← heightCoeff_eq_fixed_rowWeight η t I hI]
  simp only [phaseParent, heightCoeff, idealCoeff_product, hφ, hξ]
  ring

/-- Every actual first-pair character, followed by a second frequency, is a
row over one of finitely many fixed parents. The identities hold on all ideals
and all heights, including every original arithmetic zero. -/
theorem actual_source_rows_fixed_parent (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    ∃ u : Oˣ, ∃ τL ∈ fixedParentDictionary η, ∃ τR ∈ fixedParentDictionary η,
      activeConductor C D = (u : O) * ∏ i, activePrimary C D i ∧
      ∀ j : O, ∀ t : ℝ, ∀ I : Ideal O,
        (rowWeight F.left fixedBadMask 1 j t I =
          rowWeight τL fixedBadMask 1
            (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
              (u : O) * leftEffectiveFactor C D * j) t I *
            leftCanceledMask C D (primaryGenerator I)) ∧
        (rowWeight F.right fixedBadMask 1 j t I =
          rowWeight τR fixedBadMask 1
            (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
              (u : O) * rightEffectiveFactor C D * j) t I *
            rightCanceledMask C D (primaryGenerator I)) := by
  obtain ⟨u, φL, hφL, φR, hφR, hu, hrow⟩ := actual_joint_row_dictionary C D hC
  refine ⟨u, phaseParent η φL ξ₁, phaseParent_mem η φL hφL ξ₁,
    phaseParent η φR ξ₂, phaseParent_mem η φR hφR ξ₂, hu, ?_⟩
  intro j t I
  by_cases hI : Supported I
  · have hn := supported_primaryGenerator_ne_zero I hI
    have hs := primary_span_supported I hI
    have hp := (primaryGenerator_spec I hn).2
    obtain ⟨hl, hr⟩ := hrow
      (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) j
      (primaryGenerator I) (hs.symm ▸ hI) hp
    rw [hs] at hl hr
    constructor
    · rw [rowWeight_split F.left, ← heightCoeff_eq_fixed_rowWeight F.left t I hI,
        F.left_height I hI t, phaseParent_rowWeight η φL ξ₁ _ t I hI]
      calc
        _ = (rowWeight η fixedBadMask 1 1 t I * rayCharacter ξ₁ (primaryGenerator I)) *
            (leftCoefficient
              (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
              (activeConductor C D)
              (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D))
              (primaryGenerator I) * idealRowHom j I) := by ring
        _ = _ := by rw [hl]; ring
    · rw [rowWeight_split F.right, ← heightCoeff_eq_fixed_rowWeight F.right t I hI,
        F.right_height I hI t, phaseParent_rowWeight η φR ξ₂ _ t I hI]
      calc
        _ = (rowWeight η fixedBadMask 1 1 t I * rayCharacter ξ₂ (primaryGenerator I)) *
            (rightCoefficient
              (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
              (activeConductor C D)
              (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D))
              (primaryGenerator I) * idealRowHom j I) := by ring
        _ = _ := by rw [hr]; ring
  · have hz (τ : Character) (w : O) : rowWeight τ fixedBadMask 1 w t I = 0 :=
      rowWeight_zero_of_not_supported τ fixedBadMask 1 w t
        (dvd_mul_right goodLambda 2) (dvd_mul_left 2 goodLambda) I hI
    simp only [hz, zero_mul, and_self]

#print axioms actual_source_rows_fixed_parent
#print axioms fixedParentDictionary_fixedQ

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualSourceRow -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorPower ; sha256 5b70c1d16f1df66d3fe2a930ae683c79f849e5b97e7cc45ddccc5fe2af89bd8b -/
section



/-! Refined powers for the actual extracted Gaussian source. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance jointErrorPowerInstance1 {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance jointErrorPowerInstance2 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

/-- Reuses the source power vector while retaining the exact affine error.
Only its first entry depends on this argument. -/
def refinedErrorDeficit (p : O) (Z : ℝ) (k : ℕ) (sigma deficit : ℝ) : ℝ :=
  deficit+sigma-5*errorRemoval p Z k-errorMoving p Z k

theorem refined_error_power_from_bands
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(hbPlain:0≤ b)
    (L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0< Cm ∧ 0≤ Ce ∧ 0< Cd ∧ 0< Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Kc:ℝ,0< Kc ∧ ∃Z₀:ℝ,1< Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0< K → 1≤ cost → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n);
    let Hweights:=coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J
      (internalQ Q η₀) Kc v0 εsrc (seed.absNorm:ℝ)
      (CenteredMomentEnergyFirstGaussianCoefficients.fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase v0
        (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
        (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,Hweights j*CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (refinedErrorDeficit prime Z (k+1) sigma (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    refined_error_smaller_gaussian (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kc,hKc,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0
  let Km:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input rfl
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  have hg:=hbound χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n)
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  have hz:0< Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hE:0≤ Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤ N:=
    (live_card_le Bp.val).trans ((live_card_le B.val).trans hcard)
  have hloProd:=CenteredMomentEnergyOriginalProfileControl.lower_product input N lower hlower hcardInput
    (fun i=> hlowerSrc.trans (src.lower_le i.val.val))
  have hlo:CenteredMomentSecondInputCapacitySource.lowerFactor N lower a≤(∏i,input.lo i)*a*a:=by
    unfold CenteredMomentSecondInputCapacitySource.lowerFactor
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hloProd (sq_nonneg a)
  have hcoef:=CenteredMomentEnergyFirstGaussianCoefficients.error_coefficients
    N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc prime (k+1)
    Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Km v0 (τ.modulus.absNorm:ℝ) cost Ebase
    (refinedErrorDeficit prime Z (k+1) sigma (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid r
    (∏i,input.lo i) a (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
    (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
    (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
    (by unfold Km errorCommonRadius;positivity)
    (CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain) hlo
  have hexp:
      (Bcap+Bcap)*εmask+(εchild+εremove+(sigma+errorRemoval prime Z (k+1)-errorMoving prime Z (k+1))/6+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh)=
      errorRemoval prime Z (k+1)+(refinedErrorDeficit prime Z (k+1) sigma (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))))/6+paid :=by
    dsimp [paid,refinedErrorDeficit];ring
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hh:=mul_le_mul_of_nonneg_right (hcoef j)
    (Real.rpow_nonneg (volume_pos input).le (powers εsrc j))
  simpa only [CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh

#print axioms refined_error_power_from_bands
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorPower -/

/- BEGIN ORIGINAL MODULE Cycle25.Arithmetic.Perturbation ; sha256 5f1467cef9a025bc02f66bb5df45e43add8f801eee6e7e47c237d20b86af025b -/
section


namespace Cycle25.Arithmetic

noncomputable def countingDen (κ p : ℝ) : ℝ := 3*κ*(3-p)-2*p
/-- B0.5's Cκ(p), with the inner divisions cleared. -/
noncomputable def countingCoefficient (κ p : ℝ) : ℝ :=
  2*(1-p)*(3*κ-p)/countingDen κ p
noncomputable def rowDen (κ d p : ℝ) : ℝ := (5/6-d)+d*countingCoefficient κ p
/-- The row exponent Rκ(δ,p) of B0.40. -/
noncomputable def rowExponent (κ d p : ℝ) : ℝ :=
  1-d+d*countingCoefficient κ p*(5/6-d)/(2*rowDen κ d p)
/-- The full endpoint Fκ^(4) of B0.47. -/
noncomputable def fullBoundary (κ d p : ℝ) : ℝ :=
  (1+ell0)/2+d/2+h0*(3*rowExponent κ d p/4-5/12)+
    d*p*(ell0-(h0-4*ell0)/(12*κ))

theorem countingDen_lower {κ p : ℝ} (hk : 7/10 ≤ κ) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    (17:ℝ)/4 ≤ countingDen κ p := by
  have hprod := mul_le_mul_of_nonneg_right hk (show 0 ≤ 3-p by linarith)
  unfold countingDen
  nlinarith

theorem countingCoefficient_pos {κ p : ℝ} (hk : 7/10 ≤ κ) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    0 < countingCoefficient κ p := by
  have hden : 0 < countingDen κ p := by linarith [countingDen_lower hk hp]
  have h1 : 0 < 1-p := by linarith
  have h2 : 0 < 3*κ-p := by linarith
  unfold countingCoefficient
  positivity

theorem rowDen_pos {κ d p : ℝ} (hk : 7/10 ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) : 0 < rowDen κ d p := by
  have hc := countingCoefficient_pos hk hp
  unfold rowDen
  by_cases he : d = 0
  · rw [he]; norm_num
  · have hd0 : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm he)
    have hdc : 0 < d*countingCoefficient κ p := mul_pos hd0 hc
    linarith

theorem canonical_counting_formula {κ p : ℝ} (hk : 7/10 ≤ κ) :
    countingCoefficient κ p = 2*(1-p)*(1-p/(3*κ))/(3-p-2*p/(3*κ)) := by
  have hk0 : κ ≠ 0 := ne_of_gt (by linarith)
  unfold countingCoefficient countingDen
  field_simp [hk0]

theorem rowExponent_eq_certR {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    rowExponent kappa0 d p = certR d (1/2-p) := by
  have hk : (7:ℝ)/10 ≤ kappa0 := le_of_lt kappa0_range.1
  have hD : countingDen kappa0 p ≠ 0 := ne_of_gt (by linarith [countingDen_lower hk hp])
  have hS : rowDen kappa0 d p ≠ 0 := ne_of_gt (rowDen_pos hk hd hp)
  have hu : 0 ≤ (1/2:ℝ)-p ∧ (1/2:ℝ)-p ≤ 1/2 := by constructor <;> linarith
  have hJ : certJ d (1/2-p) ≠ 0 := ne_of_gt (by linarith [(certJ_bounds hd hu).1])
  unfold rowExponent certR
  field_simp [hS, hJ]
  unfold rowDen countingCoefficient
  field_simp [hD]
  simp only [countingDen, certJ, certB]
  ring_nf
  field_simp (disch := first | assumption | (solve | norm_num) |
    (convert hJ using 1; simp only [certJ]; ring))
  ring

theorem fullBoundary_kappa0 {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary kappa0 d p = boundaryF d p := by
  unfold fullBoundary boundaryF certT
  rw [rowExponent_eq_certR hd hp]

theorem fullBoundary_binding : fullBoundary kappa0 delta0 (1/2) = b0 := by
  have hd : 0 ≤ delta0 ∧ delta0 ≤ 5/6 := by
    constructor <;> linarith [delta0_interval.1, delta0_interval.2]
  rw [fullBoundary_kappa0 hd ⟨by norm_num, le_refl _⟩]
  exact boundaryF_binding

theorem fullBoundary_eq_iff {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary kappa0 d p = b0 ↔ d = delta0 ∧ p = 1/2 := by
  rw [fullBoundary_kappa0 hd hp]
  exact boundaryF_eq_iff hd hp

theorem counting_gap {a κ p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hp : 0 ≤ p ∧ p ≤ 1/2) :
    0 ≤ countingCoefficient κ p-countingCoefficient a p ∧
    countingCoefficient κ p-countingCoefficient a p ≤ (κ-a)/18 := by
  have hk : 7/10 ≤ κ := ha.trans hak
  have hDa : 0 < countingDen a p := by linarith [countingDen_lower ha hp]
  have hDk : 0 < countingDen κ p := by linarith [countingDen_lower hk hp]
  have hgap : 0 ≤ κ-a := sub_nonneg.mpr hak
  have hn : 0 ≤ 6*p*(1-p)^2 := by have hp0 := hp.1; positivity
  have hnupper : 6*p*(1-p)^2 ≤ (8:ℝ)/9 := by
    have hm : 0 ≤ (p-1/3)^2*(4/3-p) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  have hid : countingCoefficient κ p-countingCoefficient a p =
      (6*p*(1-p)^2/(countingDen κ p*countingDen a p))*(κ-a) := by
    unfold countingCoefficient
    field_simp [ne_of_gt hDa, ne_of_gt hDk]
    simp only [countingDen]
    ring
  have hDD : (17/4:ℝ)^2 ≤ countingDen κ p*countingDen a p := by
    rw [pow_two]
    exact mul_le_mul (countingDen_lower hk hp) (countingDen_lower ha hp)
      (by norm_num) (le_of_lt hDk)
  have hcoef : 6*p*(1-p)^2/(countingDen κ p*countingDen a p) ≤ (1:ℝ)/18 := by
    apply (div_le_iff₀ (mul_pos hDk hDa)).2
    nlinarith
  rw [hid]
  constructor
  · positivity
  · calc
      _ ≤ (1/18)*(κ-a) := mul_le_mul_of_nonneg_right hcoef hgap
      _ = (κ-a)/18 := by ring

theorem row_gap {a κ d p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    rowExponent κ d p-rowExponent a d p ≤ (5/12)*((κ-a)/18) := by
  have hk := ha.trans hak
  have hc := counting_gap ha hak hp
  have hca : 0 ≤ countingCoefficient a p := le_of_lt (countingCoefficient_pos ha hp)
  have hck : 0 ≤ countingCoefficient κ p := le_of_lt (countingCoefficient_pos hk hp)
  have hSa := rowDen_pos ha hd hp
  have hSk := rowDen_pos hk hd hp
  have hd0 := hd.1
  have hV : 0 ≤ (5/6:ℝ)-d := by linarith
  have hSkV : (5/6:ℝ)-d ≤ rowDen κ d p := by
    unfold rowDen; nlinarith [mul_nonneg hd0 hck]
  have hSaV : (5/6:ℝ)-d ≤ rowDen a d p := by
    unfold rowDen; nlinarith [mul_nonneg hd0 hca]
  have hSS : ((5/6:ℝ)-d)^2 ≤ rowDen κ d p*rowDen a d p := by
    simpa only [pow_two] using mul_le_mul hSkV hSaV hV (le_of_lt hSk)
  have hratio : d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p) ≤ d/2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hSS hd0]
  have hid : rowExponent κ d p-rowExponent a d p =
      (d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p))*
        (countingCoefficient κ p-countingCoefficient a p) := by
    unfold rowExponent
    field_simp [ne_of_gt hSa, ne_of_gt hSk]
    simp only [rowDen]
    ring
  rw [hid]
  calc
    _ ≤ (d/2)*(countingCoefficient κ p-countingCoefficient a p) :=
      mul_le_mul_of_nonneg_right hratio hc.1
    _ ≤ (5/12)*(countingCoefficient κ p-countingCoefficient a p) :=
      mul_le_mul_of_nonneg_right (by linarith) hc.1
    _ ≤ (5/12)*((κ-a)/18) := mul_le_mul_of_nonneg_left hc.2 (by norm_num)

/-- T1.3 proved by finite differences; no differentiation or limiting argument
is needed for the uniform perturbation used by the contradiction. -/
theorem fullBoundary_gap {κ d p : ℝ} (hk : kappa0 ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary κ d p-fullBoundary kappa0 d p ≤ (κ-kappa0)/10 := by
  have hk0 : (7:ℝ)/10 ≤ kappa0 := le_of_lt kappa0_range.1
  have hk' : (7:ℝ)/10 ≤ κ := hk0.trans hk
  have ha0 : 0 < kappa0 := by linarith
  have hb0 : 0 < κ := by linarith
  have hgap : 0 ≤ κ-kappa0 := sub_nonneg.mpr hk
  have hh0 : 0 ≤ h0 := by linarith [h0_interval.1]
  have hg := derivative_geometry
  have hreserve : 0 ≤ h0-4*ell0 := le_of_lt hg.2.1
  have hrow := row_gap hk0 hk hd hp
  have hR : 3*h0/4*(rowExponent κ d p-rowExponent kappa0 d p) ≤
      (3/4)*(4/5)*(5/12)*((κ-kappa0)/18) := by
    calc
      _ ≤ (3*h0/4)*((5/12)*((κ-kappa0)/18)) :=
        mul_le_mul_of_nonneg_left hrow (by positivity)
      _ ≤ (3/4)*(4/5)*(5/12)*((κ-kappa0)/18) := by
        nlinarith [mul_nonneg (show 0 ≤ 4/5-h0 by linarith [hg.1]) hgap]
  have hprod : (7/10:ℝ)^2 ≤ κ*kappa0 := by
    rw [pow_two]
    exact mul_le_mul hk' hk0 (by norm_num) (le_of_lt hb0)
  have hinvid : 1/kappa0-1/κ = (κ-kappa0)/(κ*kappa0) := by
    field_simp
  have hinv : 1/kappa0-1/κ ≤ (κ-kappa0)/((7/10:ℝ)^2) := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hgap (by norm_num) hprod
  have hdp : 0 ≤ d*p := mul_nonneg hd.1 hp.1
  have hdp' : d*p ≤ (5:ℝ)/12 := by
    have hm := mul_le_mul hd.2 hp.2 hp.1 (show (0:ℝ) ≤ 5/6 by norm_num)
    norm_num at hm
    exact hm
  have hcoef : 0 ≤ d*p*(h0-4*ell0)/12 := by positivity
  have hcoef' : d*p*(h0-4*ell0)/12 ≤ (5/12)*(13/100)/12 := by
    have hm := mul_le_mul hdp' (le_of_lt hg.2.2) hreserve (show (0:ℝ) ≤ 5/12 by norm_num)
    linarith
  have hinv0 : 0 ≤ (κ-kappa0)/((7/10:ℝ)^2) := by positivity
  have hI : (d*p*(h0-4*ell0)/12)*(1/kappa0-1/κ) ≤
      ((5/12)*(13/100)/12)*((κ-kappa0)/((7/10:ℝ)^2)) := by
    calc
      _ ≤ (d*p*(h0-4*ell0)/12)*((κ-kappa0)/((7/10:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef' hinv0
  have hid : fullBoundary κ d p-fullBoundary kappa0 d p =
      (3*h0/4)*(rowExponent κ d p-rowExponent kappa0 d p)+
        (d*p*(h0-4*ell0)/12)*(1/kappa0-1/κ) := by
    unfold fullBoundary
    field_simp
    ring
  have hconst : (3/4:ℝ)*(4/5)*(5/12)*(1/18)+(5/12)*(13/100)/(12*(7/10)^2) ≤ 1/10 := by
    norm_num
  have hm := mul_le_mul_of_nonneg_right hconst hgap
  rw [hid]
  ring_nf at hR hI hm ⊢
  linarith only [hR, hI, hm]

theorem fullBoundary_uniform {κ d p : ℝ} (hk : kappa0 ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary κ d p ≤ b0+(κ-kappa0)/10 := by
  have hgap := fullBoundary_gap hk hd hp
  rw [fullBoundary_kappa0 hd hp] at hgap
  linarith [boundaryF_le_b0 hd hp]

theorem supremum_improvement {β d p : ℝ} (hβ : b0 < β)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary (2*β-1) d p-β ≤ -(4/5)*(β-b0) := by
  have hk : kappa0 ≤ 2*β-1 := by rw [kappa0_eq]; linarith
  have hF := fullBoundary_uniform hk hd hp
  rw [kappa0_eq] at hF
  linarith

end Cycle25.Arithmetic
end
/- END ORIGINAL MODULE Cycle25.Arithmetic.Perturbation -/
