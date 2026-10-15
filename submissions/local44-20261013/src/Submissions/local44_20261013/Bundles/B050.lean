/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B047
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicJoins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalCap
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedProfile

/- BEGIN ORIGINAL MODULE Global.Weighted.CellGeometry ; sha256 5209775532375f8395f3930a2dd2721931fefa0a74327db6a55527fe83f2daab -/
section


/-! Arithmetic and detector hypotheses for the literal retained full-w cells. -/
namespace Submission20261012.Global
open OAI OAI.SevenEighths
noncomputable section
open scoped Classical BigOperators
open Filter
namespace ProbeAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification

/-- The nonzero physical source normalizer already implies that every actual
prime slot has a label.  No separate prime-distribution input is required. -/
theorem weighted_source_pools_nonempty {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∀ᶠZ : ℝ in atTop,∀j : Fin D.N,(Cycle25.Numerator.sourcePrimePool F Z j).Nonempty := by
  obtain ⟨C,hC,hbound⟩ := weighted_source_normalizer_bound D F
  filter_upwards [hbound] with Z hn
  intro j
  by_contra hne
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
  have hmass : PrincipalSignalComparison.slotMass (Cycle25.Numerator.sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=> F.w) (fun j=> Z^(D.ell j))) j=0 := by
    simp only [PrincipalSignalComparison.slotMass,hempty,Finset.sum_empty]
  have hprod : (∏i : Fin D.N,PrincipalSignalComparison.slotMass
      (Cycle25.Numerator.sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=> F.w) (fun j=> Z^(D.ell j))) i)=0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hmass
  apply hn.1
  unfold weightedSourceNormalizer Probe.principalScalar
  exact mul_eq_zero_of_right _ (Complex.ofReal_eq_zero.mpr (mul_eq_zero_of_right _ hprod))

/-- A source-conductor threshold can be chosen uniformly for all dyads in a
fixed positive exponent range. -/
theorem eventually_uniform_source_conductor {P : ℝ→Prop} (dmin : ℝ) (hdmin : 0 < dmin)
    (hP : ∀ᶠU : ℝ in atTop,P U) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin ≤ d → P (Z^d) := by
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hP
  filter_upwards [(tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U0),
    eventually_ge_atTop (1:ℝ)] with Z hZmin hZ
  intro d hd
  exact hU0 (Z^d) (hZmin.trans (Real.rpow_le_rpow_of_exponent_le hZ hd))

/-- The actual external rectangle is within the bounded-height source count
range, after a threshold depending only on the finite height index budget. -/
theorem weighted_source_height_le (τ : ℝ) (n : ℕ) (hτ : 0 < τ) :
    ∀ᶠZ : ℝ in atTop,∀i : ℕ,i ≤ n →
      0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ ∧ ((3*i+1:ℕ):ℝ)*Z^τ ≤ Z^(2*τ) := by
  filter_upwards [HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hn hZ
  intro i hi
  have hi' : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hZp : 0 < Z := zero_lt_one.trans hZ
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ (3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
    _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring

def weightedCellRows {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z : ℝ) (idx grid : FreeRow→ℕ)
    (k i j : ℕ) : Finset FreeRow :=
  cubeBinRows ((supportedNonfloorRows F.S F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^(Submission20261012.Global.h+D.t))) grid)∩dyadicRows 1 k)
    idx grid i j

structure WeightedCellRowData {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character) (Z τ : ℝ)
    (idx grid : FreeRow→ℕ) (n k i j : ℕ) : Prop where
  a_lower : (51/100:ℝ) < 51/100+D.e*j
  a_upper : (51/100:ℝ)+D.e*j ≤ 7/8
  d_lower : (1/200:ℝ) ≤ sourceDyadConductor Z D.t k
  d_upper : sourceDyadConductor Z D.t k ≤ 7/8
  d_physical_upper : sourceDyadConductor Z D.t k ≤ Submission20261012.Global.h+3*D.t
  index_le : i ≤ n
  rows_source : ∀u∈weightedCellRows D F Z idx grid k i j,
    u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u ≤ Z^(sourceDyadConductor Z D.t k-D.t)
  rows_moment : ∀u∈weightedCellRows D F Z idx grid k i j,
    (Z^(sourceDyadConductor Z D.t k))^(1/100:ℝ) ≤ rowNorm u ∧
      rowNorm u ≤ Z^(sourceDyadConductor Z D.t k)
  rows_nonprincipal : ∀u∈weightedCellRows D F Z idx grid k i j,
    (rowCharacter F.S F.exclusions.prime u).residue≠1
  rows_frequency : ∀u∈weightedCellRows D F Z idx grid k i j,
    Z^(sourceDyadConductor Z D.t k-2*D.t) ≤ rowNorm u
  next : ∀u∈weightedCellRows D F Z idx grid k i j,
    detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(i+1:ℕ)*Z^τ) < 51/100+D.e*j+2*D.e
  current : ∀u∈weightedCellRows D F Z idx grid k i j,
    (51/100:ℝ)+D.e*j ≤ detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*i:ℕ)*Z^τ)

theorem weighted_source_cell_geometry {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀(η : Character) (τ : ℝ) (n : ℕ) (idx grid : FreeRow→ℕ),
      let rows := supportedNonfloorRows F.S F.maximal
        (rowBand (Z^(1/100:ℝ)) (Z^(Submission20261012.Global.h+D.t))) grid
      (∀u∈rows,idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/D.e⌋₊ ∧
        (51/100:ℝ)+D.e*grid u ≤ 7/8) →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(idx u+1:ℕ)*Z^τ) < 51/100+D.e*grid u+2*D.e) →
      (∀u∈rows,(51/100:ℝ)+D.e*grid u ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*idx u:ℕ)*Z^τ)) →
      ∀k i j : ℕ,i∈Finset.range (n+1) →
        (weightedCellRows D F Z idx grid k i j).Nonempty →
        WeightedCellRowData D F η Z τ idx grid n k i j := by
  have htop : Submission20261012.Global.h+D.t+2*D.t ≤ 7/8 := by linarith only [D.t_small, Submission20261012.Global.h_interval.2]
  filter_upwards [sourceDyad_geometry_eventually (1/200) (7/8) D.t (Submission20261012.Global.h+D.t)
    (by norm_num) (by norm_num) D.t_pos htop,eventually_gt_atTop (1:ℝ)] with Z hgeo hZ
  refine ⟨hZ,?_⟩
  intro η τ n idx grid
  dsimp only
  intro hlabels hnext hcurrent k i j hi hne
  let rows := supportedNonfloorRows F.S F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^(Submission20261012.Global.h+D.t))) grid
  let cell := weightedCellRows D F Z idx grid k i j
  have hsub : cell⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : cell⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      rowNorm u ≤ Z^(Submission20261012.Global.h+D.t) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ) < 51/100+D.e*j := by
    have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j ≤ 7/8 := by
    simpa only [huj] using (hlabels u (hsubr hu)).2.2
  have hsource : ∀v∈cell,v.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm v ∧
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
      rowNorm v ≤ Z^(sourceDyadConductor Z D.t k-D.t) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,
      hg.2.2.2.2.2 v (hsub hv)⟩
  have hphysical : sourceDyadConductor Z D.t k ≤ Submission20261012.Global.h+3*D.t := by
    unfold sourceDyadConductor
    linarith only [hg.2.1]
  refine ⟨ha,ha',hg.2.2.1,hg.2.2.2.1,hphysical,
    Nat.le_of_lt_succ (Finset.mem_range.mp hi),hsource,?_,?_,?_,?_,?_⟩
  · intro v hv
    constructor
    · apply le_trans _ (hsource v hv).2.1
      rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hg.2.2.2.1])
    · apply (hsource v hv).2.2.2.trans
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [D.t_pos])
  · intro v hv
    exact calibrated_row_nonprincipal F.S F.exclusions.prime F.maximal F.exclusions.bad
      v (hsource v hv).1 (hsource v hv).2.2.1
  · intro v hv
    simpa only [sourceDyadConductor,add_sub_cancel_right] using (hg.2.2.2.2.1 v (hsub hv)).1
  · intro v hv
    have hh := hnext v (hsubr hv)
    have hm := (mem_cubeBinRows _ idx grid i j v).mp hv
    rwa [hm.2.1,hm.2.2] at hh
  · intro v hv
    have hh := hcurrent v (hsubr hv)
    have hm := (mem_cubeBinRows _ idx grid i j v).mp hv
    rwa [hm.2.1,hm.2.2] at hh

end ProbeAssembly
end
end Submission20261012.Global

#print axioms Submission20261012.Global.ProbeAssembly.weighted_source_cell_geometry
end
/- END ORIGINAL MODULE Global.Weighted.CellGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.BufferedDilation ; sha256 e467d9bec15e9469185792624752debdc8bf26a1e1f9195c30147184eec4e45f -/
section




/-! Uniform Mellin gates for the literal clipped profiles. The constants
are fixed before the dilation, zero bin, frequency and derivative order
chosen by the buffered estimate. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set
namespace SevenEighths.Local44.Analytic
open HeckeDyadic CenteredMomentRetainedProfile CenteredMomentLattice

theorem dilated_mellin_uniform (W : ℝ → ℂ) (a b B l r : ℝ)
    (ha : 0 < a) (hB : 1 ≤ B)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (c : ℝ), 1 ≤ c → c ≤ B →
      ∀ x ∈ Icc l r, ∀ t : ℝ,
        (1+|t|)^k*‖mellin (dilated W c) ((x : ℂ)+t*Complex.I)‖ ≤ C k := by
  have hbound (k : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 1 ≤ c → c ≤ B → ∀ x ∈ Icc l r, ∀ t : ℝ,
        (1+|t|)^k*‖mellin (dilated W c) ((x : ℂ)+t*Complex.I)‖ ≤ C := by
    obtain ⟨S, C, hC, hdecay⟩ := profile_strip_decay (a/B) b
      (div_pos ha (zero_lt_one.trans_le hB)) l r k
    let D := C * B^(S.sup Prod.snd) *
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW 0)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨D+1, by linarith, ?_⟩
    intro c hc hcB x hx t
    let g := normPowerProfile (dilated W c) (a/B) b
      (div_pos ha (zero_lt_one.trans_le hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) 0
    have hg : (g : ℝ → ℂ) = dilated W c := by
      funext y
      simp [g, normPowerProfile_apply]
    have hgs : Function.support (g : ℝ → ℂ) ⊆ Icc (a/B) b := by
      rw [hg]
      exact dilated_support W a b B c ha hB hc hcB hs
    have hd := hdecay g hgs x hx t
    rw [hg] at hd
    have hn := normPowerProfile_dilated_finite W a b B c ha hB hc hcB hs hW 0 S
    calc
      _ ≤ C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := hd
      _ ≤ D := by
        dsimp only [D]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hn hC.le
      _ ≤ D+1 := by linarith
  choose C hC hb using hbound
  exact ⟨C, hC, hb⟩

/-- Two independent original profiles share one fixed collection of
Mellin constants, uniformly over both retained dilations. -/
theorem dilated_mellin_pair_uniform (W₁ W₂ : ℝ → ℂ)
    (a₁ b₁ B₁ a₂ b₂ B₂ l r : ℝ)
    (ha₁ : 0 < a₁) (hB₁ : 1 ≤ B₁) (ha₂ : 0 < a₂) (hB₂ : 1 ≤ B₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ (k : ℕ) (c : ℝ), 1 ≤ c → c ≤ B₁ →
        ∀ x ∈ Icc l r, ∀ t : ℝ,
          (1+|t|)^k*‖mellin (dilated W₁ c) ((x : ℂ)+t*Complex.I)‖ ≤ C k) ∧
      (∀ (k : ℕ) (c : ℝ), 1 ≤ c → c ≤ B₂ →
        ∀ x ∈ Icc l r, ∀ t : ℝ,
          (1+|t|)^k*‖mellin (dilated W₂ c) ((x : ℂ)+t*Complex.I)‖ ≤ C k) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := dilated_mellin_uniform W₁ a₁ b₁ B₁ l r ha₁ hB₁ hs₁ hW₁
  obtain ⟨C₂, hC₂, hb₂⟩ := dilated_mellin_uniform W₂ a₂ b₂ B₂ l r ha₂ hB₂ hs₂ hW₂
  refine ⟨fun k => C₁ k+C₂ k, fun k => add_pos (hC₁ k) (hC₂ k), ?_, ?_⟩
  · intro k c hc hcB x hx t
    exact (hb₁ k c hc hcB x hx t).trans (le_add_of_nonneg_right (hC₂ k).le)
  · intro k c hc hcB x hx t
    exact (hb₂ k c hc hcB x hx t).trans (le_add_of_nonneg_left (hC₁ k).le)

/-- Turn the uniform strip bound into the exact source profile record.
Frequency is unrestricted here; its separate buffered-height gate is
checked when applying the pointwise theorem. -/
def bufferedDilatedProfile (W : ℝ → ℂ) (a b B σmin σmax : ℝ)
    (ha : 0 < a) (hB : 1 ≤ B)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (C : ℕ → ℝ)
    (hm : ∀ (k : ℕ) (c : ℝ), 1 ≤ c → c ≤ B →
      ∀ x ∈ Icc (-1-σmax) (2-σmin), ∀ t : ℝ,
        (1+|t|)^k*‖mellin (dilated W c) ((x : ℂ)+t*Complex.I)‖ ≤ C k)
    (n : ℕ) (edge e σ freq c : ℝ)
    (hedge : edge ≤ 1) (he : e ≤ 1/1000)
    (hσ : σmin ≤ σ) (hσ' : σ ≤ σmax) (hc : 1 ≤ c) (hcB : c ≤ B) :
    BufferedPlainProfile n C edge e where
  W := dilated W c
  A := a/B
  B := b
  σ := σ
  freq := freq
  lower_pos := div_pos ha (zero_lt_one.trans_le hB)
  support := dilated_support W a b B c ha hB hc hcB hs
  smooth := dilated_contDiff W hW c
  mellin_two := by
    intro x hx t
    apply hm 2 c hc hcB x
    constructor <;> linarith [hx.1, hx.2]
  mellin_tail := by
    intro x hx t
    apply hm (n+2) c hc hcB x
    constructor <;> linarith [hx.1, hx.2]

#print axioms dilated_mellin_uniform
#print axioms dilated_mellin_pair_uniform
#print axioms bufferedDilatedProfile

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.BufferedDilation -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedData ; sha256 f61178d1cae6fb88b8ef195fd9aa72a98cad4c28bfa0edd20795ede58e0075d3 -/
section


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open HeckeFiniteDeletion CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open ConcretePrimeRowBridge LocalMoment ProbeHighRowFamily CenteredMomentFixedRayInducingTransport CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O

/-- One literal residual product at the reconstructed row. The two members
of a paired energy may select different fixed ray parents and punctures. -/
structure JointBufferedProductData (η : Character) (w : NonzeroElement)
    (Slot : Type*) (n : ℕ) (profileBound : ℕ → ℝ) (a e : ℝ) where
  parent : JointParentLabel η
  natural : NaturalRow parent.val w.val
  puncture : Ideal O
  puncture_ne : puncture ≠ 0
  plain₁ : BufferedPlainProfile n profileBound a e
  plain₂ : BufferedPlainProfile n profileBound a e
  r₁ : ℝ
  r₂ : ℝ
  r : Slot → ℝ
  σ : Slot → ℝ
  v : Slot → ℝ
  t : ℝ
  bin : ℕ

namespace JointBufferedProductData
variable {η : Character} {w : NonzeroElement} {Slot : Type*} [Fintype Slot]
  {n : ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

def length (D : JointBufferedProductData η w Slot n profileBound a e) : ℝ :=
  D.r₁+D.r₂+∑ j, D.r j

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def value (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (B : Slot → ℝ)
    (Z d : ℝ) (D : JointBufferedProductData η w Slot n profileBound a e) : ℂ :=
  ((Real.sqrt ((Z^d)^D.r₁) : ℂ)⁻¹ * rowTwistedSum D.parent.val
    (fixedBadMask*idealGenerator D.puncture) 1 w.val
    (twistProfile D.plain₁.W D.plain₁.σ D.plain₁.freq) 0 ((Z^d)^D.r₁)) *
  ((Real.sqrt ((Z^d)^D.r₂) : ℂ)⁻¹ * rowTwistedSum D.parent.val
    (fixedBadMask*idealGenerator D.puncture) 1 w.val
    (twistProfile D.plain₂.W D.plain₂.σ D.plain₂.freq) 0 ((Z^d)^D.r₂)) *
  ∏ j, normalizedSlot D.parent.val (fixedBadMask*idealGenerator D.puncture) 1 w.val
    (primePool M H (B j) ((Z^d)^(D.r j)))
    (fun I => idealCoeff (η₀ j).inverse I * annularWeight (V j) ((Z^d)^(D.r j)) (D.σ j) (D.v j) I)
    D.t ((Z^d)^(D.r j))

/-- Only the literal source conductor, profile, frequency and scale gates;
there is no assumed pointwise estimate or nonprincipality premise. -/
structure Admissible (η₀ : Slot → Character) (A B : Slot → ℝ)
    (Rwidth τ ηaux σmin σmax Z d T : ℝ)
    (D : JointBufferedProductData η w Slot n profileBound a e) : Prop where
  r₁_nonneg : 0 ≤ D.r₁
  r₁_le : D.r₁ ≤ Rwidth
  r₂_nonneg : 0 ≤ D.r₂
  r₂_le : D.r₂ ≤ Rwidth
  slots : ∀ j, 0 ≤ D.r j ∧ D.r j ≤ Rwidth ∧ σmin ≤ D.σ j ∧ D.σ j ≤ σmax
  conductor : ∀ label, (bufferedProductFamily M H hH η₀
    (excluded D.natural.character D.puncture) label).modulus.absNorm ≤ Z^d
  freq₁ : |D.plain₁.freq|+Z^τ/2 ≤ (3*D.bin+2 : ℕ)*Z^τ
  freq₂ : |D.plain₂.freq|+Z^τ/2 ≤ (3*D.bin+2 : ℕ)*Z^τ
  freq_slots : ∀ j, |D.t+D.v j|+Z^τ/2 ≤ (3*D.bin+2 : ℕ)*Z^τ
  height_four : (3+(3*D.bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux
  height_two : (3+(3*D.bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux
  log_scale : ∀ j, 2*(|Real.log (A j)|+|Real.log (B j)|)+1 ≤ Real.log ((Z^d)^(D.r j))
  buffer_height : 3*(D.bin+1 : ℕ)*Z^τ ≤ T

omit [Fintype Slot] in
lemma eligible (D : JointBufferedProductData η w Slot n profileBound a e)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val) :
    ¬FixedInducingRow D.parent.val Q (fixedBadMask*idealGenerator D.puncture) 1 w.val := by
  intro hi
  apply hex
  apply (jointParentDictionary_inducing_iff η D.parent Q hQ72 w.val w.property).mp
  exact (fixedInducingRow_mul_mask_iff D.parent.val Q fixedBadMask
    (idealGenerator D.puncture) 1 w.val fixedBadMask_ne_zero
    (idealGenerator_ne_zero D.puncture D.puncture_ne) one_ne_zero w.property
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hi

lemma zeroMaximum_le (η₀ : Slot → Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
    (D : JointBufferedProductData η w Slot n profileBound a e)
    (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val) (T : ℝ) :
    zeroMaximum (bufferedProductFamily M H hH η₀ (excluded D.natural.character D.puncture))
      (bufferedProductFamily_nonprincipal M H hH η₀ D.parent.val w.val D.natural Q D.puncture
        hQM hQη₀ D.puncture_ne w.property (D.eligible Q hQ72 hex)) T ≤
    zeroMaximum (fun label => (momentData (jointRelativeParent η
      (relativeSlotTranslate M H hH η₀) label)).character w)
      (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) w hex) T := by
  apply zeroMaximum_le_of_zero_inclusion
  intro label
  refine ⟨(D.parent,label), ?_⟩
  intro s hs hz
  have hc (I : Ideal O) :
      idealCoeff (bufferedProductFamily M H hH η₀ (excluded D.natural.character D.puncture) label) I =
      idealCoeff (excluded (jointRelativeNaturalFamily η (relativeSlotTranslate M H hH η₀)
        w (D.parent,label)) D.puncture) I := by
    cases label with
    | none =>
      exact jointRelative_plain_coeff M H hH η η₀ w D.parent D.natural
        D.puncture D.puncture_ne I
    | some jθ =>
      exact jointRelative_ray_sector_coeff M H hH η η₀ w D.parent D.natural
        jθ.1 jθ.2 D.puncture D.puncture_ne I
  have hn := jointRelativeNatural_nonprincipal η (relativeSlotTranslate M H hH η₀) Q hQ72
    (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) w hex (D.parent,label)
  exact (positive_zeros_eq_of_mask _ _ hn
    (jointRelativeNatural_momentData_mask η (relativeSlotTranslate M H hH η₀) w (D.parent,label)) hs).mp
    ((excluded_positive_zeros _ D.puncture hn hs).mp
      ((coefficient_equality_positive_zeros _ _ hc (excluded_nonprincipal _ _ hn) hs).mp hz))

end JointBufferedProductData

/-- Uniform actual product bound packaged for joint reconstruction. All
analytic estimates are supplied by the source plain and prime theorems. -/
theorem joint_buffered_data_bound (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    {Slot : Type*} [Fintype Slot]
    (η : Character) (η₀ : Slot → Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
    (V : Slot → ℝ → ℂ) (A B : Slot → ℝ) (hA : ∀ j, 0 < A j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (A j) (B j)) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (Rwidth dmax τ ε e κ ηaux σmin σmax loss : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hloss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ loss)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ (w : NonzeroElement)
        (R : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ label, R label ≠ 0),
      jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) R hR
        p.lower p.upper p.height w →
      ∀ D : JointBufferedProductData η w Slot n profileBound p.lower e,
      D.Admissible M H hH η₀ A B Rwidth τ ηaux σmin σmax Z d p.height →
      ‖D.value M H η₀ V B Z d‖^2 ≤ C*(Z^d)^((2*p.lower-1)*D.length+loss) := by
  obtain ⟨n,C,hC,hbound⟩ := natural_buffered_product_bound M H hH η₀ Q hQM hQη₀
    V A B hA hVs hV Rwidth dmax τ ε e κ ηaux σmin σmax loss hRw hdmax hτ hε
    he he' hκ hκone hη hbudget hprimebudget hloss profileBound hprofile
  refine ⟨n,C,hC,?_⟩
  intro Z d hZ hd hdmax' hbase hT p hp w R hR hbin D hD
  obtain ⟨hex,hlo,hhi⟩ := hbin
  have hmax : zeroMaximum (bufferedProductFamily M H hH η₀
      (excluded D.natural.character D.puncture))
      (bufferedProductFamily_nonprincipal M H hH η₀ D.parent.val w.val D.natural Q D.puncture
        hQM hQη₀ D.puncture_ne w.property (D.eligible Q hQ72 hex))
        (3*(D.bin+1 : ℕ)*Z^τ) < p.lower+2*e := by
    apply (zeroMaximum_mono _ _ hD.buffer_height).trans_lt
    apply (D.zeroMaximum_le M H hH η₀ Q hQ72 hQM hQη₀ hex p.height).trans_lt
    rw [← jointRelativeSource_zeroMaximum η (relativeSlotTranslate M H hH η₀) Q hQ72
      (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) w hex R hR p.height]
    exact hhi.trans_lt hp
  exact hbound Z d hZ hd hdmax' hbase hT D.parent.val w.val D.natural D.puncture
    D.puncture_ne w.property (D.eligible Q hQ72 hex) p.lower D.bin
    (by linarith [p.lower_bound]) (by linarith [p.upper_bound]) hmax
    D.plain₁ D.plain₂ D.r₁ D.r₂ D.r D.σ D.v D.t
    hD.r₁_nonneg hD.r₁_le hD.r₂_nonneg hD.r₂_le hD.slots hD.conductor
    hD.freq₁ hD.freq₂ hD.freq_slots hD.height_four hD.height_two hD.log_scale

#print axioms joint_buffered_data_bound

#print axioms JointBufferedProductData.zeroMaximum_le
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedData -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalNormalization ; sha256 2d623297adf3167ff6a230068830c40103fe41eb90ef91d910ecdb9258171998 -/
section




/-! Original-input coherent exceptional normalization at the enlarged main ball.
The lower plain cap is retained before any allocation. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstChildProfileControl
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
local instance coherentExceptionalNormalizationDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _

open CenteredMomentFirstMixedCommonRadius

theorem actual_coherent_main_exceptional_reference
    (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D))
    (hE : E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
    (K V Z omega M : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hV : 0 < V)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D})
    (hM : 1 ≤ M) (hwidth : M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*M) :
    let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
    ((V/(C.absNorm : ℝ))*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Rmain^(5/6 : ℝ)*Z^(-(3/500 : ℝ))/
      ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))^2*Z^(allowance C D Z)))*
        Z^(-2*max (M/4-Real.logb Z (C.absNorm : ℝ)) 0/3) ≤ Z^(-93/1000+5*omega/6) := by
  dsimp only
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := commonPart_of_equal_support C D hC.1 hCD
  have hd := commonPart_of_equal_support D C hD.1 hCD.symm
  let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
    (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
  have hr : 0 < Rmain := by unfold Rmain mainCommonRadius; positivity
  have hs := actual_main_column_saving η τ fixedBadMask C D E hC hD U
    K V Z 0 (9/500) omega 0 hZ hmod
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq C D hC.1 hD.1 hCD Z] at hs
  have he := actual_exceptional_reference η τ C D hC hD hCD U K V Z 0
    (Real.logb Z Rmain) 0 0 (3/500) hK hV hZ hmod
  dsimp only at he
  rw [←hE] at he
  simp only [zero_add,neg_zero,Real.rpow_zero,mul_one,div_one] at he
  rw [Real.rpow_logb hz hZ.ne' hr] at he
  have hh := mul_le_mul_of_nonneg_right he.le
    (Real.rpow_nonneg hz.le (-2*max (M/4-Real.logb Z (C.absNorm : ℝ)) 0/3))
  apply hh.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  dsimp only [Rmain] at *
  simp only [nominalLog] at hs ⊢
  norm_num only at hs
  simp only [sub_zero,add_zero] at hs ⊢
  have hmax := le_max_left (M/4-Real.logb Z (C.absNorm : ℝ)) (0 : ℝ)
  linarith


/-- The genuine prime average and original coherent volume normalize to
exactly the first common allowance reference. -/
theorem actual_coherent_main_exceptional_scalar
    (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D))
    (hE : E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
    (K V Z omega M P Kphys primeLoss loss : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hV : 0 < V)
    (hP : 0 < P) (hKphys : 0 ≤ Kphys)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D})
    (hM : 1 ≤ M) (hwidth : M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*M)
    (hprime : 1/P ≤ Z^(-(3/500 : ℝ)+primeLoss))
    (hradius : Kphys ≤ mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0) :
    (((C.absNorm : ℝ)*P)⁻¹*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Kphys^(5/6 : ℝ))*
      Z^(loss-2*max (M/4-Real.logb Z (C.absNorm : ℝ)) 0/3) ≤
    ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ)^2)*Z^(allowance C D Z))*
      Z^(-93/1000+5*omega/6+primeLoss+loss) := by
  have hz := zero_lt_one.trans hZ
  have hc := norm_pos C hC.1
  have ht := norm_pos τ.modulus τ.modulus_ne_bot
  let cap := 2*max (M/4-Real.logb Z (C.absNorm : ℝ)) 0/3
  let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
    (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
  have hrpos : 0 < Rmain := by dsimp only [Rmain,mainCommonRadius]; positivity
  let ref := (τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ)^2)*Z^(allowance C D Z)
  have href : 0 < ref := by dsimp only [ref]; positivity
  have hb := actual_coherent_main_exceptional_reference η τ C D E hC hD hCD U hE
    K V Z omega M hZ hK hV hmod hM hwidth hvolume
  dsimp only at hb
  rw [show -2*max (M/4-Real.logb Z (C.absNorm : ℝ)) 0/3 = -cap by
    dsimp only [cap]; ring] at hb
  have hs : (C.absNorm : ℝ)⁻¹*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Rmain^(5/6 : ℝ)*
      Z^(-(3/500 : ℝ))*Z^(-cap) ≤ ref*Z^(-93/1000+5*omega/6) := by
    apply (mul_le_mul_of_nonneg_left hb href.le).trans_eq' ?_
    dsimp only [ref,Rmain]
    field_simp
    <;> ring
  calc
    _ = ((C.absNorm : ℝ)⁻¹*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Kphys^(5/6 : ℝ))*
        (1/P)*Z^(loss-cap) := by dsimp only [cap]; ring
    _ ≤ ((C.absNorm : ℝ)⁻¹*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Rmain^(5/6 : ℝ))*
        Z^(-(3/500 : ℝ)+primeLoss)*Z^(loss-cap) := by
      gcongr
    _ = ((C.absNorm : ℝ)⁻¹*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Rmain^(5/6 : ℝ)*
        Z^(-(3/500 : ℝ))*Z^(-cap))*Z^(primeLoss+loss) := by
      simp only [Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_neg hz.le]
      ring
    _ ≤ (ref*Z^(-93/1000+5*omega/6))*Z^(primeLoss+loss) :=
      mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hz]; dsimp only [ref]; congr 2 <;> ring

#print axioms actual_coherent_main_exceptional_reference
#print axioms actual_coherent_main_exceptional_scalar
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalNormalization -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalNormalization ; sha256 e6412c29285436ebe498c788ffbb88b400ba9f2097b78f50c66e575a5004c12f -/
section




/-! Actual first-child exceptional normalization at the enlarged main ball. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstChildProfileControl
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
local instance jointExceptionalNormalizationDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- This is the actual exceptional reference, with the lower plain lengths
transported through the literal allocation. The fixed conductor is allowed
to enlarge the reference width, rather than strengthening the plain gate. -/
theorem actual_local_main_exceptional_reference
    {ι : Type*} [Fintype ι]
    (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D))
    (hE : E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
    (K V Z omega M : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hV : 0 < V)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D})
    (s : Input ι) (Rmask : Ideal O)
    (B : actualAllocations s.pools (commonPart C D)) (t : ℝ)
    (hM : 1 ≤ M) (hwidth : M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*M)
    (hX₁ : Z^(M/4) ≤ s.X₁) (hX₂ : Z^(M/4) ≤ s.X₂)
    (hY₁ : Z^(M/4) ≤ s.Y₁) (hY₂ : Z^(M/4) ≤ s.Y₂) :
    let d := child s (commonPart C D) Rmask B τ t
    let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
    ((V/(C.absNorm : ℝ))*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Rmain^(5/6 : ℝ)*Z^(-(3/500 : ℝ))/
      ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))^2*Z^(allowance C D Z)))*
        Z^(-2*max (inputCap Z d) 0/3) ≤ Z^(-93/1000+5*omega/6) := by
  dsimp only
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := commonPart_of_equal_support C D hC.1 hCD
  have hd := commonPart_of_equal_support D C hD.1 hCD.symm
  let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
    (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
  have hr : 0 < Rmain := by unfold Rmain mainCommonRadius; positivity
  have hs := actual_main_child_stage η τ fixedBadMask C D E hC hD U
    K V Z 0 (9/500) omega 0 hZ hmod s Rmask B t (Real.logb Z V) M
    hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq C D hC.1 hD.1 hCD Z] at hs
  have he := actual_exceptional_reference η τ C D hC hD hCD U K V Z 0
    (Real.logb Z Rmain) 0 0 (3/500) hK hV hZ hmod
  dsimp only at he
  rw [←hE] at he
  simp only [zero_add,neg_zero,Real.rpow_zero,mul_one,div_one] at he
  rw [Real.rpow_logb hz hZ.ne' hr] at he
  have hh := mul_le_mul_of_nonneg_right he.le
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z (child s (commonPart C D) Rmask B τ t)) 0/3))
  apply hh.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  dsimp only [Rmain] at *
  simp only [nominalLog] at hs ⊢
  norm_num only at hs
  simp only [sub_zero,add_zero] at hs ⊢
  linarith

/-- The actual raw child volume is bounded using its nonzero frozen
coefficient. The clipping cost is fixed by the original slot count. -/
theorem actual_local_main_exceptional_child_core
    {ι : Type*} [Fintype ι]
    (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D))
    (hE : E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
    (K Z omega M : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D})
    (s : Input ι) (Rmask : Ideal O)
    (B : actualAllocations s.pools (commonPart C D)) (t : ℝ)
    (N : ℕ) (b : ℝ) (hb : 1 ≤ b) (hcard : Fintype.card ι ≤ N) (hupper : s.upper ≤ b)
    (hne : frozenCoefficient B.val (commonPart C D) Rmask s.ν s.W s.P ≠ 0)
    (hM : 1 ≤ M) (hwidth : M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ (883/1000)*M)
    (hX₁ : Z^(M/4) ≤ s.X₁) (hX₂ : Z^(M/4) ≤ s.X₂)
    (hY₁ : Z^(M/4) ≤ s.Y₁) (hY₂ : Z^(M/4) ≤ s.Y₂) :
    let V := CenteredMomentAmplificationChildInput.volume s
    let d := child s (commonPart C D) Rmask B τ t
    let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
    (CenteredMomentAmplificationChildInput.volume d)^(1/3 : ℝ)*Rmain^(5/6 : ℝ)*
      Z^(-(3/500 : ℝ))*Z^(-2*max (inputCap Z d) 0/3)/
      ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))*Z^(allowance C D Z)) ≤
        (b^N)^(1/3 : ℝ)*Z^(-93/1000+5*omega/6) := by
  dsimp only
  let V := CenteredMomentAmplificationChildInput.volume s
  let d := child s (commonPart C D) Rmask B τ t
  let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
    (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
  have hV : 0 < V := CenteredMomentAmplificationChildInput.volume_pos s
  have hCpos : 0 < (C.absNorm : ℝ) := norm_pos C hC.1
  have hqpos : 0 < (τ.modulus.absNorm : ℝ) := norm_pos _ τ.modulus_ne_bot
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hbase : 0 < V/(C.absNorm : ℝ) := div_pos hV hCpos
  have hrad : 0 < Rmain := by unfold Rmain mainCommonRadius; positivity
  have hvol := common_volume_le N b hb s hcard hupper (commonPart C D) Rmask B τ t hne
  conv_rhs at hvol => rw [commonPart_of_equal_support C D hC.1 hCD]
  have hvpow : (CenteredMomentAmplificationChildInput.volume d)^(1/3 : ℝ) ≤
      (b^N)^(1/3 : ℝ)*(V/(C.absNorm : ℝ))^(1/3 : ℝ) := by
    have hh := Real.rpow_le_rpow (CenteredMomentAmplificationChildInput.volume_pos d).le hvol
      (by norm_num : (0 : ℝ) ≤ 1/3)
    rw [mul_div_assoc,Real.mul_rpow (pow_nonneg (zero_le_one.trans hb) N) hbase.le] at hh
    exact hh
  have hcap := actual_local_main_exceptional_reference η τ C D E hC hD hCD U hE
    K V Z omega M hZ hK hV hmod s Rmask B t hM hwidth hvolume hX₁ hX₂ hY₁ hY₂
  dsimp only at hcap
  calc
    _ ≤ ((b^N)^(1/3 : ℝ)*(V/(C.absNorm : ℝ))^(1/3 : ℝ))*Rmain^(5/6 : ℝ)*
        Z^(-(3/500 : ℝ))*Z^(-2*max (inputCap Z d) 0/3)/
        ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))*Z^(allowance C D Z)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hvpow (Real.rpow_nonneg hrad.le _))
          (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg hz.le _)) (by positivity)
    _ = (b^N)^(1/3 : ℝ)*
        (((V/(C.absNorm : ℝ))*(V/(C.absNorm : ℝ))^(1/3 : ℝ)*Rmain^(5/6 : ℝ)*Z^(-(3/500 : ℝ))/
          ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))^2*Z^(allowance C D Z)))*
            Z^(-2*max (inputCap Z d) 0/3)) := by
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hb) N) _)

#print axioms actual_local_main_exceptional_reference
#print axioms actual_local_main_exceptional_child_core
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalNormalization -/

/- BEGIN ORIGINAL MODULE Analytic.JointUnitPopulation ; sha256 ca0baf3ff087aa890d82e6f7cbe37a445a7a19e98519915a57d5f8df085f0545 -/
section


/-! The unit in the first signed reconstruction depends on the first
common labels. Splitting into the six actual units has a fixed cost. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily
local notation "O" => HeckeFamily.O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

/-- A nonempty supported window forces both population exponents to be
nonnegative. This prevents using a subunit population estimate on an
actually occupied window. -/
theorem joint_nonempty_window_nonnegative (S : Finset JointReconstructionLabel)
    (unit : JointReconstructionLabel → Oˣ) (Z P W : ℝ)
    (hZ : 1 < Z) (hS : S.Nonempty)
    (hrow : ∀ v ∈ S, v.row (unit v) ≠ 0)
    (hw : ∀ v ∈ S, (Ideal.absNorm (Ideal.span {v.row (unit v)}) : ℝ) ≤ Z^W)
    (hr : ∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (v.row (unit v))) : ℝ) ≤ Z^P) :
    0 ≤ P ∧ 0 ≤ W := by
  obtain ⟨v,hv⟩ := hS
  have hwi : Ideal.span {v.row (unit v)} ≠ (0 : Ideal O) := by simpa using hrow v hv
  have hnw : (1 : ℝ) ≤ (Ideal.span {v.row (unit v)}).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hwi)
  have hnr : (1 : ℝ) ≤ (jointMissingRadical v.C₁ (v.row (unit v))).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (jointMissingRadical_ne_zero v.C₁ (v.row (unit v))))
  constructor
  · by_contra hp
    have hp' := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hp)
    linarith [hr v hv]
  · by_contra hw'
    have hw'' := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hw')
    linarith [hw v hv]

section FixedDensityData
variable {Label : Type*} [Fintype Label]
variable (η : Label → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
  (hQη : ∀ label, Q ≤ (η label).modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_joint_variable_unit_population (B loss : ℝ)
    (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧
      ∀ (Z P W : ℝ), 1 ≤ Z → 0 ≤ P → P ≤ B → 0 ≤ W → W ≤ B →
      ∀ (p : DensityWindow) (unit : JointReconstructionLabel → Oˣ)
        (S : Finset JointReconstructionLabel),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, ∃ hw : v.row (unit v) ≠ 0, rawZeroBin (fun j => momentData (η j))
        p.lower p.upper p.height ⟨v.row (unit v), hw⟩) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {v.row (unit v)}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (v.row (unit v))) : ℝ) ≤ Z^P) →
      (S.card : ℝ) ≤ K*(1+|p.height|)^A*Z^(unmarkedDensity (2*p.lower-1)*W+P+loss) := by
  obtain ⟨A,K,hK,hcount⟩ := actual_joint_population_polynomial η Q hQtop hQ72 hQη hβ
    M H hH S₀ φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    hβupper B loss hB hloss
  refine ⟨A,6*K,by positivity,?_⟩
  intro Z P W hZ hP hPB hW hWB p unit S hsup heq hproj hbin hnorm hNw hNr
  let bound := K*(1+|p.height|)^A*Z^(unmarkedDensity (2*p.lower-1)*W+P+loss)
  have hfiber (u : Oˣ) : ((S.filter (fun v => unit v=u)).card : ℝ) ≤ bound := by
    apply hcount Z P W hZ hP hPB hW hWB p u
    · intro v hv
      exact hsup v (Finset.mem_filter.mp hv).1
    · intro v hv
      exact heq v (Finset.mem_filter.mp hv).1
    · intro v hv
      exact hproj v (Finset.mem_filter.mp hv).1
    · intro v hv
      simpa only [(Finset.mem_filter.mp hv).2] using hbin v (Finset.mem_filter.mp hv).1
    · intro v hv
      exact hnorm v (Finset.mem_filter.mp hv).1
    · intro v hv
      simpa only [(Finset.mem_filter.mp hv).2] using hNw v (Finset.mem_filter.mp hv).1
    · intro v hv
      simpa only [(Finset.mem_filter.mp hv).2] using hNr v (Finset.mem_filter.mp hv).1
  have hcard : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  calc
    (S.card : ℝ) = ∑ u : Oˣ, ((S.filter (fun v => unit v=u)).card : ℝ) := by
      exact_mod_cast card_eq_sum_buffered_fibers S unit
    _ ≤ ∑ _u : Oˣ, bound := Finset.sum_le_sum (fun u _ => hfiber u)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; dsimp [bound]; ring

end FixedDensityData
#print axioms actual_joint_variable_unit_population
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointUnitPopulation -/
