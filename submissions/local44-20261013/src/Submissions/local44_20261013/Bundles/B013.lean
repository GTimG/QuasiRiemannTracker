/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B008
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B010
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentNaturalFixedRaySourceFixedIdeal ; sha256 667d1cd0159b485eb5e7f3bf794ce7d72bce8cba24dd562ceeb4a219f264b057 -/
section





namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalFixedRaySource Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {D : Cycle25.Weighted.MomentData}

def weighted_sourceFixedIdeal (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma weighted_sourceFixedIdeal_ne_zero (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma weighted_sourceFixedIdeal_ne_top (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus ≤ Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=> P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : weighted_sourceFixedIdeal F ≤ Ideal.span {goodLambda})))

lemma weighted_sourceFixedIdeal_le_modulus (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ F.modulus := inf_le_left
lemma weighted_sourceFixedIdeal_le_72 (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ Ideal.span {(72:O)} := inf_le_right

def weighted_sourceExceptional (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (weighted_sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

end SevenEighths.Cycle25CenteredMomentNaturalFixedRaySource

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentNaturalFixedRaySourceFixedIdeal -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.SourceAmplitudeClasses ; sha256 12486589a4b78ee673e2e3a239b59f3ca3c316ed04f06d2a69cfdfb0a1d73ee2 -/
section





/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Cycle25WeightedHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_source_amplitude_batches (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth κplain : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hkplain : 7/10≤κplain) (hkplain1 : κplain≤3/4) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤7/8 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → (7/37)*dmax≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
      W upper (fun j=> ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
    W upper (fun j=> ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hqb := HeckeDetectorAmplitudeFirst.classMean_bounds rows Finset.univ (Z^d) (2*a-1)
    binWidth hb (fun j=> ell j/d) Q bin (by linarith)
    (fun j _=>(div_pos (hell j) (by linarith : 0< d)).le)
    (by rw [←Finset.sum_div]; exact div_pos (by nlinarith) (by linarith)) hne'
  have hdelta : 0<2*a-1 := by linarith
  have hcut := Cycle25DetectorRowCount.cutoff_bounds (δ:=2*a-1) (p:=q/(2*a-1))
    hdelta.le (by linarith) (div_nonneg hqb.1 hdelta.le)
    ((div_le_iff₀ hdelta).mpr (by linarith [hqb.2])) hkplain hkplain1
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=> hcal u (hsub hu)) (fun u hu=> hrow u (hsub hu)) a i hi ha (by linarith)
      (fun u hu=> hnext u (hsub hu)) (fun u hu=> hcurrent u (hsub hu))
      (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=> ell j/d) Q bin u hu'
end SevenEighths.Cycle25WeightedHighRowFamily

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.SourceAmplitudeClasses -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Parameters ; sha256 c4237d0be578f95a5fa606684dd3b66a1eddf8d8ac48afd45e19d59c856b11b7 -/
section


/-! Physical geometry at the exact Cycle25 algebraic boundary. -/
noncomputable section
namespace Cycle25

def theta : ℝ := Arithmetic.b0
def ell : ℝ := Arithmetic.ell0
def lx : ℝ := Arithmetic.x0
def ly : ℝ := Arithmetic.y0
def h : ℝ := Arithmetic.h0
def b : ℝ := ly-lx
def rowExtension : ℝ := 1/1000000
def signal (s : ℝ) : ℝ := s-(4+b)/6

theorem ell_interval : (16712:ℝ)/100000 < ell ∧ ell < 167121/1000000 :=
  Arithmetic.ell0_short_interval
theorem h_interval : (793:ℝ)/1000 < h ∧ h < 795/1000 := Arithmetic.h0_interval
theorem theta_eq : theta = 11/12-ell/4 := rfl
theorem theta_pos : 0 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_gt_half : (1:ℝ)/2 < theta := by rw [theta_eq]; linarith [ell_interval.2]
theorem theta_lt_seven_eighths : theta < (7:ℝ)/8 := by rw [theta_eq]; linarith [ell_interval.1]
theorem theta_lt_one : theta < 1 := theta_lt_seven_eighths.trans (by norm_num)
theorem length_sum : lx+ly = 1-ell := by unfold lx ly ell Arithmetic.x0 Arithmetic.y0; ring
theorem length_difference : ly-lx=b := rfl
theorem row_endpoint : h=1-lx+ell := by unfold h lx ell Arithmetic.x0; ring
theorem y_endpoint : ly=h-2*ell := rfl
theorem signal_low : signal theta=lx/2+b/12 := by
  rw [signal,theta_eq]
  have := length_sum
  unfold b
  linarith
theorem signal_slope (s t : ℝ) : signal s-signal t=s-t := by unfold signal; ring
theorem ell_pos : 0 < ell := by linarith [ell_interval.1]
theorem ell_lt_one_fifth : ell < (1:ℝ)/5 := by linarith [ell_interval.2]
theorem x_rescaled_pos : 0 < lx-ell := sub_pos.mpr Arithmetic.physical_geometry.1
theorem b_pos : 0 < b := sub_pos.mpr Arithmetic.physical_geometry.2.1
theorem ly_lt_half : ly < (1:ℝ)/2 := Arithmetic.physical_geometry.2.2.2.1
theorem ly_coarse : (458:ℝ)/1000 < ly ∧ ly < 461/1000 := by
  rw [y_endpoint]
  constructor <;> linarith [h_interval.1,h_interval.2,ell_interval.1,ell_interval.2]
theorem y_rescaled_pos : 0 < ly-ell := by linarith [ly_coarse.1,ell_interval.2]
theorem row_rescaled_pos : 0 < 1-3*ell := by linarith [ell_interval.2]
theorem gram_domination : 0 < ly-ell-(11:ℝ)/6*b := by
  have := length_sum
  unfold b
  linarith [ly_coarse.2,ell_interval.2]
theorem h_pos : 0 < h := by linarith [h_interval.1]
theorem h_gt_half : (1:ℝ)/2 < h := by linarith [h_interval.1]
theorem h_lt_one : h < 1 := by linarith [h_interval.2]
theorem rowExtension_pos : 0 < rowExtension := by norm_num [rowExtension]
theorem extended_row_count_supply : (7:ℝ)/37 < ell/(h+rowExtension) := by
  apply (lt_div_iff₀ (add_pos h_pos rowExtension_pos)).2
  norm_num [rowExtension]
  linarith [ell_interval.1,h_interval.2]
theorem row_count_supply : (7:ℝ)/37 < ell/h := by
  apply (lt_div_iff₀ h_pos).2
  linarith [ell_interval.1,h_interval.2]
theorem row_extension_supply : h < 5*ell := by linarith [h_interval.2,ell_interval.1]
theorem numerator_short : h < 2*ly := Arithmetic.physical_geometry.2.2.2.2.2
theorem extended_numerator_short : h+rowExtension < 2*ly := by
  rw [y_endpoint]
  norm_num [rowExtension]
  linarith [h_interval.1,ell_interval.2]
theorem extended_h_lt_one : h+rowExtension < 1 := by
  norm_num [rowExtension]
  linarith [h_interval.2]
theorem extended_row_supply : h+rowExtension < 5*ell := by
  norm_num [rowExtension]
  linarith [h_interval.2,ell_interval.1]
theorem numerator_supply_all {kap d : ℝ} (hk : 7/10 ≤ kap) (hd : (1:ℝ)/2 ≤ d) :
    (2*ly-d)/(6*kap) < ell := by
  apply (div_lt_iff₀ (by linarith : 0 < 6*kap)).2
  have hprod := mul_le_mul_of_nonneg_left hk ell_pos.le
  nlinarith [ly_coarse.2,ell_interval.1]
theorem low_rescaled_tuple {v : ℝ} (hv : 0 ≤ v) :
    -v+max 0 (5*ell-1+v)/8 ≤ 0 := by
  have hm : max 0 (5*ell-1+v) ≤ 8*v := max_le (by linarith) (by linarith [ell_lt_one_fifth])
  linarith
theorem low_rescaled_identity (v : ℝ) :
    (1-ell-2*v)+(ell-v)-1 = -3*v := by ring
theorem small_row_margin : h*(17/50-1/6)-ly/2+(63:ℝ)/5000 < 0 := by
  dsimp only [h,ly]
  linarith [Arithmetic.small_row_margin]
theorem principal_w_margin : 0 < ly/20 := by linarith [ly_coarse.1]
theorem principal_z_margin : 0 < h/600 := by linarith [h_pos]

end Cycle25
end
/- END ORIGINAL MODULE Cycle25.Assembly.Parameters -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.Discarded ; sha256 05e6dc579e2614d20adf8865f778e4af74937a01fc8f6a4ea2e25689b454db06 -/
section



noncomputable section
set_option maxHeartbeats 800000
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.Numerator.PhysicalTail
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionMass
local notation "O" => HeckeFamily.O

/-- The exact coefficient cutoff bounds every discarded dual length uniformly.
Neither a scale-bin assumption nor a pointwise critical-line L-bound is needed. -/
theorem discardedSchwartz_active_negligible (xi saving epsilon b Ccond : ℝ)
    (hxi : 0< xi) (heps : 0< epsilon) (hb : 0< b) (hCcond : 0< Ccond) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀(τ ψ : Character)(G : 𝓢(ℝ,ℂ))(Y N U : ℝ),
      0< Y → 0< N → N≤ b*Y → 1≤ U →
      (ψ.modulus.absNorm:ℝ)*(redundantIdeal τ.modulus ψ.modulus).absNorm≤ Ccond*U →
      ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*U^(epsilon-saving) := by
  obtain ⟨H,C,hC,hbound⟩ := deleted_discarded_negligible xi saving 1 (b*Ccond) epsilon
    hxi (mul_pos hb hCcond) heps
  refine ⟨H,C*Ccond^epsilon,by positivity,?_⟩
  intro τ ψ G Y N U hY hN hcut hU hcap
  let S := redundantSet τ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hQone : (1:ℝ)≤ψ.modulus.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hnorm : (Ideal.absNorm (∏P∈S,P):ℝ)≤ Ccond*U := by
    have hr : 0≤(Ideal.absNorm (∏P∈S,P):ℝ) := by positivity
    have hl := mul_le_mul_of_nonneg_right hQone hr
    exact (show (Ideal.absNorm (∏P∈S,P):ℝ)≤(ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ) by simpa only [one_mul] using hl).trans hcap
  have hYX : 1≤ b*(Y/N) := by
    rw [←mul_div_assoc,le_div_iff₀ hN]
    simpa using hcut
  have hscale : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤
      (b*Ccond)*U^(1:ℝ)*(Y/N) := by
    calc
      _ ≤ Ccond*U := hcap
      _ ≤ (Ccond*U)*(b*(Y/N)) := le_mul_of_one_le_right (by positivity) hYX
      _ = _ := by rw [Real.rpow_one];ring
  have hh := (hbound G S hS ψ ψ.inverse τ.inverse (ψ.modulus.absNorm:ℝ) (Y/N) U
    hU hQ (div_pos hY hN) hscale).2
  change ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤_ at hh
  have hG : 0≤ H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hU0 : 0< U := zero_lt_one.trans_le hU
  calc
    _ ≤ C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*U^(-saving) := hh
    _ ≤ C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Ccond*U)^epsilon*U^(-saving) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hCcond.le hU0.le,Real.rpow_sub hU0]
      rw [Real.rpow_neg hU0.le]
      ring


/-- Once the physical profile is fixed, the complete discarded packet has an
arbitrary inverse-power bound at every active coefficient scale. -/
theorem discardedSchwartz_fixed_profile (xi saving b Ccond : ℝ)
    (hxi : 0< xi) (hb : 0< b) (hCcond : 0< Ccond) (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0< C ∧ ∀(τ ψ : Character)(Y N U : ℝ),
      0< Y → 0< N → N≤ b*Y → 1≤ U →
      (ψ.modulus.absNorm:ℝ)*(redundantIdeal τ.modulus ψ.modulus).absNorm≤ Ccond*U →
      ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤ C*U^(-saving) := by
  obtain ⟨H,C,hC,hbound⟩ := discardedSchwartz_active_negligible xi (saving+1) 1 b Ccond
    hxi (by norm_num) hb hCcond
  have hG : 0≤ H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  refine ⟨C*(H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G+1),by positivity,?_⟩
  intro τ ψ Y N U hY hN hcut hU hcap
  have hh := hbound τ ψ G Y N U hY hN hcut hU hcap
  rw [show (1:ℝ)-(saving+1) = -saving by ring] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G+1) hC.le) (by positivity))

lemma fourth_norm_add (a b : ℂ) : ‖a+b‖^4≤8*(‖a‖^4+‖b‖^4) := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 4).trans
    (by convert add_pow_le (norm_nonneg a) (norm_nonneg b) 4 using 1 <;> norm_num)

theorem weighted_fourth_add {ι : Type*} (s : Finset ι) (R T Q : ι→ℂ) (Er Et : ℝ)
    (hr : (∑i∈s,‖R i‖^4*‖Q i‖^2)≤ Er)
    (ht : (∑i∈s,‖T i‖^4*‖Q i‖^2)≤ Et) :
    (∑i∈s,‖R i+T i‖^4*‖Q i‖^2)≤8*(Er+Et) := by
  calc
    _ ≤ ∑i∈s,8*(‖R i‖^4+‖T i‖^4)*‖Q i‖^2 :=
      Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (fourth_norm_add _ _) (sq_nonneg _))
    _ = 8*((∑i∈s,‖R i‖^4*‖Q i‖^2)+(∑i∈s,‖T i‖^4*‖Q i‖^2)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,add_mul,mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    _ ≤ _ := by linarith

/-- Polynomial pointwise tails are negligible even with all selected factors. -/
theorem selected_tail_fourth {ι : Type*} (s : Finset ι) (T Q : ι→ℂ)
    (U r q saving Ccard Ctail Cslot : ℝ) (hU : 0< U)
    (hc : 0≤ Ccard) (ht : 0≤ Ctail) (hq : 0≤ Cslot)
    (hcard : (s.card:ℝ)≤ Ccard*U^r)
    (htail : ∀i∈s,‖T i‖≤ Ctail*U^(-saving))
    (hslot : ∀i∈s,‖Q i‖≤ Cslot*U^q) :
    (∑i∈s,‖T i‖^4*‖Q i‖^2)≤ Ccard*Ctail^4*Cslot^2*U^(r+2*q-4*saving) := by
  calc
    _ ≤ ∑i∈s,(Ctail*U^(-saving))^4*(Cslot*U^q)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (htail i hi) 4)
        (pow_le_pow_left₀ (norm_nonneg _) (hslot i hi) 2) (sq_nonneg _) (by positivity)
    _ = (s.card:ℝ)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) := by simp
    _ ≤ (Ccard*U^r)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hpow (e : ℝ) (n : ℕ) : (U^e)^n=U^(e*n) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
      rw [mul_pow,mul_pow,hpow,hpow]
      calc
        _ = Ccard*Ctail^4*Cslot^2*(U^r*U^(-saving*4)*U^(q*2)) := by ring
        _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU];congr 2;ring


/-- The crude lattice count alone suffices for all discarded selected moments;
its constant is independent of any source-moment constant C0. -/
theorem row_discarded_fourth_negligible (xi saving q b Ccond Cslot : ℝ)
    (hxi : 0< xi) (hb : 0< b) (hCcond : 0< Ccond) (hslot0 : 0< Cslot)
    (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0< C ∧ ∀(rows : Finset FreeRow)(τ ψ : FreeRow→Character)
      (N : FreeRow→ℝ)(Q : FreeRow→ℂ)(Y U : ℝ),
      0< Y → 1≤ U → (∀u∈rows,0< N u ∧ N u≤ b*Y) →
      (∀u∈rows,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ U) →
      (∀u∈rows,((ψ u).modulus.absNorm:ℝ)*
        (redundantIdeal (τ u).modulus (ψ u).modulus).absNorm≤ Ccond*U) →
      (∀u∈rows,‖Q u‖≤ Cslot*U^q) →
      (∑u∈rows,‖discardedSchwartz (τ u) (ψ u) G (Y/N u) (U^(xi/2))‖^4*‖Q u‖^2)≤ C*U^(-saving) := by
  let s : ℝ := (1+2*q+saving)/4
  obtain ⟨C,hC,hbound⟩ := discardedSchwartz_fixed_profile xi s b Ccond hxi hb hCcond G
  refine ⟨128*C^4*Cslot^2,by positivity,?_⟩
  intro rows τ ψ N Q Y U hY hU hN hrows hcap hslot
  have hh := selected_tail_fourth rows
    (fun u=> discardedSchwartz (τ u) (ψ u) G (Y/N u) (U^(xi/2))) Q
    U 1 q s 128 C Cslot (zero_lt_one.trans_le hU) (by norm_num) hC.le hslot0.le
    (by simpa using ProbeHighRowFamily.freeRow_count rows U hU hrows)
    (fun u hu=> hbound (τ u) (ψ u) Y (N u) U hY (hN u hu).1 (hN u hu).2 hU (hcap u hu)) hslot
  convert hh using 1
  dsimp only [s]
  congr 2
  ring


theorem subtype_discarded_fourth_negligible (xi saving q b Ccond Cslot : ℝ)
    (hxi : 0< xi) (hb : 0< b) (hCcond : 0< Ccond) (hslot0 : 0< Cslot)
    (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0< C ∧ ∀(rows : Finset FreeRow)(τ ψ : rows→Character)
      (N : rows→ℝ)(Q : rows→ℂ)(Y U : ℝ),
      0< Y → 1≤ U → (∀i,0< N i ∧ N i≤ b*Y) →
      (∀u∈rows,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ U) →
      (∀i,((ψ i).modulus.absNorm:ℝ)*
        (redundantIdeal (τ i).modulus (ψ i).modulus).absNorm≤ Ccond*U) →
      (∀i,‖Q i‖≤ Cslot*U^q) →
      (∑i:rows,‖discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/2))‖^4*‖Q i‖^2)≤ C*U^(-saving) := by
  let s : ℝ := (1+2*q+saving)/4
  obtain ⟨C,hC,hbound⟩ := discardedSchwartz_fixed_profile xi s b Ccond hxi hb hCcond G
  refine ⟨128*C^4*Cslot^2,by positivity,?_⟩
  intro rows τ ψ N Q Y U hY hU hN hrows hcap hslot
  have hh := selected_tail_fourth Finset.univ
    (fun i:rows=> discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/2))) Q
    U 1 q s 128 C Cslot (zero_lt_one.trans_le hU) (by norm_num) hC.le hslot0.le
    (by simpa using ProbeHighRowFamily.freeRow_count rows U hU hrows)
    (fun i _=> hbound (τ i) (ψ i) Y (N i) U hY (hN i).1 (hN i).2 hU (hcap i))
    (fun i _=> hslot i)
  convert hh using 1
  dsimp only [s]
  congr 2
  ring

/-- Exact unit-modulus reflection transfers the retained weighted fourth moment
to the original polynomial, with a separately certified tail contribution. -/
theorem original_split_weighted_fourth {ι : Type*} (s : Finset ι)
    (P R T g Q : ι→ℂ) (D : ι→ℝ) (Er Et : ℝ)
    (hD : ∀i∈s,1≤ D i) (hg : ∀i∈s,‖g i‖=1)
    (heq : ∀i∈s,P i=g i*(R i+T i))
    (hr : (∑i∈s,‖R i/(D i:ℂ)‖^4*‖Q i‖^2)≤ Er)
    (ht : (∑i∈s,‖T i‖^4*‖Q i‖^2)≤ Et) :
    (∑i∈s,‖P i/(D i:ℂ)‖^4*‖Q i‖^2)≤8*(Er+Et) := by
  have htail : (∑i∈s,‖T i/(D i:ℂ)‖^4*‖Q i‖^2)≤ Et := by
    apply (Finset.sum_le_sum (fun i hi=>?_)).trans ht
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (hD i hi))]
    exact div_le_self (norm_nonneg _) (hD i hi)
  have hnorm (i : ι) (hi : i∈s) : ‖P i/(D i:ℂ)‖=‖R i/(D i:ℂ)+T i/(D i:ℂ)‖ := by
    rw [heq i hi,mul_div_assoc,norm_mul,hg i hi,one_mul,add_div]
  simp_rw [Finset.sum_congr rfl (fun i hi=> congrArg (fun t : ℝ=> t^4*‖Q i‖^2) (hnorm i hi))]
  exact weighted_fourth_add s (fun i=> R i/(D i:ℂ)) (fun i=> T i/(D i:ℂ)) Q Er Et hr htail

end Cycle25.Weighted.Numerator.PhysicalTail
end

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.Discarded -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.RetainedGeometry ; sha256 f6342630d58980faf523ab39a2eff5b43a784fbe0e82cdc2c6f638178d71f66b -/
section




namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily CenteredMomentRetainedWeightedSource CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentNaturalPrimitive CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionTailMass
open CenteredMomentReflectionRetainedLength CenteredMomentSectorLocalization

/-- All natural primitive/deletion scales obey the combined conductor bound;
no individual deletion factor is charged a second time. -/
lemma actual_dual_scale_bound (τ ψ : Character) (X B : ℝ) (hX : 0 < X)
    (hcap : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes τ ψ,P):ℝ) ≤ B*X)
    (D : (sourcePrimes τ ψ).powerset) (I : SmoothIdeal (sourcePrimes τ ψ)) :
    dualScale τ ψ X D I ≤ B := by
  have hQ : 0 < (ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact (dual_scale_bounds (sourcePrimes τ ψ) D.val (redundantSet_prime _ _)
    (Finset.mem_powerset.mp D.property) I _ X B hQ hX hcap).2

/-- A uniform logarithmic scale interval for every retained annulus and every
rowwise coefficient dilation, under only its combined-scale bound. -/
theorem eventually_retained_log_interval (C xi : ℝ) (hC : 0 < C) (hxi : 0 < xi) :
    ∀ᶠU:ℝ in atTop, 1 < U ∧ ∀(τ ψ:Character) (X m:ℝ), 0 < X →
      (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes τ ψ,P):ℝ) ≤ C*U^m*X →
      ∀a:CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes τ ψ),
      ∀hY:0 < dualScale τ ψ X a.1.1 a.1.2,
      a.2 ∈ retainedAnnuli (U^(xi/4)) (dualScale τ ψ X a.1.1 a.1.2) hY →
      Real.log (dyadicScale a.2*dualScale τ ψ X a.1.1 a.1.2) ∈
        Set.Icc 0 ((m+xi)*Real.log U) := by
  have hc : ∀ᶠU:ℝ in atTop, 4*C ≤ U^(3*xi/4) :=
    (tendsto_rpow_atTop (by linarith:0 < 3*xi/4)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with U hc hU
  refine ⟨hU,?_⟩
  intro τ ψ X m hX hcap a hY ha
  have hz := zero_lt_one.trans hU
  have hlow := retained_scale_lower _ _ hY _ ha
  have hdual := actual_dual_scale_bound τ ψ X (C*U^m) hX hcap a.1.1 a.1.2
  have hscale : dyadicScale a.2 ≤ 4*U^(xi/4) :=
    retained_scale_le _ _ ((retainedAnnuli_mem _ _ hY _).mp ha).1
  have hupper : dyadicScale a.2*dualScale τ ψ X a.1.1 a.1.2 ≤ U^(m+xi) := by
    calc
      _ ≤ (4*U^(xi/4))*(C*U^m) :=
        mul_le_mul hscale hdual hY.le (by positivity)
      _ = (4*C)*U^(xi/4)*U^m := by ring
      _ ≤ U^(3*xi/4)*U^(xi/4)*U^m := by gcongr
      _ = U^(m+xi) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  refine ⟨Real.log_nonneg hlow,?_⟩
  calc
    _ ≤ Real.log (U^(m+xi)) := Real.log_le_log (zero_lt_one.trans_le hlow) hupper
    _ = _ := by rw [Real.log_rpow hz]

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.RetainedGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.SourceState ; sha256 2244f9fb94cf780737d291bf1872b5bba232f1d1f879a3c59996f0d34e7a9026 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open UniqueFactorizationMonoid CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {D : Cycle25.Weighted.MomentData}

def weighted_sourceFixedIdeal (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma weighted_sourceFixedIdeal_ne_zero (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma weighted_sourceFixedIdeal_ne_top (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus ≤ Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=> P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : weighted_sourceFixedIdeal F ≤ Ideal.span {goodLambda})))

lemma weighted_sourceFixedIdeal_le_modulus (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ F.modulus := inf_le_left
lemma weighted_sourceFixedIdeal_le_72 (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ Ideal.span {(72:O)} := inf_le_right

def weighted_sourceExceptional (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (weighted_sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

def weighted_sourceExceptionalBound (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (weighted_sourceFixedIdeal F) η)).toFinset

lemma weighted_source_exceptional_norm (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character)
    (u : FreeRow) (hu : weighted_sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm ≤ weighted_sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=> prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (weighted_sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

lemma weighted_source_keep_iff (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val↔¬weighted_sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma weighted_source_fixed_gates (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    internalQ (weighted_sourceFixedIdeal F) η≠0 ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ F.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ η.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)⟩

end SevenEighths.Cycle25WeightedNumeratorPhysical

end

end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.SourceState -/
