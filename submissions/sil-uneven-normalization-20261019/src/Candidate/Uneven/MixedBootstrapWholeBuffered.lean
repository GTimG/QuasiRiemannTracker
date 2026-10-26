import Candidate.Cycle63.Marked.Route.ActualWitnesses
import Candidate.Uneven.BootstrapAssembly
import Candidate.Uneven.MixedBootstrapActualWeighted
import Candidate.Cycle63.Marked.Route.ActualWeightedCount
import Candidate.Uneven.BootstrapMonotone
import Candidate.Cycle63.Marked.DeletionMaxAmplitude
import Candidate.Uneven.SaturatedUnmarked
import Candidate.Cycle63.Marked.WholeBufferedMax
import Candidate.Uneven.MixedBootstrapFamilyMaximum
import Candidate.Cycle63.Marked.WholeNaturalBatch
import Candidate.Cycle63.Marked.WholeFamilyMaximum
import Candidate.Cycle63.Marked.Route.ActualMaxWeighted

/- Original module: Candidate.Uneven.BootstrapWitnesses. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.BootstrapActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment BootstrapAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤ H}
variable {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

/-- The adaptive detector witnesses are constructed from actual buffered zero
maxima, uniformly for every amplitude bin, including unused rounded bins. -/
theorem actual_adaptive_supported_witnesses
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*η)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤ η)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*η≤ ε/2) :
    ∃Z₀ : ℝ,∀Z : ℝ,Z₀≤ Z → ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀{Row : Type}(χ : Row→Label→Character)(hχ : ∀u j,(χ u j).residue≠1),
      ∀(a binWidth : ℝ)(i : ℕ),i≤ I → 31/50≤2*a-1 → 2*a-1≤33/50 →
      0< binWidth → binWidth≤(2*a-1)/2 →
      (∀u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u,a≤ HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i:ℕ)*Z^τ)) →
      (∀u j,(χ u j).modulus.absNorm≤ Z^d) →
      ∀(slots : Finset Slot)(widths : Slot→ℝ),(∀s∈slots,0≤ widths s) →
      0<(∑s∈slots,widths s) →
      Nonempty (∀bin : BinLabel slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
          (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
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
  exact ⟨fun bin=> Classical.choice (hbinWitness bin)⟩

end OAI.SevenEighths.BootstrapActualWeighted
end

/- Original module: Candidate.Uneven.MixedBootstrapActualWitnesses. -/
section
/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.MixedBootstrapActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open CenteredMomentNaturalRowSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment BootstrapAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤  H}
variable {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

theorem actual_weighted_from_buffered_maxima_fixedmesh
    (coarse anchor : Label→Character) (u₀ : O) (F₀ : ∀j,NaturalRow (coarse j) u₀)
    (R₀ : Ideal O) (hu₀ : u₀≠0) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j ≤  M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j) ≤  Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ Δ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2  ≤  bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<η)
    (hΔ0 : 0 ≤  Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ) ≤  HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta  ≤  7/8) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin ≤  dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε ≤ 1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw ≤ 1) (hηw : 0 ≤  ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw ≤  ε/2),
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
      ∀d : ℝ,dmin ≤  d → d ≤  dmax →
      ∀B : NaturalBatch (Slot:=Slot) M H hH (fun j=> excluded (F₀ j).character R₀) anchor bad W (33/50) (33/50) (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i ≤  I →
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      0 ≤  mesh → mesh ≤  Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈B.slots,B.widths s ≤  mesh) → 0<(∑s∈B.slots,B.widths s) →
      0 ≤  height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ ≤  height →
      (∀s∈B.slots,|B.relativeHeight s| ≤  height) → (∀u∈B.rows,|B.commonHeight u| ≤  height) →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u : B.rows,a ≤  HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm ≤  Z^d) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖ ≤ ((Z^d)^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2) ≤ 
        C*(1+height)^J*
        (Z^d)^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
          401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_uniform_fixedmesh (Slot:=Slot) M H hH
    coarse anchor u₀ F₀ R₀ hu₀ bad hbadM hbad0 hbadTop hbad72 Sbad hbad setup W bΦ Δ εm binWidth η hWs hW hbΦ hrad
    hbin hη hΔ0 hΔ hεm hβ hβhi
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Z₀,hwitness⟩ := BootstrapActualWeighted.actual_adaptive_supported_witnesses (Label:=Label) (Slot:=Slot)
    dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε he he' hκw hκw' hηw hbudget
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hfield
  have hlarge : ∀ᶠ Z : ℝ in atTop,U₀ ≤  Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀)
  refine ⟨C,hC,?_⟩
  filter_upwards [hlarge,eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hlarge hZ₀ hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' B a mesh height i hi ha0 ha hmesh hmeshmax' hmeshaux hbin' hwm hL hh hf hv hchoice
    hχ hnext hcurrent hmod hQ
  have hthreshold : U₀ ≤  Z^d := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hd)
  have hfield := hU₀ (Z^d) hthreshold
  by_cases hne : B.rows.Nonempty
  · obtain ⟨u₀,hu₀⟩ := hne
    obtain ⟨w⟩ := hwitness Z hZ₀ d hd hd' (fun u:B.rows=> B.family u.val)
      (fun u=> hχ u.val u.property) a binWidth i hi ha0 ha hbin hbin' hnext hcurrent
      (fun u=> hmod u.val u.property) B.slots B.widths
      (fun s hs=>(B.widthsPositive s hs).le) hL
    let urow : B.rows := ⟨u₀,hu₀⟩
    exact hfield.2 (B.retracted urow) a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) mesh height i
      ha0 ha hε hεsmall hmesh hmeshmax' hmeshaux hbin' hwm hL hh hf hv hchoice
      (fun bin u=> w bin (supportedRowRetraction B.rows urow u)) hQ
  · have hempty : B.rows=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty,Finset.sum_empty]
    have hUp : 0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    positivity

end OAI.SevenEighths.MixedBootstrapActualWeighted
end

/- Original module: Candidate.Uneven.BootstrapMax. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators
namespace Sil.Uneven.Bootstrap


theorem max_weighted_row_sum {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C d loss : ℝ)
    (hw : ∀s∈slots,0≤ w s) (hU : 1≤ U) (hC : 0≤ C)
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50)
    (hsub : ∀J⊆slots,(∑u∈rows,‖∏s∈J,Q u s‖^2) ≤
      C*U^(count d (∑s∈J,w s)+d*(∑s∈J,w s)+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(count d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss) := by
  have hs (J : Finset Slot) (hJ:J⊆slots) :
      count d (∑s∈J,w s)+d*(∑s∈J,w s)+loss ≤
      count d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss := by
    apply add_le_add _ (le_refl loss)
    exact full_exponent_mono hd0 hd
      (Finset.sum_le_sum_of_subset_of_nonneg hJ (fun s hs _=> hw s hs))
  calc
    _ ≤ ∑u∈rows,∑J∈slots.powerset,‖∏s∈J,Q u s‖^2 :=
      Finset.sum_le_sum (fun u _=> OAI.SevenEighths.Deletion26.max_product_le_powerset slots (Q u))
    _ = ∑J∈slots.powerset,∑u∈rows,‖∏s∈J,Q u s‖^2 := Finset.sum_comm
    _ ≤ ∑J∈slots.powerset,C*U^(count d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJs := Finset.mem_powerset.mp hJ
      exact (hsub J hJs).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU (hs J hJs)) hC)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

theorem max_weighted_row_sum_of_nonempty {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C d loss : ℝ)
    (hw : ∀s∈slots,0≤ w s) (hU : 1≤ U) (hC : 0≤ C)
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50)
    (hcount : (rows.card : ℝ)≤ C*U^(Saturated.rho d+loss))
    (hsub : ∀J⊆slots,J.Nonempty → (∑u∈rows,‖∏s∈J,Q u s‖^2) ≤
      C*U^(count d (∑s∈J,w s)+d*(∑s∈J,w s)+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(count d (∑s∈slots,w s)+d*(∑s∈slots,w s)+loss) := by
  apply max_weighted_row_sum rows slots Q w U C d loss hw hU hC hd0 hd
  intro J hJ
  rcases J.eq_empty_or_nonempty with rfl|hne
  · simp only [Finset.prod_empty,norm_one,one_pow,Finset.sum_const,Finset.sum_empty,
      nsmul_eq_mul,mul_one,mul_zero,add_zero]
    exact hcount.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (add_le_add (zero_width_count hd0 hd).symm.le (le_refl loss))) hC)
  · exact hsub J hJ hne

end Sil.Uneven.Bootstrap
end

/- Original module: Candidate.Uneven.MixedBootstrapActualMax. -/
section
/- Independent coarse source and relative anchor. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.MixedBootstrapActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Marked830Assembly
open CenteredMomentNaturalRowSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤  H)

theorem actual_max_weighted_from_buffered_maxima_fixedmesh
    (coarse anchor : Label→Character) (u₀ : O) (F₀ : ∀j,NaturalRow (coarse j) u₀)
    (R₀ : Ideal O) (hu₀ : u₀≠0) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j ≤  M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j) ≤  Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ Δ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2  ≤  bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<η)
    (hΔ0 : 0 ≤  Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ) ≤  HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta  ≤  7/8) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin ≤  dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε ≤ 1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw ≤ 1) (hηw : 0 ≤  ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw ≤  ε/2),
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
      ∀d : ℝ,dmin ≤  d → d ≤  dmax →
      ∀B : NaturalBatch (Slot:=Slot) M H hH (fun j=> excluded (F₀ j).character R₀) anchor bad W (33/50) (33/50) (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i ≤  I →
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      0 ≤  mesh → mesh ≤  Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈B.slots,B.widths s ≤  mesh) →
      0 ≤  height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ ≤  height →
      (∀s∈B.slots,|B.relativeHeight s| ≤  height) → (∀u∈B.rows,|B.commonHeight u| ≤  height) →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u : B.rows,a ≤  HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm ≤  Z^d) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖ ≤ ((Z^d)^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,(∏s∈B.slots,max 1 ‖B.Q u s‖)^2) ≤ 
        C*(1+height)^J*
        (Z^d)^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
          402*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  let base := fun j=> excluded (F₀ j).character R₀
  obtain ⟨Jm,hmarked⟩ := actual_weighted_from_buffered_maxima_fixedmesh
    (Slot:=Slot) coarse anchor u₀ F₀ R₀ hu₀ bad hbadM hbad0 hbadTop hbad72 Sbad hbad setup W bΦ Δ εm binWidth η
    hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hβhi
  obtain ⟨Ju,hunmarked⟩ := SaturatedActualWeighted.actual_unmarked_from_buffered_maxima_uniform (Slot:=Slot) M H hH base setup
    εm η hεm hη hβ
  refine ⟨Ju+Jm,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Cm,hCm,hmarked⟩ := hmarked dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨Cu,hCu,hunmarked⟩ := hunmarked dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  let J := Ju+Jm
  let C := Cu+Cm
  have hC : 0< C := by dsimp [C]; linarith
  refine ⟨(2:ℝ)^Fintype.card Slot*C,by positivity,?_⟩
  filter_upwards [hmarked,hunmarked] with Z hmarked hunmarked
  refine ⟨hmarked.1,?_⟩
  intro d hd hd' B a mesh height i hiI ha0 ha hmesh hmeshmax' hmeshaux hbin' hwm hh hf hv hchoice
    hχ hnext hcurrent hmod hQ
  let U := Z^d
  have hU : 1< U := Real.one_lt_rpow hmarked.1 (hdmin.trans_le hd)
  let Cnow := C*(1+height)^J
  have hCnow : 0< Cnow := by dsimp [Cnow]; positivity
  have hCu' : Cu*(1+height)^Ju ≤  Cnow := by
    apply mul_le_mul (show Cu ≤  C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+height) (by dsimp [J]; omega)) (by positivity) hC.le
  have hCm' : Cm*(1+height)^Jm ≤  Cnow := by
    apply mul_le_mul (show Cm ≤  C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+height) (by dsimp [J]; omega)) (by positivity) hC.le
  let loss := 402*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η
  have hS : 0 ≤ ∑s∈B.slots,B.widths s := Finset.sum_nonneg (fun s hs=>(B.widthsPositive s hs).le)
  have hcount : (B.rows.card:ℝ) ≤  Cnow*U^(Marked830.VariableSupply.density (2*a-1)+loss) := by
    have he := hunmarked.2 d hd hd' B a height i hiI ha0 (by linarith) hh hf hχ hnext hcurrent hmod
    apply he.trans
    apply mul_le_mul hCu' (Real.rpow_le_rpow_of_exponent_le hU.le _)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hCnow.le
    dsimp [loss]
    nlinarith [mul_nonneg hbin.le hS]
  have hsub (selected : Finset Slot) (hs : selected⊆B.slots) (hne : selected.Nonempty) :
      (∑u∈B.rows,‖∏s∈selected,B.Q u s‖^2) ≤  Cnow*
        U^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈selected,B.widths s)+(2*a-1)*(∑s∈selected,B.widths s)+loss) := by
    let Bs := B.restrictSlots M H hH selected hs
    have hL : 0<∑s∈selected,B.widths s := Finset.sum_pos (fun s h=> B.widthsPositive s (hs h)) hne
    have he := hmarked.2 d hd hd' Bs a mesh height i hiI ha0 ha hmesh hmeshmax' hmeshaux hbin'
      (fun s h=> hwm s (hs h)) hL hh hf (fun s h=> hv s (hs h)) hchoice hχ hnext hcurrent hmod
      (fun u hu s h=> hQ u hu s (hs h))
    apply he.trans
    apply mul_le_mul hCm' (Real.rpow_le_rpow_of_exponent_le hU.le _)
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hCnow.le
    have hsum : (∑s∈selected,B.widths s) ≤ ∑s∈B.slots,B.widths s :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun s hs _=>(B.widthsPositive s hs).le)
    change _ ≤ _
    dsimp only [loss,Bs,NaturalBatch.restrictSlots]
    nlinarith [mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*binWidth by positivity)]
  have he := Sil.Uneven.Bootstrap.max_weighted_row_sum_of_nonempty B.rows B.slots B.Q B.widths U Cnow
    (2*a-1) loss (fun s hs=>(B.widthsPositive s hs).le) hU.le hCnow.le
    (by linarith) (by linarith) (by simpa only [Sil.Uneven.Saturated.rho, Marked830.VariableSupply.density] using hcount) hsub
  have hN : (2:ℝ)^B.slots.card ≤ (2:ℝ)^Fintype.card Slot :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ B.slots)
  apply he.trans
  calc
    _ ≤ (2:ℝ)^Fintype.card Slot*Cnow*U^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+loss) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN hCnow.le)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
    _=_ := by
      dsimp only [Cnow,U,loss]
      congr 1 <;> ring

end OAI.SevenEighths.MixedBootstrapActualWeighted
end

/- Original module: Candidate.Uneven.MixedBootstrapWholeBuffered. -/
section
/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.MixedBootstrapPlain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤  H)

theorem actual_whole_max_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j ≤  M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j) ≤  Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ Δ εm binWidth ηloss : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2  ≤  bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hΔ0 : 0 ≤  Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ) ≤  HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta  ≤  7/8) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin ≤  dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε ≤ 1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw ≤ 1) (hηw : 0 ≤  ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw ≤  ε/2),
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
      ∀d : ℝ,dmin ≤  d → d ≤  dmax →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀s∈slots,0< w s) → (∀s∈slots,(33/50:ℝ) ≤  σ s) → (∀s∈slots,σ s ≤  (33/50:ℝ)) →
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ) ≤  Z^d) →
      (∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤  Z^d) →
      (∀u∈rows,∀j,initialKeep (MixedBootstrapNaturalBases.base M H hH ηcoarse η₀ u₀ hu₀ R₀ j)
        (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val) →
      (∀s∈slots,∀j,
        ((DetectorDictionaryInverseRawInitialGates.deletedBase
          (momentData (MixedBootstrapNaturalBases.base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)<(Z^d)^(w s)) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow (excluded F₀.character R₀) u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i ≤  I →
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      0 ≤  mesh → mesh ≤  markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈slots,w s ≤  mesh) →
      0 ≤  height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ ≤  height →
      (∀s∈slots,|v s| ≤  height) → (∀u∈rows,|t u| ≤  height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u : rows,a ≤  zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈rows,∀j,(naturalRow (MixedBootstrapNaturalBases.base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u.val u.property.1).character.modulus.absNorm ≤  Z^d) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH (excluded F₀.character R₀) η₀ W (Z^d) w σ v t θ u s‖
         ≤ ((Z^d)^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH (excluded F₀.character R₀) η₀ W (Z^d) w σ v t θ u s‖)^2) ≤ 
        C*(1+height)^J*
        (Z^d)^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈slots,w s)+(2*a-1)*(∑s∈slots,w s)+
          402*ε+mesh+εm+2*binWidth*(∑s∈slots,w s)+ηloss) := by
  obtain ⟨J,hcount⟩ :=
    MixedBootstrapActualWeighted.actual_max_weighted_from_buffered_maxima_fixedmesh (Slot:=Slot) M H hH
      (wholeSourceBase M H hH η₀ ηcoarse) (wholeSourceAnchor M H hH η₀)
      u₀ (fun j=> naturalRow (wholeSourceBase M H hH η₀ ηcoarse j) u₀ hu₀)
      (R₀*wholeAnchorMask M H hH η₀) hu₀ bad
      hbadM hbad0 hbadTop hbad72 Sbad hbad setup W bΦ Δ εm binWidth ηloss
      hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hβhi
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩ := hcount dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hcount
  refine ⟨hcount.1,?_⟩
  intro d hd hd' rows slots w σ v t θ hw hlo hhi hrow hnorm hkeep hlarge
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hmeshaux hbin' hwm hh hf hv ht
    hχ hnext hcurrent hmod hQ
  let B := MixedBootstrapNaturalBases.wholeNaturalBatch M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ bad W (33/50) (33/50) (Z^d) hWs rows slots w σ v t θ
    hw hlo hhi hrow hnorm hkeep hlarge
  have he (u : FreeRow) (hu : u∈rows) :=
    MixedBootstrapNaturalBases.whole_family_maximum M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ (χ u) u.val u.property.1 (holes u)
      (hholes u hu) (hcoeff u hu) (hχ u hu)
  let hc : ∀u∈B.rows,∀j,(B.family u j).residue≠1 := fun u hu=>(he u hu).choose
  have hmax (u : FreeRow) (hu : u∈rows) (T : ℝ) :
      zeroMaximum (B.family u) (hc u hu) T=
      zeroMaximum (wholeSourceFamily M H hH η₀ (χ u)) (hχ u hu) T :=
    (he u hu).choose_spec T
  exact hcount.2 d hd hd' B a mesh height i hiI ha0 ha hmesh hmeshmax hmeshaux hbin' hwm hh hf hv ht hc
    (fun u=> by rw [hmax u.val u.property];exact hnext u)
    (fun u=> by rw [hmax u.val u.property];exact hcurrent u) hmod hQ

end
end OAI.SevenEighths.MixedBootstrapPlain
end
