/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical initial data specialize the actual allocated-family absolute envelope. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularCanonicalAbsoluteData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open CenteredMomentEnergyBands CenteredMomentCommonProfile RayFourExpansion CenteredMomentCommonAllocationSum
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass CenteredMomentLogDyadic
open Record12518109Natural.MarkedPlain Record1252270103Finite
open Cycle61Moment Cycle61InitialMass Record1252270103Second
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open High.GlobalPhysical SecondSectorDatum SelectedRegularSourceData SelectedRegularLowPoint
local notation "O"=>HeckeFamily.O
local instance canonicalAbsoluteDecEq {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance canonicalAbsoluteFinite (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem eventually_canonical_absolute (N:ℕ)(B lam cap ξ amp reserve:ℝ)
    (hB:B≤1)(hlam:1≤lam)(hcap:cap≤1)(hξ:0<ξ)(hξ1:ξ≤1)
    (hamp:0<amp)(hamp1:amp≤1)(hreserve:0≤reserve)(hreserve1:reserve≤1)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2):
    ∃Ca:ℝ,0<Ca ∧ ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{α Label:Type}[Fintype α][Fintype Label](rayM:Ideal O)[NeZero rayM]
      (H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
      (i:Initial (α:=α) rayM H Z)(η η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)
      (bin:ℤ×(Fin 5→ℤ))(reflected:Bool)(Q:Ideal O),
      Fintype.card α≤N→(∀ j : α, (0:ℝ) ≤ i.w j)→
      (globalFace B lam cap).Admissible (length Z i.X₁) (length Z i.X₂) (∑j,i.w j) 1→
      (1:ℝ) ≤ i.Y₂ → i.Y₂ ≤ i.X₁ → i.Y₂ ≤ i.X₂ →
    let a:=i.anchor hH W hW hsW hZ η η₀ R₀ 1 hR₀ (by simp) 1 1 1 1 (fun _=>1)
      ξ reserve bin reflected Q
    ∀(column:Label→a.Column)
      (hLive:∀l,column l∈firstLiveColumns
        (High.CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
        (fun _=>logAnnulus))
      (alloc:∀l,actualAllocations a.s.pools (FirstFamily.columnIdeal a.reflected a.s a.modifier a.R a.seed
        (Z^a.D) Z a.ξ a.hK a.bin (column l)))
      (P:Finset (Ideal O))(ht:ℝ)(χ₀:Label→RayCharacter),
      Function.Injective (fun l=>(a.label (column l),(column l).2.1.val))→
      P.Nonempty→∀(mesh loss BD:ℝ)(depth:ℕ),
      Pool.FixedCellPoolData P Z amp (amp/2) mesh loss BD 4 depth→
    let F:=allocatedRegularFamily a column hLive alloc P amp ht N χ₀
    let H0:=fun l=>(High.CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l).1).H0
    let radius:=fun l=>ExceptionalPrice.literalFirstRadius reflected Z (volume a.s) Z ξ reserve (a.label (column l))
    ∀Wa:𝓢(ℝ,ℂ),
      secondAbsoluteBudget F.datum (fun q=>F.childModifier q.1)
        (regularFamilyWeight F Wa (fun _=>P) H0 radius (amp/2))≤Ca*(i.p.control {(0,0)})^2*Z^(75:ℝ) := by
  obtain ⟨Ca,hCa,habs⟩:=full_family_absolute N
    (initialSlotBound W hW hsW) 2 (1/4) (9/4) (amp/2) 32 2 4 32 0 4 4
    (initialSlotBound_ge_one W hW hsW) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Ca,hCa,?_⟩
  filter_upwards [habs,InitialTruncated.eventually_initial_caps N B lam cap hB hlam hcap,
    ExceptionalPrice.eventually_initial_first_geometry N B lam cap ξ amp reserve hB hlam hcap
      hξ hξ1 hamp.le hamp1 hreserve hreserve1,allocated_frequency N] with Z ha hc hg hf
  refine ⟨ha.1,?_⟩
  intro hZ α Label _ _ rayM _ H hH i η η₀ R₀ hR₀ bin reflected Q hN hw hadm hy₂ hyl hyr a
    column hLive alloc P ht χ₀ hinj hP mesh loss BD depth hcell F H0 radius Wa
  have hz:=zero_lt_one.trans hZ
  have caps:=hc.2 hZ rayM H hH W hW hsW η η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same hN hw hadm hy₂ hyl hyr
  have geom:=hg.2 hZ rayM H hH W hW hsW η η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same hN hw hadm hy₂ hyl hyr
  have hgeom (l:Label):0<H0 l ∧ 0≤radius l+6*amp ∧ radius l+6*amp≤32 ∧
      ((F.childSeed l).absNorm:ℝ)≤Z^(4:ℝ) ∧ Z^(radius l+6*amp)=F.Hmain l:=by
    have gg:=fun j=>by
      have g:=geom a.modifier reflected bin j
      exact And.intro g.1 (And.intro g.2.1 (And.intro g.2.2.1
        (And.intro g.2.2.2.2.2.1 g.2.2.2.2.2.2)))
    let prop:=(fun (K:ℝ)(hK:0<K)=>∀j:FirstColumnIndex
        (High.CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed K Z ξ hK bin),
      0<(High.CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed K Z ξ hK bin j.1).H0 ∧
      let rad:=ExceptionalPrice.literalFirstRadius reflected Z (volume a.s) Z ξ reserve
        (FirstFamily.firstLabel a.s a.modifier a.R a.seed K Z ξ hK bin j)
      0≤rad+6*amp ∧ rad+6*amp≤32 ∧ (j.2.1.val.absNorm:ℝ)≤Z^(4:ℝ) ∧
        Z^(rad+6*amp)=firstMainRadius reflected K (volume a.s) Z ξ (3*amp) reserve
          (FirstFamily.firstLabel a.s a.modifier a.R a.seed K Z ξ hK bin j))
    have base:prop Z hz:=gg
    have transport (K:ℝ)(hK:0<K)(he:K=Z):prop K hK:=by
      subst K
      exact base
    exact transport (Z^a.D) a.hK (by change Z^(1:ℝ)=Z;exact Real.rpow_one Z) (column l)
  have hVlo:1≤volume F.s:=caps.2.2.1
  have hVhi:volume F.s≤Z^(2:ℝ):=caps.2.2.2.1.trans
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num:(1:ℝ)≤2))
  have hlog:|Real.logb Z (volume F.s)|≤2:=by
    rw [abs_of_nonneg (Real.logb_nonneg hZ hVlo)]
    exact (Real.logb_le_iff_le_rpow hZ (volume_pos F.s)).mpr hVhi
  have hfull:=ha.2 a F i.p Wa (fun _=>P) H0 radius hN (fun _=>le_rfl)
    (fun _=>by change (1:ℝ)≤2;norm_num)
    (fun _=>by change (2:ℝ)≤2;exact le_rfl)
    (fun j=>by change 1≤Z^(i.w j);exact Real.one_le_rpow hZ.le (hw j)) (by change (0:ℝ)≤9/4;norm_num)
    (by change (0:ℝ)≤9/4;norm_num) (by change (1:ℝ)≤1;exact le_rfl)
    rfl rfl caps.2.1 hVlo hVhi hlog (by change (1:Ideal O)≠0;exact one_ne_zero) hinj hLive
    (fun l=>(hgeom l).2.2.2.1)
    (fun l=>by simpa only [neg_zero,Real.rpow_zero,←(hgeom l).2.2.2.2] using Real.one_le_rpow hZ.le (hgeom l).2.1)
    (fun l=>by rw [←(hgeom l).2.2.2.2];exact Real.rpow_le_rpow_of_exponent_le hZ.le (hgeom l).2.2.1)
    (hf.2 a column hLive alloc P amp ht χ₀ rfl hξ.le hξ1 hreserve hamp.le)
    (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ caps.2.2.2.2)
    (fun _=>hP) (fun l=>(hgeom l).1) (fun l=>(hgeom l).2.1) (fun l=>(hgeom l).2.2.1)
    (fun l=>(alloc l).val (Sum.inr 0)) (fun l=>(alloc l).val (Sum.inr 1)) (fun _=>1)
    (fun l=>Collision.markedProduct (alloc l).val) (fun _=>amp) (fun _=>mesh) (fun _=>loss) (fun _=>BD) (fun _=>depth)
    (fun _=>hcell) (fun _=>rfl)
  norm_num only [SelectedRegularAbsolute.exponent] at hfull
  exact hfull

end
end QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute.eventually_canonical_absolute
