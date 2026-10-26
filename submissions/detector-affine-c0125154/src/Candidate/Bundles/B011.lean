/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B009
import Candidate.Bundles.B010
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowDirect
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflectionError

/- BEGIN ORIGINAL Cycle25.Energy.ReferenceLowWindow; sha256 85ba6c12dbbbae8de07593c8f9e04afff7bf67f23d892fa3184383e2925758a6 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLowWindow.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                

                                    

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLowWindow
open HeckeFamily CenteredMomentEnergyBands Cycle25CenteredMomentEnergyReferenceState
open Cycle25CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=>HeckeFamily.O

lemma reflection_window_length (Z R x:ℝ)(hZ:1<Z)(hR:0≤R)
    (hx:x∈Set.Icc 0 (R*Real.log Z)):
    length Z (Real.exp x)≤R ∧ Real.exp x≤Z^R:=by
  have hlog:0<Real.log Z:=Real.log_pos hZ
  have hexp:Real.exp x≤Z^R:=by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
    apply Real.exp_le_exp.mpr
    simpa [mul_comm] using hx.2
  refine ⟨?_,hexp⟩
  have hmax:max 1 (Real.exp x)≤Z^R:=
    max_le (Real.one_le_rpow hZ.le hR) hexp
  have hl:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.exp x))) hmax
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hl

theorem deleted_reference_window (Z M X₁ X₂ ell z kappa xi:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hk:7/10≤kappa)(hxi:0≤xi)(hxiM:xi≤M/16)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+6*kappa*z≤M) ∨
    (0<along ∧ ∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
      length Z (Real.exp x)+short+z≤5*M/6 ∧
      length Z (Real.exp x)+short+6*kappa*z≤M):=by
  dsimp only
  let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))
  rcases deleted_reference_cases Z M X₁ X₂ ell z kappa xi (max 0 (M-along+xi))
    hZ hM hX₁ hX₂ hell hz hze hk hxi hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h|h
  · exact Or.inl h
  · refine Or.inr ⟨h.1,?_⟩
    intro x hx
    have hh:=reflection_window_length Z (max 0 (M-along+xi)) x hZ (le_max_left _ _) hx
    have hb:=reflected_low_admissible M xi _ (max 0 (M-along+xi)) z kappa hxiM h.2.1 h.2.2
    constructor <;> linarith [hh.1]

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLowWindow

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReferenceLowWindow -/

/- BEGIN ORIGINAL Cycle25.Energy.ReferenceLowDeletedGeometry; sha256 8178113917e128aeec9d20f1c9ed8ddcd1c0880923c155c9d37bb1c814de35ff -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLowDeletedGeometry.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                        
                                       

                                                
                                    

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLowDeletedGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState Cycle25CenteredMomentEnergyReferenceDivisors
open Cycle25CenteredMomentEnergyReferenceLowWindow
local notation "O"=>HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:7/10≤κ)(hxi:0≤xi)(hxiM:xi≤s.width/16)
    (hlarge:5*s.width/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)):=by
  dsimp only
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hd:=balanced_divisor_range s hZ Mcap X₁ X₂ ell κ hwidth
    hX₁ hX₂ hell hκ hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hd
  have hn₁:=divisor_norm s D₁ hD₁
  have hn₂:=divisor_norm s D₂ hD₂
  have hl₁:=Real.logb_nonneg hZ hn₁.1
  have hl₂:=Real.logb_nonneg hZ hn₂.1
  have hMcap:0≤Mcap:=s.width_nonneg.trans hwidth
  have hLc:0≤L:=by linarith
  refine ⟨hd.2.2.2.1,hd.2.2.2.2,by linarith,by linarith [s.width_nonneg],?_,
    hd.2.2.1,?_,?_⟩
  · linarith [hg.2.2.2.2]
  · exact max_le hLc (by linarith [hd.2.1])
  · have hp₁:∀I∈D₁,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₁ hi)
    have hp₂:∀I∈D₂,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₂ hi)
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ)
    have halong:Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ))=along:=by
      rw [←hd.2.2.2.2]
      exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
    rcases Cycle25CenteredMomentEnergyReferenceLowBranchGeometry.deleted_reference_cases
      Z s.width X₁ X₂ ell z κ xi (max 0 (s.width-along+xi)) hZ s.width_nonneg
      hX₁ hX₂ hell hz hze hκ hxi hlarge hcap D₁ D₂ hp₁ hp₂
      (by rw [halong]) with hc|hc
    · apply Or.inl
      simpa only [hd.2.2.2.1,hd.2.2.2.2] using hc
    · apply Or.inr
      have hh:=Cycle25CenteredMomentEnergyReferenceLowBranchGeometry.reflected_low_admissible
        s.width xi _ (max 0 (s.width-along+xi)) z κ hxiM hc.2.1 hc.2.2
      simpa only [hd.2.2.2.1] using hh

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLowDeletedGeometry

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.ReferenceLowDeletedGeometry -/

/- BEGIN ORIGINAL Cycle25.Energy.OriginalHighReflectionGeometry; sha256 f7462015ada95676308671e3a9853a481f8ba2bf3f965f4c901f6dd990db27d2 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionGeometry.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                 

                                                
                                    
                                       

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState Cycle25CenteredMomentEnergyReferenceDivisors
open Cycle25CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=>HeckeFamily.O

lemma original_long_positive (Z M X₁ X₂ ell κ:ℝ)(hZ:1<Z)(hM:0<M)
    (_hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:7/10≤κ)
    (hshort:length Z X₁≤M/4)
    (hlarge:5*M/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤M):
    0<Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤X₂:=by
  have hbudget:=slot_budgets M (length Z X₁+length Z X₂) ell κ hM.le hell hκ hlarge (by linarith)
  have hpos:0<length Z X₂:=by linarith [hbudget.1]
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0<Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma deleted_length_le (Z X N:ℝ)(hZ:1<Z)(hX:0<X)(hN:1≤N):
    length Z (X/N)≤length Z X:=by
  exact Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 _))
    (max_le_max_left 1 (div_le_self hX.le hN))

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hM:0<s.width)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:7/10≤κ)(hxi:0≤xi)(hxiM:xi≤s.width/16)
    (hshort:length Z X₁≤s.width/4)
    (hlarge:5*s.width/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ));
    let along:=Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ));
    Z^short=X₁/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)):=by
  dsimp only
  have hZ0:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hp₁:=div_pos hX₁ (zero_lt_one.trans_le hn₁)
  have hp₂:=div_pos hX₂ (zero_lt_one.trans_le hn₂)
  have he₁:=Real.rpow_logb hZ0 hZ.ne' hp₁
  have he₂:=Real.rpow_logb hZ0 hZ.ne' hp₂
  have hd₁:=deleted_length_le Z X₁ _ hZ hX₁ hn₁
  have hd₂:=deleted_length_le Z X₂ _ hZ hX₂ hn₂
  have hraw₁:Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ))≤
      length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₁];exact le_max_right _ _
  have hraw₂:Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))≤
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₂];exact le_max_right _ _
  have hlen₁:=length_nonneg Z X₁ hZ
  have hlen₂:=length_nonneg Z X₂ hZ
  have hslot:0≤6*κ*ell:=mul_nonneg (by linarith) hell
  have hl:=original_long_positive Z s.width X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hshort hlarge hcap
  have hrange:=divisor_reflection_range s hZ Mcap X₂ hwidth hl.2.2 D₂ hD₂
  dsimp only at hrange
  have hlogdiv:=Real.logb_div (b:=Z) hX₂.ne' (zero_lt_one.trans_le hn₂).ne'
  rw [←hlogdiv] at hrange
  have hL0:0≤L:=by linarith
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,hrange.2.1,
    max_le hL0 (by linarith [hrange.1]),?_⟩
  rw [he₁,he₂]
  by_cases hd:length Z (X₁/((∏P∈D₁,P).absNorm:ℝ))+
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+z≤5*s.width/6
  · refine Or.inl ⟨hd,?_⟩
    have hkz:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*κ)
    linarith
  · obtain ⟨he,hbudget⟩:=slot_budgets s.width (length Z X₁+length Z X₂) ell κ
      hM.le hell hκ hlarge (by linarith)
    have hlow:=reflected_low s.width (length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)))
      (Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))) ell z κ xi
      (max 0 (s.width-Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+xi))
      hM.le (length_nonneg Z _ hZ)
      (hd₁.trans hshort) hell hz hze hκ he hbudget hxi
      (by rw [←length_eq_max_log Z _ hZ hp₂];exact lt_of_not_ge hd) le_rfl
    exact Or.inr (reflected_low_admissible s.width xi _ _ z κ hxiM hlow.2.1 hlow.2.2)

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionGeometry

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.OriginalHighReflectionGeometry -/

/- BEGIN ORIGINAL Cycle25.Energy.OriginalHighReflectionDeleted; sha256 eebdf75ee01ee68b09da88902b08091ceec94aa37c13d1ef62b190dcd3bb5ef2 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionDeleted.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
                                                    
                                                                     
                                                            

                                    

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionDeleted
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyOriginalHighReflectionGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem deleted_original_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi≤s.width/16 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=Real.logb Z (X₁/((∏I∈D₁,I).absNorm:ℝ))
  let along:=Real.logb Z (X₂/((∏I∈D₂,I).absNorm:ℝ))
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=>hw i)
  have hg:=actual_deleted_gates s hZ.1 (by linarith) hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=>hw i)) hsum hsumle hκ hxi.le hxiM hshort hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=>Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionDeleted

end

end OAI

end
/- END ORIGINAL Cycle25.Energy.OriginalHighReflectionDeleted -/
