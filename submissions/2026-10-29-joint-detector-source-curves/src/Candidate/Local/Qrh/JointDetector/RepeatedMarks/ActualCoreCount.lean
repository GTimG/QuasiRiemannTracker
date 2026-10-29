/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatch
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.InverseFree
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ResponseExtraction
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.DictionaryCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FiniteSelection
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.TrivialResponse
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ParentPlainBatch
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.WordSelection

/-! Actual core moment preparation. Every estimate below is derived from
the coefficient-uniform marked inverse theorem, with the original rooted
slot identities. No assumed moment or count field enters RootedBatch. -/
namespace Qrh.JointDetector.RepeatedMarks.ActualCoreCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentCommonMaskExpansion
open CenteredMomentDetectorEnergyInitialState CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

/-- One fixed dictionary and arbitrary fixed finite copied slot type have
uniform inverse moments before all scales, masks, bins and source subsets. -/
theorem inverse_fields {Label Slot : Type} [Fintype Label] [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (W : ℝ→ℂ) (Aroot εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : Continuous W) (hεm : 0<εm) :
    ∃ J : ℕ,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀ B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
      ∀ rows : Finset FreeRow,rows⊆B.rows → ∀ label : Label,
      ∀ selected : Finset Slot,selected⊆B.slots →
      ∀ (χ : FreeRow→Character) (reverse : Bool),
        (∀ u∈rows,∀ I : Ideal O,idealCoeff (χ u) I=
          if reverse then conj (idealCoeff (B.family u label) I) else idealCoeff (B.family u label) I) →
      ∀ r : ℝ,0≤r → r+2*(∑ s∈selected,B.widths s)<1 →
        2*r+8*(∑ s∈selected,B.widths s)<3 →
      ∀ tstar : ℝ,∀ n : ℕ,n≤2 → ∀ σ∈Icc (0:ℝ) 1,
      ∀ height freq : ℝ,0≤height → freq∈Icc (-height) height →
      (∑ u∈rows,‖polynomial (χ u) true ((logProfile^[n]) (inverseTest U tstar r))
        (U^r) σ freq*(∏ s∈selected,B.Q u s)‖^2)≤(C*(1+height)^J)*U^(1+εm) := by
  obtain ⟨J,henergy⟩ := normalized_inverse_marked_energy_free W (33/50) (33/50) εm
    hWs hW hεm (Fintype.card Slot)
  choose C U₀ hC hU₀ he using fun j : Label => henergy (ProbeHighRowFamily.momentData (base j))
  let Csum := 1+∑ j,C j
  let Ubase := 1+∑ j,U₀ j
  have hsumC : 0≤∑ j,C j := Finset.sum_nonneg (fun j _ => (hC j).le)
  have hCsum : 0<Csum := by dsimp [Csum]; linarith
  have hCj (j : Label) : C j≤Csum := by
    have hh := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ j)
    dsimp [Csum]
    linarith
  have hUj (j : Label) : U₀ j≤Ubase := by
    have hh := Finset.single_le_sum (fun j _ => (zero_lt_one.trans (hU₀ j)).le) (Finset.mem_univ j)
    dsimp [Ubase]
    linarith
  refine ⟨J,Csum,hCsum,?_⟩
  filter_upwards [eventually_ge_atTop Ubase,eventually_gt_atTop (1:ℝ)] with U hUb hU
  refine ⟨hU,?_⟩
  intro B rows hrows label selected hselected χ reverse hχ r hr hfirst hsecond tstar n hn σ hσ height freq hh ht
  have hK : Fintype.card selected≤Fintype.card Slot :=
    Fintype.card_le_of_injective (fun s : selected => s.val) Subtype.val_injective
  have hcoeff (u : FreeRow) (hu : u∈rows) (I : Ideal O) :
      idealCoeff (χ u) I=if reverse then conj (idealCoeff
        ((ProbeHighRowFamily.momentData (base label)).character (ProbeHighRowFamily.momentElement u)) I)
        else idealCoeff ((ProbeHighRowFamily.momentData (base label)).character (ProbeHighRowFamily.momentElement u)) I := by
    rw [hχ u hu I,B.idealCoefficients u (hrows hu) label I]
  have hb := he label U ((hUj label).trans hUb) (ι:=selected) hK
    (fun s : selected => B.inversePools s.val) (fun s => B.widths s.val)
    (fun s => B.widthsNonneg s.val (hselected s.property))
    (fun s => B.inversePrime s.val (hselected s.property))
    (fun s => B.inverseRatios s.val (hselected s.property))
    B.inverseBase B.inverseMask B.inverseAux B.inverseRoot
    (fun s => B.inverseCoefficients s.val) (fun s => B.sigma s.val)
    (fun s => B.relativeHeight s.val) B.commonHeight
    (fun s => B.sigmaLower s.val (hselected s.property))
    (fun s => B.sigmaUpper s.val (hselected s.property)) r hr
    (by simpa only [Finset.sum_coe_sort] using hfirst)
    (by simpa only [Finset.sum_coe_sort] using hsecond)
    rows (fun u hu => B.embeddingNorm u (hrows hu)) χ reverse hcoeff tstar n hn σ hσ height freq hh ht
  have hprod (u : FreeRow) (hu : u∈rows) : (∏ s∈selected,B.Q u s)=
      ∏ s : selected, normalizedSlot B.inverseBase B.inverseMask B.inverseAux
        (u.val*B.inverseRoot^6) (B.inversePools s.val)
        (fun I=>idealCoeff (B.inverseCoefficients s.val) I*
          HeckePrimeAnnular.annularWeight W (U^(B.widths s.val)) (B.sigma s.val) (B.relativeHeight s.val) I)
        B.commonHeight (U^(B.widths s.val)) := by
    calc (∏ s∈selected,B.Q u s) = ∏ s : selected,B.Q u s.val :=
        (Finset.prod_coe_sort selected (fun s => B.Q u s)).symm
      _ = _ := Finset.prod_congr rfl (fun s _ =>
        B.inverseIdentity u (hrows hu) s.val (hselected s.property))
  have hb' : (∑ u∈rows,‖polynomial (χ u) true ((logProfile^[n]) (inverseTest U tstar r))
      (U^r) σ freq*(∏ s∈selected,B.Q u s)‖^2)≤(C label*(1+height)^J)*U^(1+εm) := by
    convert hb using 1
    exact Finset.sum_congr rfl (fun u hu => by rw [hprod u hu])
  exact hb'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hCj label) (pow_nonneg (by linarith) _))
      (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end
end Qrh.JointDetector.RepeatedMarks.ActualCoreCount

namespace Qrh.JointDetector.RepeatedMarks.ActualCoreCount
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification Deletion26
local notation "O" => HeckeFamily.O

/-- One trivial response constant works for every actual rooted batch and
every subcollection. It does not assert a per-slot exceptional slope. -/
theorem trivial_response_bound (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (hW : Continuous W) :
    ∃ C : ℝ,1≤C ∧ ∀ {Label Slot : Type*} (M : Ideal O) [NeZero M]
      (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
      (base anchor : Label→Character) (bad : Label→Ideal O) (U Aroot : ℝ),1<U →
      ∀ B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
      ∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖^2≤C*U^(B.widths s) := by
  obtain ⟨C,hC,hcoeff⟩ := annular_coefficient_bounds W 1 2 (33/50) (33/50)
    (by norm_num) hWs hW
  refine ⟨max 1 ((256*C)^2),le_max_left _ _,?_⟩
  intro Label Slot M inst H hH base anchor bad U Aroot hU B u hu s hs
  have hUp : 0<U := zero_lt_one.trans hU
  rw [B.inverseIdentity u hu s hs]
  apply (normalizedSlot_root_sq_bound B.inverseBase B.inverseMask B.inverseAux B.inverseRoot u.val
    (B.inversePools s) _ B.commonHeight (U^(B.widths s)) C
    (Real.one_le_rpow hU.le (B.widthsNonneg s hs)) hC.le
    (fun I hI=>(B.inversePrime s hs I hI).ne_zero)
    (fun I hI=>(div_le_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (B.inverseRatios s hs I hI).2)
    (fun I hI=>hcoeff (B.inverseCoefficients s) (U^(B.widths s)) (B.sigma s)
      (B.relativeHeight s) B.commonHeight (Real.rpow_pos_of_pos hUp _)
      (B.sigmaLower s hs) (B.sigmaUpper s hs) I (B.inversePrime s hs I hI).ne_zero)).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hUp.le _)

end
end Qrh.JointDetector.RepeatedMarks.ActualCoreCount

namespace Qrh.JointDetector.RepeatedMarks.ActualCoreCount
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRowwisePolynomial
open QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

theorem plain_fields {Label Slot : Type} [Fintype Label] [Nonempty Label]
    [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (B L c mesh εm Aroot : ℝ) (hL : 0≤L) (hεm : 0<εm) (hAr : 0≤Aroot)
    (hsource : UnitFaceSource (globalFace B L c) mesh (εm/2))
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hQM : ∀j,bad j≤M) (hQ0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hQt : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hQ72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2) :
    ∃ J : ℕ,∃ C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀ N : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
      (∀s∈N.slots,N.widths s≤mesh) →
      ∀rows : Finset FreeRow,rows⊆N.rows → ∀label : Label,
      ∀selected : Finset Slot,selected⊆N.slots →
      ∀(χ : FreeRow→Character)(reverse : Bool),
      (∀u∈rows,∀I,idealCoeff (χ u) I=
        if reverse then (starRingEnd ℂ) (idealCoeff (N.family u label) I) else idealCoeff (N.family u label) I) →
      ∀m height : ℝ,0≤m → 0≤height →
      (∀s∈selected,|N.commonHeight+N.relativeHeight s|≤height) →
      (∑s∈selected,N.widths s)≤c → 2*m+L*(∑s∈selected,N.widths s)≤B →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) HeckeDetectorDyadicProfiles.positiveAnnular) (U^m) σd freq*
        polynomial (χ u) false ((logProfile^[k]) HeckeDetectorDyadicProfiles.positiveAnnular) (U^m) σd freq*
        (∏s∈selected,N.Q u s)‖^2)≤C*(1+height)^J*U^(1+εm) := by
  obtain ⟨Cw,hCw,hWb⟩ := ParentPlainBatch.exists_profile_bound W hW hWs
  obtain ⟨bΦ,hbΦ,hrad⟩ := radialMajorant_support_bound
  have hp (j : Label) := ParentPlainBatch.field_for_label (Slot:=Slot) M H hH
    B L c mesh εm Aroot hL hεm hAr hsource base anchor bad j
    (hQM j) (hQ0 j) (hQt j) (hQ72 j) W hW hWs Cw hCw.le hWb bΦ hrad
  choose J C hC hp using hp
  let Jsum := ∑j,J j
  let Csum := 1+∑j,C j
  have hCsum : 0<Csum := by
    have hh : 0≤∑j,C j := Finset.sum_nonneg (fun j _=>(hC j).le)
    dsimp [Csum]; linarith
  have hCj (j : Label) : C j≤Csum := by
    have hh := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ j)
    dsimp [Csum]; linarith
  have hJj (j : Label) : J j≤Jsum := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have hpall : ∀ᶠ U : ℝ in atTop,∀j,_ := eventually_all.mpr hp
  refine ⟨Jsum,Csum,hCsum,?_⟩
  filter_upwards [hpall,eventually_gt_atTop (1:ℝ)] with U hpall hU
  refine ⟨hU,?_⟩
  intro N hwm rows hrows label selected hselected χ reverse hχ m height hm hh hv hcap hbudget j k hjk σd hσd freq hfreq
  have he := (hpall label).2 N hwm rows hrows selected hselected χ reverse hχ m height hm hh hv
    hcap hbudget j k hjk σd hσd freq hfreq
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (hCj label) (pow_le_pow_right₀ (by linarith) (hJj label))
      (pow_nonneg (by linarith) _) hCsum.le) (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end
end Qrh.JointDetector.RepeatedMarks.ActualCoreCount
