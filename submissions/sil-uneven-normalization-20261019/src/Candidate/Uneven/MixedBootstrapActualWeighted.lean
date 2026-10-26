import Candidate.Uneven.MixedAuxiliaryPlainRowwise
import Candidate.Cycle63.Marked.Route.ActualWeightedFixedMesh
import Candidate.Uneven.BootstrapAssembly
import Candidate.Cycle63.Marked.Route.ActualWeightedCount
import Candidate.Target836.Marked836.ActualWeightedFixedMesh
import Candidate.Cycle63.Marked.Route.ActualMarkedGates
import Candidate.Cycle63.Marked.AnnularPool
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

/- Original module: Candidate.Uneven.MixedBootstrapAuxiliaryFields. -/
section
/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.MixedBootstrapActualWeighted
open Cycle63ActualWeighted HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open LocalMoment CenteredMomentDetectorPlainFiberSource
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Uniform auxiliary moment for the same literal batch used in PR63.
The bases are fixed natural seeds over their corresponding relative anchors.
No bound on the moving rows is assumed beyond the fields of NaturalBatch. -/
theorem actual_auxiliary_source_fields
    (coarse anchor : Label→Character) (u₀ : O) (F₀ : ∀j,NaturalRow (coarse j) u₀)
    (R₀ : Ideal O) (hu₀ : u₀≠0) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j ≤ M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j) ≤ Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (bΦ εm mesh : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2 ≤ bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) (hmesh0 : 0< mesh) (hmesh : mesh ≤ AuxiliaryAssembly.sourceMesh εm)
    (hβlo : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,1< U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH (fun j=> excluded (F₀ j).character R₀)
        anchor bad W (33/50) (33/50) U,
      (∀s∈B.slots,B.widths s ≤ mesh) →
      ∀height : ℝ,0 ≤ height → (∀s∈B.slots,|B.relativeHeight s| ≤ height) →
      (∀u∈B.rows,|B.commonHeight u| ≤ height) →
      ∀rows : Finset FreeRow,rows⊆B.rows → ∀label : Label,
      ∀selected : Finset Slot,selected⊆B.slots →
      Sil.Uneven.AuxiliarySource.widthLo ≤ (∑s∈selected,B.widths s) →
      (∑s∈selected,B.widths s) ≤ Sil.Uneven.AuxiliarySource.widthHi →
      ∀m : ℝ,AuxiliaryInitial.plainLower ≤ m → m ≤ AuxiliaryInitial.plainUpper →
      2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s∈selected,B.widths s) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀j k : ℕ,j+k ≤ 2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular) (U^m) σ freq*
        polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular) (U^m) σ freq*
          (∏s∈selected,B.Q u s)‖^2) ≤ (C*(1+height)^J)*U^(1+εm) := by
  have hP (j : Label) := AuxiliaryPlainTransport.actual_rowwise_marked_plain_energy_mixed_anchor (α:=Slot)
    M H hH Sbad hbad W hWs hW bΦ εm mesh hbΦ hrad hεm hmesh0 hmesh hβlo hβhi
    (coarse j) (anchor j) u₀ (F₀ j) R₀ hu₀ (bad j) (hbadM j) (hbad0 j) (hbadTop j) (hbad72 j)
  choose Jp Cp hCp hP using hP
  let J := ∑j,Jp j
  let C := 1+∑j,Cp j
  have hCps : 0 ≤ ∑j,Cp j := Finset.sum_nonneg (fun j _=>(hCp j).le)
  have hC : 0< C := by dsimp [C]; linarith
  have hCpj (j : Label) : Cp j ≤ C := by
    have hh := Finset.single_le_sum (fun k _=>(hCp k).le) (Finset.mem_univ j)
    dsimp [C]; linarith
  have hJp (j : Label) : Jp j ≤ J :=
    Finset.single_le_sum (fun k _=> Nat.zero_le (Jp k)) (Finset.mem_univ j)
  have hPall : ∀ᶠU : ℝ in atTop,∀j,_ := eventually_all.mpr hP
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hPall,eventually_gt_atTop (1:ℝ)] with U hPall hU
  refine ⟨hU,?_⟩
  intro B hwm height hh hv hchoice rows hrows label selected hselected hwl hwu m hm hm1 hcap
    j k hjk σ hσ freq hfreq
  have hPC : Cp label*(1+height)^(Jp label) ≤ C*(1+height)^J :=
    mul_le_mul (hCpj label) (pow_le_pow_right₀ (by linarith) (hJp label)) (by positivity) hC.le
  have hinj : Function.Injective (fun u:FreeRow=> u.val) := Subtype.val_injective
  have he := (hPall label).2 rows (fun u:FreeRow=> u.val) hinj (fun u=> B.family u label)
    (fun u hu=> B.elementCoefficients u (hrows hu) label)
    (fun u hu=> B.retained u (hrows hu) label) (fun u hu=> B.embeddingNorm u (hrows hu))
    m hm hm1 selected (fun s=> B.rays label s.val) (fun s=> B.widths s.val)
    (fun s=> B.sigma s.val) (fun s=> B.relativeHeight s.val) height B.commonHeight
    (fun s=>(B.widthsPositive s.val (hselected s.property)).le)
    (fun s=> hwm s.val (hselected s.property))
    (fun s=> B.sigmaLower s.val (hselected s.property))
    (fun s=> B.sigmaUpper s.val (hselected s.property)) hh
    (fun s=> hv s.val (hselected s.property)) (fun u hu=> hchoice u (hrows hu))
    (by simpa only [Finset.sum_coe_sort] using hwl)
    (by simpa only [Finset.sum_coe_sort] using hwu)
    (by simpa only [Finset.sum_coe_sort] using hcap) j k hjk σ hσ freq (abs_le.mpr hfreq)
  have heq : (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular)
      (U^m) σ freq*polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular)
      (U^m) σ freq*(∏s∈selected,B.Q u s)‖^2) ≤ (Cp label*(1+height)^(Jp label))*U^(1+εm) := by
    convert he using 1
    apply Finset.sum_congr rfl
    intro u hu
    congr 3
    rw [←Finset.prod_coe_sort selected (B.Q u)]
    exact Finset.prod_congr rfl (fun s _=> B.plainIdentity u (hrows hu) label s.val (hselected s.property))
  exact heq.trans (mul_le_mul_of_nonneg_right hPC (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end OAI.SevenEighths.MixedBootstrapActualWeighted
end

/- Original module: Candidate.Uneven.MixedBootstrapActualWeighted. -/
section
/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.MixedBootstrapActualWeighted
open OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment BootstrapAssembly Cycle63ActualMarked
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open Marked830Assembly (RawFiberMoments)
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤  H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

export OAI.SevenEighths.Marked836ActualWeighted (actual_marked_source_fields_fixedmesh)

theorem actual_weighted_row_sum_fixedmesh
    (coarse anchor : Label→Character) (u₀ : O) (F₀ : ∀j,NaturalRow (coarse j) u₀)
    (R₀ : Ideal O) (hu₀ : u₀≠0) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j ≤  M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j) ≤  Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ Δ εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2  ≤  bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hΔ0 : 0 ≤  Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ) ≤  HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta  ≤  7/8) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀ᶠ U : ℝ in atTop,1< U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH (fun j=> excluded (F₀ j).character R₀) anchor bad W (33/50) (33/50) U,
      ∀a ε T allowance mesh binWidth height : ℝ,∀i : ℕ,
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 → 0<ε → ε ≤ 1/1000 →
      0 ≤  mesh → mesh ≤  Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → 0< binWidth → binWidth ≤ (2*a-1)/2 →
      (∀s∈B.slots,B.widths s ≤  mesh) → 0<(∑s∈B.slots,B.widths s) →
      0 ≤  height → 2*Real.pi*allowance+(3*i:ℕ)*T ≤  height →
      (∀s∈B.slots,|B.relativeHeight s| ≤  height) → (∀u∈B.rows,|B.commonHeight u| ≤  height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖ ≤ (U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2) ≤ 
        ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
          (dyadicLength U:ℝ)^2*C)*(1+height)^J*
        U^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
          401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)) := by
  let base := fun j=> excluded (F₀ j).character R₀
  let D := FixedUnmarkedDictionary.ofBases base
  have hκβ : 2*HeckeZeroSupremum.beta-1  ≤  3/4+2*Δ := by linarith
  obtain ⟨Ju,Cu,hCu,hU⟩ := Cycle63ActualUnmarked.actual_unmarked_fiber_gates D setup εm hεm hβ
  obtain ⟨Jm,Cm,hCm,hM⟩ := actual_marked_source_fields_fixedmesh (Slot:=Slot) M H hH base anchor bad
    hbadM hbad0 hbadTop hbad72 W (33/50) (33/50) bΦ (3/4+2*Δ) εm hWs hW (by linarith) hrad
    (by linarith) hεm hβ hκβ
  obtain ⟨Ja,Ca,hCa,hA⟩ := actual_auxiliary_source_fields (Slot:=Slot) M H hH
    coarse anchor u₀ F₀ R₀ hu₀ bad hbadM hbad0 hbadTop hbad72 Sbad hbad W bΦ εm
    (AuxiliaryAssembly.sourceMesh εm) hWs hW hbΦ hrad hεm
    (AuxiliaryAssembly.source_mesh_pos hεm) le_rfl hβ hβhi
  let C := Cu+Cm+Ca
  let J := Ju+Jm+Ja
  refine ⟨J+1,192*C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hU,hM,hA] with U hU hM hA
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax' hmeshaux hbin hbin'
    hwm hL hh hf hv hchoice witness hQ
  have hUp : 0< U := zero_lt_one.trans hU.1
  let Cnow := C*(1+height)^J
  have hCnow : 0< Cnow := by dsimp [Cnow,C]; positivity
  have hCu' : Cu*(1+height)^Ju ≤  Cnow := by
    apply mul_le_mul (show Cu ≤  C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hCm' : Cm*(1+height)^Jm ≤  Cnow := by
    apply mul_le_mul (show Cm ≤  C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hCa' : Ca*(1+height)^Ja  ≤  Cnow := by
    apply mul_le_mul (show Ca  ≤  C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1  ≤  1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hcut (bin : BinLabel B.slots ((2*a-1)/2) binWidth) :=
    binCutoff_bounds B.slots B.widths a binWidth ha0 ha hbin hbin'
      (fun s hs=>(B.widthsPositive s hs).le) hL bin
  have hmom (bin : BinLabel B.slots ((2*a-1)/2) binWidth) (label : Label)
      (left right : Fin (dyadicLength U)) : RawFiberMoments
      (adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
        witness bin label left right) B.slots B.family B.Q B.widths U a ε
      (binCutoff B.slots B.widths a binWidth bin) (3/4+2*Δ) εm Cnow height label left right := by
    let F := adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
      witness bin label left right
    have hfields (u : FreeRow) (hu : u∈F) := adaptiveFiber_fields B.rows B.slots B.widths B.Q B.family
      U a ε T allowance binWidth i hbin witness bin label left right u hu
    have hsub : F⊆B.rows := fun u hu=>(hfields u hu).1
    by_cases hne : F.Nonempty
    · let ub : UnmarkedBatch Label U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i := {
        rows := F
        family := B.family
        witness := witness bin
        row_norm := fun u hu=> B.rowNorm u (hsub hu)
        data := D.data
        reverse := fun _=> false
        row_coeff := fun u hu j I=> by
          simpa only [Bool.false_eq_true,ite_false,D,FixedUnmarkedDictionary.data,
            FixedUnmarkedDictionary.ofBases,momentElement] using B.idealCoefficients u (hsub hu) j I }
      have huf : ub.fiberRows label left right=F := by
        apply Finset.filter_eq_self.mpr
        intro u hu
        exact ⟨(hfields u hu).2.1,(hfields u hu).2.2.1,(hfields u hu).2.2.2.1⟩
      have hune : (ub.fiberRows label left right).Nonempty := huf.symm ▸ hne
      have hu := hU.2 a ε (binCutoff B.slots B.widths a binWidth bin) T allowance height i
        (by linarith) hε.le hεsmall (hcut bin).1 (hcut bin).2 hh hf ub rfl label left right hune
      dsimp only [UnmarkedBatch.fiber,UnmarkedFiber.r,UnmarkedFiber.m] at hu
      rw [huf] at hu
      have hgeom := fiber_lengths F hne B.family U a ε (binCutoff B.slots B.widths a binWidth bin)
        T allowance i hU.1 (witness bin) left right (fun u hu=>(hfields u hu).2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.1)
      dsimp only at hgeom
      have hr0 : 0 ≤  Real.logb U ((2:ℝ)^left.val) := by linarith [hgeom.2.2.2.1,(hcut bin).1]
      have hm0 : 0 ≤  Real.logb U ((2:ℝ)^right.val) := hgeom.2.2.2.2
      have hm1 : Real.logb U ((2:ℝ)^right.val) ≤ 1 := by linarith [hgeom.2.2.1]
      refine ⟨?_,?_,?_,?_⟩
      · exact hu.1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCu' (by positivity))
          (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro j k hjk σ hσ freq hfreq
        exact (hu.2 j k hjk σ hσ freq hfreq).trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).1 _ hr0 hcap1 hcap2
          (binCutoff B.slots B.widths a binWidth bin) n hn σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
      · intro selected hselected hcap j k hjk σ hσ freq hfreq
        have he := (hM.2 B (fun s hs=>(hwm s hs).trans hmeshmax') height hh hv hchoice
          F hsub label selected hselected).2 _ hm0 hm1 hcap j k hjk σ hσ freq hfreq
        exact he.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg (zero_lt_one.trans hU.1).le _))
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change RawFiberMoments F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [he]
      constructor
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity
      · intro j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap1 hcap2 n hn σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
      · intro selected hselected hcap j k hjk σ hσ freq hfreq
        simp only [Finset.sum_empty]
        positivity
  have hauxmom (bin : BinLabel B.slots ((2*a-1)/2) binWidth) (label : Label)
      (left right : Fin (dyadicLength U)) : AuxiliaryPlainMoments
      (adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
        witness bin label left right) B.slots B.family B.Q B.widths U εm Cnow height label right := by
    let F := adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
      witness bin label left right
    have hsub : F⊆B.rows := fun u hu=>(adaptiveFiber_fields B.rows B.slots B.widths B.Q B.family
      U a ε T allowance binWidth i hbin witness bin label left right u hu).1
    intro selected hselected hw hm0 hm1 hcap j k hjk σ hσ freq hfreq
    have he := hA.2 B (fun s hs=>(hwm s hs).trans hmeshaux) height hh hv hchoice F hsub
      label selected hselected hw.1 hw.2 (Real.logb U ((2:ℝ)^right.val)) hm0
      (by change _  ≤  (45/100:ℝ); linarith) hcap j k hjk σ hσ freq hfreq
    exact he.trans (mul_le_mul_of_nonneg_right hCa' (Real.rpow_nonneg hUp.le _))
  have he := weighted_row_sum B.rows B.slots B.family B.Q B.widths U a ε T allowance mesh binWidth Δ
    εm Cnow height i hU.1 ha0 ha hε hmesh hbin hΔ0 hΔ hCnow hh hf B.widthsPositive hwm hL witness hQ hmom hauxmom
  convert he using 1
  dsimp only [Cnow]
  rw [pow_succ]
  ring

theorem actual_weighted_row_sum_uniform_fixedmesh
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
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀ᶠ U : ℝ in atTop,1< U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH (fun j=> excluded (F₀ j).character R₀) anchor bad W (33/50) (33/50) U,
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 → 0<ε → ε ≤ 1/1000 →
      0 ≤  mesh → mesh ≤  Cycle63MarkedPlain.markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈B.slots,B.widths s ≤  mesh) → 0<(∑s∈B.slots,B.widths s) →
      0 ≤  height → 2*Real.pi*allowance+(3*i:ℕ)*T ≤  height →
      (∀s∈B.slots,|B.relativeHeight s| ≤  height) → (∀u∈B.rows,|B.commonHeight u| ≤  height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖ ≤ (U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2) ≤ 
        C*(1+height)^J*
        U^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
          401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_fixedmesh (Slot:=Slot) M H hH
    coarse anchor u₀ F₀ R₀ hu₀ bad hbadM hbad0 hbadTop hbad72 Sbad hbad setup W bΦ Δ εm hWs hW hbΦ hrad hΔ0 hΔ hεm hβ hβhi
  obtain ⟨K,hK,hdyadic⟩ := fixed_label_dyadic_cost (Label:=Label) η hη
  let A : ℝ := (HeckeDetectorClassBudget.alphabetBound binWidth : ℝ)^Fintype.card Slot
  let C' := (1+A)*(1+K)*C
  have hA : 0 ≤  A := by dsimp [A]; positivity
  have hC' : 0< C' := by dsimp [C']; positivity
  refine ⟨J,C',hC',?_⟩
  filter_upwards [hfield,hdyadic] with U hfield hdyadic
  refine ⟨hfield.1,?_⟩
  intro B a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax' hmeshaux hbin' hwm hL hh hf hv hchoice
    witness hQ
  have he := hfield.2 B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax' hmeshaux
    hbin hbin' hwm hL hh hf hv hchoice witness hQ
  have hcard : (Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ) ≤  A := by
    have hb := HeckeDetectorClassBudget.bin_card_le B.slots ((2*a-1)/2) binWidth (by linarith) hbin
    have hp : (HeckeDetectorClassBudget.alphabetBound binWidth)^B.slots.card ≤ 
        (HeckeDetectorClassBudget.alphabetBound binWidth)^Fintype.card Slot := by
      apply Nat.pow_le_pow_right
      · unfold HeckeDetectorClassBudget.alphabetBound
        omega
      · exact Finset.card_le_univ B.slots
    dsimp only [A]
    exact_mod_cast hb.trans hp
  let E := Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈B.slots,B.widths s)+(2*a-1)*(∑s∈B.slots,B.widths s)+
    401*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)
  have hUp : 0< U := zero_lt_one.trans hfield.1
  have hcost : ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
      (dyadicLength U:ℝ)^2*C) ≤ (A*K*C)*U^η := by
    have hp := mul_le_mul hcard hdyadic (by positivity) hA
    have hpc := mul_le_mul_of_nonneg_right hp hC.le
    convert hpc using 1 <;> ring
  have hconst : A*K*C ≤  C' := by
    apply mul_le_mul_of_nonneg_right _ hC.le
    exact mul_le_mul (by linarith : A ≤ 1+A) (by linarith : K ≤ 1+K) hK (by positivity)
  apply he.trans
  change _ ≤  C'*(1+height)^J*U^(E+η)
  calc
    _ ≤ ((A*K*C)*U^η)*(1+height)^J*U^E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost (by positivity))
        (Real.rpow_nonneg hUp.le _)
    _ ≤ (C'*U^η)*(1+height)^J*U^E := by
      gcongr
    _=C'*(1+height)^J*U^(E+η) := by rw [Real.rpow_add hUp E η]; ring
end OAI.SevenEighths.MixedBootstrapActualWeighted
end
