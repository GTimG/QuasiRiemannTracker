import Candidate.Cycle63.Marked.Route.ActualWeightedCount
import Candidate.Cycle63.Marked.Route.ActualMarkedGates
import Candidate.Cycle63.Marked.AnnularPool
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment Cycle63MarkedAssembly Cycle63ActualMarked
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_marked_source_fields_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (lo hi bΦ κ εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hκ : (3/4:ℝ)≤κ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκβ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      (∀s∈B.slots,B.widths s≤Cycle63MarkedPlain.markedPlainMesh κ εm) →
      ∀height : ℝ,0≤height → (∀s∈B.slots,|B.relativeHeight s|≤height) →
      (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀rows : Finset FreeRow,rows⊆B.rows → ∀label : Label,
      ∀selected : Finset Slot,selected⊆B.slots →
      (∀r : ℝ,0≤r → r+2*(∑s∈selected,B.widths s)<1 →
        2*r+8*(∑s∈selected,B.widths s)<3 →
        ∀tstar : ℝ,∀n : ℕ,n≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈rows,‖polynomial (B.family u label) true ((logProfile^[n]) (inverseTest U tstar r))
          (U^r) σ freq*(∏s∈selected,B.Q u s)‖^2)≤(C*(1+height)^J)*U^(1+εm)) ∧
      (∀m : ℝ,0≤ m → m≤1 → 2*m+6*κ*(∑s∈selected,B.widths s)≤1 →
        ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular) (U^m) σ freq*
          polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular) (U^m) σ freq*
            (∏s∈selected,B.Q u s)‖^2)≤(C*(1+height)^J)*U^(1+εm)) := by
  obtain ⟨Ji,hI⟩ := actual_free_inverse_energy W lo hi εm hWs hW hεm (Fintype.card Slot)
  choose Ci Ui hCi hUi hI using fun j=>hI (momentData (base j))
  have hP (j : Label) := Cycle63MarkedPlain.actual_rowwise_marked_plain_energy_fixedmesh (α:=Slot)
    M H hH W 1 2 bΦ lo hi κ εm (by norm_num) hWs hW (by norm_num) hbΦ hrad hκ hεm hβ hκβ
    (base j) (anchor j) (bad j) (hbadM j) (hbad0 j) (hbadTop j) (hbad72 j)
  choose Jp Cp hCp hP using hP
  let J := Ji+∑j,Jp j
  let C := 1+(∑j,Ci j)+(∑j,Cp j)
  let U₀ := 1+∑j,Ui j
  have hCis : 0≤∑j,Ci j := Finset.sum_nonneg (fun j _=>(hCi j).le)
  have hCps : 0≤∑j,Cp j := Finset.sum_nonneg (fun j _=>(hCp j).le)
  have hC : 0<C := by dsimp [C]; linarith
  have hUj (j : Label) : Ui j≤U₀ := by
    have hh := Finset.single_le_sum (fun k _=>(zero_lt_one.trans (hUi k)).le) (Finset.mem_univ j)
    dsimp [U₀]; linarith
  have hCij (j : Label) : Ci j≤C := by
    have hh := Finset.single_le_sum (fun k _=>(hCi k).le) (Finset.mem_univ j)
    dsimp [C]; linarith
  have hCpj (j : Label) : Cp j≤C := by
    have hh := Finset.single_le_sum (fun k _=>(hCp k).le) (Finset.mem_univ j)
    dsimp [C]; linarith
  have hJp (j : Label) : Jp j≤J := by
    have hh := Finset.single_le_sum (fun k _=>Nat.zero_le (Jp k)) (Finset.mem_univ j)
    dsimp [J]; omega
  have hPall : ∀ᶠ U : ℝ in atTop,∀j,_ := eventually_all.mpr hP
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hPall,eventually_ge_atTop U₀,eventually_gt_atTop (1:ℝ)] with U hPall hU₀ hU
  refine ⟨hU,?_⟩
  intro B hwm height hh hv hchoice rows hrows label selected hselected
  have hpow (k : ℕ)(hk : k≤J) : (1+height)^k≤(1+height)^J :=
    pow_le_pow_right₀ (by linarith) hk
  have hIC : Ci label*(1+height)^Ji≤C*(1+height)^J :=
    mul_le_mul (hCij label) (hpow Ji (by dsimp [J]; omega)) (by positivity) hC.le
  have hPC : Cp label*(1+height)^(Jp label)≤C*(1+height)^J :=
    mul_le_mul (hCpj label) (hpow _ (hJp label)) (by positivity) hC.le
  constructor
  · intro r hr hcap1 hcap2 tstar n hn σ hσ freq hfreq
    have he := hI label U ((hUj label).trans hU₀)
      (show Fintype.card selected≤Fintype.card Slot by simpa using Finset.card_le_univ selected)
      (fun s:selected=>B.inversePools s.val) (fun s=>B.widths s.val)
      (fun s=>(B.widthsPositive s.val (hselected s.property)).le)
      (fun s=>B.inversePrime s.val (hselected s.property))
      (fun s=>B.inverseRatios s.val (hselected s.property))
      (fun s=>B.inverseLarge s.val (hselected s.property) label)
      B.inverseBase (fun s=>B.inverseCoefficients s.val) (fun s=>B.sigma s.val)
      (fun s=>B.relativeHeight s.val) B.commonHeight
      (fun s=>B.sigmaLower s.val (hselected s.property))
      (fun s=>B.sigmaUpper s.val (hselected s.property)) r hr
      (by simpa only [Finset.sum_coe_sort] using hcap1)
      (by simpa only [Finset.sum_coe_sort] using hcap2)
      rows (fun u hu=>B.embeddingNorm u (hrows hu)) (fun u=>B.family u label)
      (fun u hu=>B.idealCoefficients u (hrows hu) label) tstar n hn σ hσ height freq hh hfreq
      (fun u hu=>hchoice u (hrows hu))
    have heq : (∑u∈rows,‖polynomial (B.family u label) true ((logProfile^[n]) (inverseTest U tstar r))
        (U^r) σ freq*(∏s∈selected,B.Q u s)‖^2)≤(Ci label*(1+height)^Ji)*U^(1+εm) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 3
      rw [←Finset.prod_coe_sort selected (B.Q u)]
      exact Finset.prod_congr rfl (fun s _=>B.inverseIdentity u (hrows hu) s.val (hselected s.property))
    exact heq.trans (mul_le_mul_of_nonneg_right hIC (Real.rpow_nonneg (zero_lt_one.trans hU).le _))
  · intro m hm hm1 hcap j k hjk σ hσ freq hfreq
    have hinj : Function.Injective (fun u:FreeRow=>u.val) := Subtype.val_injective
    have he := (hPall label).2 rows (fun u:FreeRow=>u.val) hinj (fun u=>B.family u label)
      (fun u hu=>B.elementCoefficients u (hrows hu) label)
      (fun u hu=>B.retained u (hrows hu) label) (fun u hu=>B.embeddingNorm u (hrows hu))
      m hm hm1 selected (fun s=>B.rays label s.val) (fun s=>B.widths s.val)
      (fun s=>B.sigma s.val) (fun s=>B.relativeHeight s.val) height B.commonHeight
      (fun s=>(B.widthsPositive s.val (hselected s.property)).le)
      (fun s=>hwm s.val (hselected s.property))
      (fun s=>B.sigmaLower s.val (hselected s.property))
      (fun s=>B.sigmaUpper s.val (hselected s.property)) hh
      (fun s=>hv s.val (hselected s.property)) (fun u hu=>hchoice u (hrows hu))
      (by simpa only [Finset.sum_coe_sort] using hcap) j k hjk σ hσ freq (abs_le.mpr hfreq)
    have heq : (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular)
        (U^m) σ freq*polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular)
        (U^m) σ freq*(∏s∈selected,B.Q u s)‖^2)≤(Cp label*(1+height)^(Jp label))*U^(1+εm) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 3
      rw [←Finset.prod_coe_sort selected (B.Q u)]
      exact Finset.prod_congr rfl (fun s _=>B.plainIdentity u (hrows hu) label s.val (hselected s.property))
    exact heq.trans (mul_le_mul_of_nonneg_right hPC (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

theorem actual_weighted_row_sum_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      ∀a ε T allowance mesh binWidth height : ℝ,∀i : ℕ,
      Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤Cycle63.Optimization.markedBinTop → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤Cycle63MarkedPlain.markedPlainMesh (Cycle63.Optimization.plainCapacityCost) εm → 0<binWidth → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0<(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
          (dyadicLength U:ℝ)^2*C)*(1+height)^J*
        U^(VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          (Cycle63.Optimization.halfGain (2*a-1))*VariableSupply.chosenWidth (∑s∈B.slots,B.widths s)+
          155*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)) := by
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨Ju,Cu,hCu,hU⟩ := Cycle63ActualUnmarked.actual_unmarked_fiber_gates D setup εm hεm hβ
  obtain ⟨Jm,Cm,hCm,hM⟩ := actual_marked_source_fields_fixedmesh (Slot:=Slot) M H hH base anchor bad
    hbadM hbad0 hbadTop hbad72 W lo hi bΦ (Cycle63.Optimization.plainCapacityCost) εm hWs hW hbΦ hrad
    (by norm_num [Cycle63.Optimization.plainCapacityCost]) hεm hβ hκβ
  let C := Cu+Cm
  let J := Ju+Jm
  refine ⟨J+1,192*C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hU,hM] with U hU hM
  refine ⟨hU.1,?_⟩
  intro B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax' hbin hbin'
    hwm hL hh hf hv hchoice witness hQ
  have hUp : 0<U := zero_lt_one.trans hU.1
  let Cnow := C*(1+height)^J
  have hCnow : 0<Cnow := by dsimp [Cnow,C]; positivity
  have hCu' : Cu*(1+height)^Ju≤Cnow := by
    apply mul_le_mul (show Cu≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hCm' : Cm*(1+height)^Jm≤Cnow := by
    apply mul_le_mul (show Cm≤C by dsimp [C]; linarith)
      (pow_le_pow_right₀ (by linarith : 1≤1+height) (by dsimp [J]; omega)) (by positivity)
    dsimp [C]; positivity
  have hcut (bin : BinLabel B.slots ((2*a-1)/2) binWidth) :=
    binCutoff_bounds B.slots B.widths a binWidth ha0 ha hbin hbin'
      (fun s hs=>(B.widthsPositive s hs).le) hL bin
  have hmom (bin : BinLabel B.slots ((2*a-1)/2) binWidth) (label : Label)
      (left right : Fin (dyadicLength U)) : RawFiberMoments
      (adaptiveFiber B.rows B.slots B.widths B.Q B.family U a ε T allowance binWidth i hbin
        witness bin label left right) B.slots B.family B.Q B.widths U a ε
      (binCutoff B.slots B.widths a binWidth bin) (Cycle63.Optimization.plainCapacityCost) εm Cnow height label left right := by
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
        row_norm := fun u hu=>B.rowNorm u (hsub hu)
        data := D.data
        reverse := fun _=>false
        row_coeff := fun u hu j I=>by
          simpa only [Bool.false_eq_true,ite_false,D,FixedUnmarkedDictionary.data,
            FixedUnmarkedDictionary.ofBases,momentElement] using B.idealCoefficients u (hsub hu) j I }
      have huf : ub.fiberRows label left right=F := by
        apply Finset.filter_eq_self.mpr
        intro u hu
        exact ⟨(hfields u hu).2.1,(hfields u hu).2.2.1,(hfields u hu).2.2.2.1⟩
      have hune : (ub.fiberRows label left right).Nonempty := huf.symm ▸ hne
      have hu := hU.2 a ε (binCutoff B.slots B.widths a binWidth bin) T allowance height i
        (by linarith) hε hεsmall (hcut bin).1 (hcut bin).2 hh hf ub rfl label left right hune
      dsimp only [UnmarkedBatch.fiber,UnmarkedFiber.r,UnmarkedFiber.m] at hu
      rw [huf] at hu
      have hgeom := fiber_lengths F hne B.family U a ε (binCutoff B.slots B.widths a binWidth bin)
        T allowance i hU.1 (witness bin) left right (fun u hu=>(hfields u hu).2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.1)
      dsimp only at hgeom
      have hr0 : 0≤Real.logb U ((2:ℝ)^left.val) := by linarith [hgeom.2.2.2.1,(hcut bin).1]
      have hm0 : 0≤Real.logb U ((2:ℝ)^right.val) := hgeom.2.2.2.2
      have hm1 : Real.logb U ((2:ℝ)^right.val)≤1 := by linarith [hgeom.2.2.1]
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
  have he := weighted_row_sum B.rows B.slots B.family B.Q B.widths U a ε T allowance mesh binWidth
    εm Cnow height i hU.1 ha0 ha hε hmesh hbin hCnow hh hf B.widthsPositive hwm hL witness hQ hmom
  convert he using 1
  dsimp only [Cnow]
  rw [pow_succ]
  ring

theorem actual_weighted_row_sum_uniform_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm binWidth η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U,
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      Cycle63.Arithmetic.q0≤2*a-1 → 2*a-1≤Cycle63.Optimization.markedBinTop → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤Cycle63MarkedPlain.markedPlainMesh (Cycle63.Optimization.plainCapacityCost) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0<(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        U^(VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          (Cycle63.Optimization.halfGain (2*a-1))*VariableSupply.chosenWidth (∑s∈B.slots,B.widths s)+
          155*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_weighted_row_sum_fixedmesh (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm hWs hW hbΦ hrad hεm hβ hκβ
  obtain ⟨K,hK,hdyadic⟩ := fixed_label_dyadic_cost (Label:=Label) η hη
  let A : ℝ := (HeckeDetectorClassBudget.alphabetBound binWidth : ℝ)^Fintype.card Slot
  let C' := (1+A)*(1+K)*C
  have hA : 0≤A := by dsimp [A]; positivity
  have hC' : 0<C' := by dsimp [C']; positivity
  refine ⟨J,C',hC',?_⟩
  filter_upwards [hfield,hdyadic] with U hfield hdyadic
  refine ⟨hfield.1,?_⟩
  intro B a ε T allowance mesh height i ha0 ha hε hεsmall hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
    witness hQ
  have he := hfield.2 B a ε T allowance mesh binWidth height i ha0 ha hε hεsmall hmesh hmeshmax'
    hbin hbin' hwm hL hh hf hv hchoice witness hQ
  have hcard : (Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)≤A := by
    have hb := HeckeDetectorClassBudget.bin_card_le B.slots ((2*a-1)/2) binWidth
      (by linarith [Cycle63.Optimization.markedBinTop_bounds.2]) hbin
    have hp : (HeckeDetectorClassBudget.alphabetBound binWidth)^B.slots.card≤
        (HeckeDetectorClassBudget.alphabetBound binWidth)^Fintype.card Slot := by
      apply Nat.pow_le_pow_right
      · unfold HeckeDetectorClassBudget.alphabetBound
        omega
      · exact Finset.card_le_univ B.slots
    dsimp only [A]
    exact_mod_cast hb.trans hp
  let E := VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
    (Cycle63.Optimization.halfGain (2*a-1))*VariableSupply.chosenWidth (∑s∈B.slots,B.widths s)+
    155*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)
  have hUp : 0<U := zero_lt_one.trans hfield.1
  have hcost : ((Fintype.card (BinLabel B.slots ((2*a-1)/2) binWidth):ℝ)*Fintype.card Label*
      (dyadicLength U:ℝ)^2*C)≤(A*K*C)*U^η := by
    have hp := mul_le_mul hcard hdyadic (by positivity) hA
    have hpc := mul_le_mul_of_nonneg_right hp hC.le
    convert hpc using 1 <;> ring
  have hconst : A*K*C≤C' := by
    apply mul_le_mul_of_nonneg_right _ hC.le
    exact mul_le_mul (by linarith : A≤1+A) (by linarith : K≤1+K) hK (by positivity)
  apply he.trans
  change _≤C'*(1+height)^J*U^(E+η)
  calc
    _≤((A*K*C)*U^η)*(1+height)^J*U^E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost (by positivity))
        (Real.rpow_nonneg hUp.le _)
    _≤(C'*U^η)*(1+height)^J*U^E := by
      gcongr
    _=C'*(1+height)^J*U^(E+η) := by rw [Real.rpow_add hUp E η]; ring
end OAI.SevenEighths.Cycle63ActualWeighted
#print axioms OAI.SevenEighths.Cycle63ActualWeighted.actual_marked_source_fields_fixedmesh
#print axioms OAI.SevenEighths.Cycle63ActualWeighted.actual_weighted_row_sum_uniform_fixedmesh
#print axioms OAI.SevenEighths.Cycle63ActualWeighted.actual_weighted_row_sum_fixedmesh
