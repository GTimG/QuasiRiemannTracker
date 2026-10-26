/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The actual natural-batch inverse field and earlier-source ordinary field share
one degree/constant and retain both representations of each slot amplitude. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.RowwisePlain
import Submissions.hailey_collet_1252270103.Record12518109Gain.ActualSourceFields
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace QRH.Record1252270103Source.High
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer Record12518109GainActual
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem ordinary_marked_source_fields_fixedmesh
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (capacity lam cap sourceMesh : ℝ) (hlam : 0≤lam)
    (W : ℝ→ℂ) (bΦ εm : ℝ)
    (hsource : QRH.Record12518109Existence.UnitFaceSource ⟨capacity,lam,0,capacity,0,cap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) U,
      (∀s∈B.slots,B.widths s≤sourceMesh) →
      ∀height : ℝ,0≤height → (∀s∈B.slots,|B.relativeHeight s|≤height) →
      (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀rows : Finset FreeRow,rows⊆B.rows → ∀label : Label,
      ∀selected : Finset Slot,selected⊆B.slots →
      (∀r : ℝ,0≤r → r+2*(∑s∈selected,B.widths s)<1 →
        2*r+8*(∑s∈selected,B.widths s)<3 →
        ∀tstar : ℝ,∀n : ℕ,n≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈rows,‖polynomial (B.family u label) true ((logProfile^[n]) (inverseTest U tstar r))
          (U^r) σ freq*(∏s∈selected,B.Q u s)‖^2)≤(C*(1+height)^J)*U^(1+εm)) ∧
      (∀m : ℝ,0≤ m → m≤1 → (∑s∈selected,B.widths s)≤cap → 2*m+lam*(∑s∈selected,B.widths s)≤capacity →
        ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular) (U^m) σ freq*
          polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular) (U^m) σ freq*
            (∏s∈selected,B.Q u s)‖^2)≤(C*(1+height)^J)*U^(1+εm)) := by
  obtain ⟨Ji,hI⟩ := actual_free_inverse_energy W (33/50) (33/50) εm hWs hW hεm (Fintype.card Slot)
  choose Ci Ui hCi hUi hI using fun j=>hI (momentData (base j))
  have hP (j : Label) := ordinary_rowwise_plain_fixedmesh (α:=Slot)
    M H hH capacity lam cap sourceMesh εm hlam hsource W bΦ hWs hW hbΦ hrad
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
  · intro m hm hm1 hwidth hcap j k hjk σ hσ freq hfreq
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
      (by simpa only [Finset.sum_coe_sort] using hwidth)
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


end QRH.Record1252270103Source.High
end
#print axioms QRH.Record1252270103Source.High.ordinary_marked_source_fields_fixedmesh
