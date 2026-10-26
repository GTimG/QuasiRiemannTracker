/- Repeated marks: the inverse marked moment for the replicated slot set `slots ×ˢ univ`.
Fork of the inverse half of Collet's `ordinary_marked_source_fields_fixedmesh`
(High/SourceFields.lean, Apache-2.0). The analytic input is the overlap adapter
`actual_free_inverse_energy` (Lemma 8.1), which accepts any finite family of possibly
repeated prime lists; here each selected slot may occur up to `copies` times. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.SourceFields
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace QRH.RepeatedMarks.Source
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

theorem replicated_inverse_source_field (copies : ℕ)
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (W : ℝ→ℂ) (εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W) (hεm : 0<εm) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) U,
      ∀height : ℝ,0≤height → (∀s∈B.slots,|B.relativeHeight s|≤height) →
      (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀rows : Finset FreeRow,rows⊆B.rows → ∀label : Label,
      ∀selected : Finset (Slot × Fin copies),
      selected⊆B.slots ×ˢ (Finset.univ : Finset (Fin copies)) →
      ∀r : ℝ,0≤r → r+2*(∑x∈selected,B.widths x.1)<1 →
        2*r+8*(∑x∈selected,B.widths x.1)<3 →
        ∀tstar : ℝ,∀n : ℕ,n≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈rows,‖polynomial (B.family u label) true ((logProfile^[n]) (inverseTest U tstar r))
          (U^r) σ freq*(∏x∈selected,B.Q u x.1)‖^2)≤(C*(1+height)^J)*U^(1+εm) := by
  obtain ⟨Ji,hI⟩ := actual_free_inverse_energy W (33/50) (33/50) εm hWs hW hεm
    (Fintype.card (Slot × Fin copies))
  choose Ci Ui hCi hUi hI using fun j=>hI (momentData (base j))
  let C := 1+(∑j,Ci j)
  let U₀ := 1+∑j,Ui j
  have hCis : 0≤∑j,Ci j := Finset.sum_nonneg (fun j _=>(hCi j).le)
  have hC : 0<C := by dsimp [C]; linarith
  have hUj (j : Label) : Ui j≤U₀ := by
    have hh := Finset.single_le_sum (fun k _=>(zero_lt_one.trans (hUi k)).le) (Finset.mem_univ j)
    dsimp [U₀]; linarith
  have hCij (j : Label) : Ci j≤C := by
    have hh := Finset.single_le_sum (fun k _=>(hCi k).le) (Finset.mem_univ j)
    dsimp [C]; linarith
  refine ⟨Ji,C,hC,?_⟩
  filter_upwards [eventually_ge_atTop U₀,eventually_gt_atTop (1:ℝ)] with U hU₀ hU
  refine ⟨hU,?_⟩
  intro B height hh hv hchoice rows hrows label selected hselected r hr hcap1 hcap2 tstar n hn σ hσ
    freq hfreq
  have hmem (x : Slot × Fin copies) (hx : x∈selected) : x.1∈B.slots :=
    (Finset.mem_product.mp (hselected hx)).1
  have hIC : Ci label*(1+height)^Ji≤C*(1+height)^Ji :=
    mul_le_mul_of_nonneg_right (hCij label) (by positivity)
  have hcard : Fintype.card selected≤Fintype.card (Slot × Fin copies) := by
    simpa using Finset.card_le_univ selected
  have he := hI label U ((hUj label).trans hU₀) hcard
    (fun x:selected=>B.inversePools x.val.1) (fun x=>B.widths x.val.1)
    (fun x=>(B.widthsPositive x.val.1 (hmem x.val x.property)).le)
    (fun x=>B.inversePrime x.val.1 (hmem x.val x.property))
    (fun x=>B.inverseRatios x.val.1 (hmem x.val x.property))
    (fun x=>B.inverseLarge x.val.1 (hmem x.val x.property) label)
    B.inverseBase (fun x=>B.inverseCoefficients x.val.1) (fun x=>B.sigma x.val.1)
    (fun x=>B.relativeHeight x.val.1) B.commonHeight
    (fun x=>B.sigmaLower x.val.1 (hmem x.val x.property))
    (fun x=>B.sigmaUpper x.val.1 (hmem x.val x.property)) r hr
    (by have hs := Finset.sum_coe_sort selected (fun x => B.widths x.1); linarith)
    (by have hs := Finset.sum_coe_sort selected (fun x => B.widths x.1); linarith)
    rows (fun u hu=>B.embeddingNorm u (hrows hu)) (fun u=>B.family u label)
    (fun u hu=>B.idealCoefficients u (hrows hu) label) tstar n hn σ hσ height freq hh hfreq
    (fun u hu=>hchoice u (hrows hu))
  have heq : (∑u∈rows,‖polynomial (B.family u label) true ((logProfile^[n]) (inverseTest U tstar r))
      (U^r) σ freq*(∏x∈selected,B.Q u x.1)‖^2)≤(Ci label*(1+height)^Ji)*U^(1+εm) := by
    convert he using 1
    apply Finset.sum_congr rfl
    intro u hu
    congr 3
    rw [←Finset.prod_coe_sort selected (fun x=>B.Q u x.1)]
    exact Finset.prod_congr rfl
      (fun x _=>B.inverseIdentity u (hrows hu) x.val.1 (hmem x.val x.property))
  exact heq.trans (mul_le_mul_of_nonneg_right hIC (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end QRH.RepeatedMarks.Source
end
