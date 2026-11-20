/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact common-payment compatibility with LowActual's original normalized slots.
No Euler holes or original coefficients are removed. -/
import Candidate.C092.transport.MediumWitnessBatch
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.PhysicalMomentInput

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology ComplexConjugate
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorSupportedWitness CenteredMomentHeckeSlots CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary CenteredMomentWholeSlotDeletion
open QRH.Cycle092.WholeSlot
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
namespace QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]

/-- The exact original normalized-slot response in the physical orientation. -/
def physicalResponse (D : BaselineData) (F : BaselineSourceData D)
    (Z pay : ℝ) (z : Fin D.N → ℂ) (u : FreeRow) : ℝ :=
  LowActual.originalResponse (fixedSourcePrincipal F.S F.exclusions.prime)
    rowMaskElement 1 0 Z pay D.length
    (fun j => CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (Z^(D.length j)))
    (fun j => physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime)
      F.W (Z^(D.length j)) (z j)) (fun j => Z^(D.length j)) u.val

/-- Conjugation changes no squared response. This is the authentic source-slot
identity, not a replacement of the physical denominator or row mask. -/
theorem physicalResponse_eq (D : BaselineData) (F : BaselineSourceData D)
    (Z pay : ℝ) (hZ : 0 < Z) (z : Fin D.N → ℂ) (u : FreeRow) :
    physicalResponse D F Z pay z u=LowActual.response Z pay D.length
      (fun j => ‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) (z j)‖^2) := by
  unfold physicalResponse LowActual.originalResponse
  congr 1
  funext j
  rw [Cycle25WeightedNumeratorPhysical.source_physical_slot_conj F u _ (z j)
    (Real.rpow_pos_of_pos hZ _),Complex.norm_conj]

lemma response_mono_payment {Slot : Type*} [Fintype Slot]
    (U pay₁ pay₂ : ℝ) (w amplitude : Slot → ℝ)
    (hU : 1 < U) (hp₁ : 0 < pay₁) (hp : pay₁ ≤ pay₂)
    (hw : ∀ j,0 ≤ w j) (ha : ∀ j,0 ≤ amplitude j)
    (hz : ∀ j,w j=0 → amplitude j ≤ pay₁) :
    LowActual.response U pay₂ w amplitude ≤ LowActual.response U pay₁ w amplitude := by
  have hν := LowActual.response_nonneg U pay₁ w amplitude
  have hslot := (LowActual.response_le_iff_amplitudes w amplitude hU hp₁ hw ha hz hν).mp le_rfl
  have hz₂ : ∀ j,w j=0 → amplitude j ≤ pay₂ := fun j hj => (hz j hj).trans hp
  apply (LowActual.response_le_iff_amplitudes w amplitude hU (hp₁.trans_le hp) hw ha hz₂ hν).mpr
  intro j
  exact (hslot j).trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

/-- Enlarging an early payment is compatible with LowActual's literal response,
including its zero-width convention and every original masked coefficient. -/
theorem originalResponse_mono_payment {Slot : Type*} [Fintype Slot]
    (η : Character) (m A : HeckeFamily.O) (t U pay₁ pay₂ : ℝ) (w : Slot → ℝ)
    (pool : Slot → Finset (Ideal HeckeFamily.O)) (coeff : Slot → Ideal HeckeFamily.O → ℂ)
    (P : Slot → ℝ) (z : HeckeFamily.O)
    (hU : 1 < U) (hp₁ : 0 < pay₁) (hp : pay₁ ≤ pay₂) (hw : ∀ j,0 ≤ w j)
    (hz : ∀ j,w j=0 → ‖normalizedSlot η m A z (pool j) (coeff j) t (P j)‖^2 ≤ pay₁) :
    LowActual.originalResponse η m A t U pay₂ w pool coeff P z ≤
      LowActual.originalResponse η m A t U pay₁ w pool coeff P z :=
  response_mono_payment U pay₁ pay₂ w _ hU hp₁ hp hw (fun _ => sq_nonneg _) hz

def commonPayment (D : BaselineData) (Z lowPay : ℝ) : ℝ := max lowPay (responsePayment D Z)

lemma commonPayment_pos (D : BaselineData) {Z lowPay : ℝ} (hZ : 0 < Z) :
    0 < commonPayment D Z lowPay := (responsePayment_pos D hZ).trans_le (le_max_right _ _)

/-- The common normalization costs the low source's old exponent plus at most
one baseline t; its fixed constant remains the actual low-source constant. -/
theorem commonPayment_le (D : BaselineData) (Z C loss : ℝ) (hZ : 1 ≤ Z)
    (hloss : 0 ≤ loss) :
    commonPayment D Z (C*Z^loss) ≤ max 1 C*Z^(loss+D.t) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hbase : 1 ≤ Z^loss := Real.one_le_rpow hZ hloss
  have ht : 1 ≤ Z^D.t := Real.one_le_rpow hZ D.t_pos.le
  apply max_le
  · calc
      _ ≤ max 1 C*Z^loss := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZp.le _)
      _ ≤ max 1 C*(Z^loss*Z^D.t) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (Real.rpow_nonneg hZp.le _) ht) (zero_le_one.trans (le_max_left _ _))
      _ = _ := by rw [←Real.rpow_add hZp]
  · calc
      responsePayment D Z ≤ Z^D.t := responsePayment_le D hZ
      _ ≤ max 1 C*(Z^loss*Z^D.t) := by
        have hh : 1 ≤ max 1 C*Z^loss := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hbase
        nlinarith [Real.rpow_nonneg hZp.le D.t]
      _ = _ := by rw [←Real.rpow_add hZp]

/-- With the genuinely early choice εlow≤D.t/2 and d≤1, the shared payment
has exponent at most 2D.t. -/
theorem commonPayment_early_bound (D : BaselineData) (Z C εlow d : ℝ)
    (hZ : 1 ≤ Z) (hε : 0 ≤ εlow) (hεsmall : εlow ≤ D.t/2) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    commonPayment D Z (C*Z^(2*εlow*d)) ≤ max 1 C*Z^(2*D.t) := by
  have hl : 0 ≤ 2*εlow*d := by positivity
  have hs : 2*εlow*d+D.t ≤ 2*D.t := by nlinarith
  exact (commonPayment_le D Z C (2*εlow*d) hZ hl).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hs) (zero_le_one.trans (le_max_left _ _)))

lemma normalization_within_baseline_budget (D : BaselineData) {budget : ℝ}
    (hb : 159*D.ε+609*D.t ≤ budget) : 2*D.t ≤ budget := by
  have hε := D.epsilon_pos
  have ht := D.t_pos
  linarith

/-- The response uses exactly LowActual's original physical normalized slots,
with a common early payment. -/
def sharedRows (D : BaselineData) (F : BaselineSourceData D)
    (rowCap Z d threshold lowPay : ℝ) (idx grid : FreeRow → ℕ)
    (z : FreeRow → Fin D.N → ℂ) (i k : ℕ) : Finset FreeRow :=
  (rowBand (Z^(1/100 : ℝ)) rowCap).filter fun u =>
    (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
    rowNorm u ≤ Z^(d-D.t) ∧
    threshold ≤ physicalResponse D F Z (commonPayment D Z lowPay) (z u) u ∧ idx u=i ∧ grid u=k

theorem sharedRows_subset_mediumRows (D : BaselineData) (F : BaselineSourceData D)
    (rowCap Z d threshold lowPay : ℝ) (idx grid : FreeRow → ℕ)
    (z : FreeRow → Fin D.N → ℂ) (i k : ℕ) (hZ : 1 < Z) :
    sharedRows D F rowCap Z d threshold lowPay idx grid z i k ⊆
      mediumRows D F rowCap Z d threshold idx grid z i k := by
  intro u hu
  rcases Finset.mem_filter.mp hu with ⟨hrow,hcal,hcond,hresponse,hidx,hgrid⟩
  apply (mem_mediumRows D F rowCap Z d threshold idx grid z i k u).mpr
  refine ⟨hrow,hcal,hcond,?_,hidx,hgrid⟩
  rw [physicalResponse_eq D F Z _ (zero_lt_one.trans hZ) (z u) u] at hresponse
  exact hresponse.trans (response_mono_payment Z (responsePayment D Z) (commonPayment D Z lowPay)
    D.length _ hZ (responsePayment_pos D (zero_lt_one.trans hZ)) (le_max_right _ _)
    (fun j => (D.slots_pos j).le) (fun _ => sq_nonneg _)
    (fun j hj => False.elim ((D.slots_pos j).ne' hj)))

/-- Shared LowActual-normalized medium rows receive the very same original
source-family witnesses; the common payment cannot invalidate the band. -/
theorem original_shared_witnesses (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost) :
    ∃ n : ℕ,0 < n ∧ ∀ η : Character,∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∃ idx grid : FreeRow → ℕ,ProbeAssembly.selected D F padding τ n η Z idx grid ∧
      ∀ (d threshold lowPay : ℝ),(1/200 : ℝ) ≤ d → d ≤ 7/8 → 1/50 < threshold →
      ∀ z : FreeRow → Fin D.N → ℂ,(∀ u j,(z u j).re=17/50) →
      (∀ u j,|(z u j).im| ≤ (3*idx u+1 : ℕ)*Z^τ) →
      ∀ i k : ℕ,
      let rows := sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid z i k
      rows.Nonempty → threshold ≤ squaredBand D k ∧ squaredBand D k ≤ 3/4 ∧
      ∀ r0 m0 : ℝ,1 ≤ r0+m0 → r0+m0 ≤ 3/2 →
      Nonempty (∀ u : rows,SupportedWitness (originalFamily D F η u.val) (Z^d) (bandLower D k)
        D.ε (r0+m0) (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i) := by
  obtain ⟨n,hn,hsupplier⟩ := original_medium_witnesses D F P padding τ hτ hheight
  refine ⟨n,hn,?_⟩
  intro η
  filter_upwards [hsupplier η] with Z hZ
  obtain ⟨idx,grid,hsel,hrest⟩ := hZ.2
  refine ⟨hZ.1,idx,grid,hsel,?_⟩
  intro d threshold lowPay hd hd' hthreshold z hz hzim i k
  dsimp only
  intro hne
  have hsub := sharedRows_subset_mediumRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid z i k hZ.1
  have hne' := hne.mono hsub
  obtain ⟨hband,hw⟩ := hrest d threshold hd hd' hthreshold z hz hzim i k hne'
  refine ⟨hband.response_lower,hband.band_upper,?_⟩
  intro r0 m0 ht ht'
  obtain ⟨w⟩ := hw r0 m0 ht ht'
  exact ⟨fun u => w ⟨u.val,hsub u.property⟩⟩

end QRH.Cycle092.MediumWitness
