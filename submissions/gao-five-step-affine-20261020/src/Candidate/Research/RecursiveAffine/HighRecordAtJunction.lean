/- Actual native HIGH record constructor at any threshold qh >= 3/5.
It constructs Hb from actual source rows/witnesses; no returned record is assumed. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.GenericHighRecord
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment LocalMoment Cycle63InitialMass
open CenteredMomentSectorLocalization
open IdealMobiusDivisorSum

def depthTwoHighClassBound (e μ : ℝ) : ℝ :=
  (Fintype.card (BufferIndex e) : ℝ)*(((Finset.Icc (⌊-(148+μ/8)/(μ/32)⌋:ℤ) ⌊(148+μ/8)/(μ/32)⌋).card^4 : ℕ) : ℝ)

structure HighRowFacts {left : Bool} {v : O} {unit : FirstSourceLabel → O} (Z B : ℝ)
    (ℓ : NonzeroJointSourceLabel left v unit) (x : Fin 4 → ℝ) (rowShift : ℝ) : Prop where
  row : rawFrequencyNorm (nonzeroJointSourceRow ℓ) ≤ Z^(x 2 + rowShift)
  supp : Supported ℓ.val.1.1.1 ∧ ℓ.val.1.1.2 ≠ 0 ∧ Supported ℓ.val.2.1.1 ∧ ℓ.val.2.1.2 ≠ 0
  same : primeSupport ℓ.val.1.1.1 = primeSupport ℓ.val.1.1.2 ∧ primeSupport ℓ.val.2.1.1 = primeSupport ℓ.val.2.1.2
  cap : ((Ideal.span {jointSourceRow left v unit ℓ.val}*firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^B
  ideal : (ℓ.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧ (ℓ.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧
    (ℓ.val.2.1.2.absNorm : ℝ) ≤ Z^B
  miss : ((firstSourceMissing left ℓ.val.1).absNorm : ℝ) ≤ Z^(x 1)

theorem high_row_pay_arith {δ ρ A length amp ampP Mrow om μ rest loss E : ℝ}
    (hδ0 : 0≤δ) (hρ0 : 0≤ρ) (hρ : ρ≤5/6) (hom : μ/8≤om) (hA : A≤length) (hamp : amp≤ampP)
    (hloss : om+μ/4+rest≤loss+Mrow)
    (hE : E≤(1-ρ)*om+ρ*(μ/8)+μ/8-(Mrow*(1-ρ)-δ*A-amp*(5-6*ρ))) :
    E≤loss-rest+ρ*Mrow+δ*length+ampP*(5-6*ρ)-4*(μ/32) := by
  have h1 : δ*A≤δ*length := mul_le_mul_of_nonneg_left hA hδ0
  have h2 : amp*(5-6*ρ)≤ampP*(5-6*ρ) := mul_le_mul_of_nonneg_right hamp (by linarith)
  have h3 : ρ*(μ/8)≤ρ*om := mul_le_mul_of_nonneg_left hom hρ0
  nlinarith [h1,h2,h3]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

section Generic

variable {Base : Type} {base : Base → Character} {κ : Type} [Fintype κ]

/-- The count-form record of the HIGH rows of a family of labels: the labels whose buffer bin is at least `(1 + qh)/2`
are binned by their buffer bin and the exponent bins of their coordinates. The record pays the reserve of the parent
when the loss covers the frequency loss and the shift of the class exponents, it has at most the buffer bins times the
fourth power of the exponent bins of the box, and its value is the shifted binned count of the keys of the labels. -/
theorem high_record_of_facts {η₀ : Character} {Z B : ℝ} (Tz : ℝ) {left : Bool} {v₁ : O}
    {unit : FirstSourceLabel → O} {left' : Bool} {u' : O} {unit' : FirstSourceLabel → O} {e : ℝ}
    (hZ : 1<Z) (select : κ → BufferIndex e) (x : κ → Fin 4→ℝ)
    (lab : κ → NonzeroJointSourceLabel left v₁ unit) (key : κ → NonzeroJointSourceLabel left' u' unit')
    (hkey : ∀l,(lab l).val=(key l).val)
    (W : ∀l,DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow (lab l)))
    (μ qh Mrow A amp shift extra : ℝ) (hμ : 0<μ) (hqh : (3/5:ℝ)≤qh)
    (hbox : ∀l j,-(148+μ/8)≤x l j ∧ x l j≤148+μ/8)
    (hfacts : ∀l,(1+qh)/2≤bufferValue e (select l) →
      bufferValue e (select l)≤7/8 ∧ bufferValue e (select l)≤(W l).zeroMax M H hH Tz ∧
      HighRowFacts Z B (lab l) (x l) (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) ∧
      highExponentValue (2*bufferValue e (select l)-1) (x l)≤
        (1-unmarkedDensity (2*bufferValue e (select l)-1))*(frequencyLoss Z 32 (μ/64)+μ/8)+
          unmarkedDensity (2*bufferValue e (select l)-1)*(μ/8)+μ/8-
          (Mrow*(1-unmarkedDensity (2*bufferValue e (select l)-1))-(2*bufferValue e (select l)-1)*A-
            amp*(5-6*unmarkedDensity (2*bufferValue e (select l)-1)))) :
    ∃Hb : SecondStepHighCount M H hH base η₀ Z B Tz left v₁ unit,
      (∀length ampP loss : ℝ,A≤length → amp≤ampP →
        (frequencyLoss Z 32 (μ/64)+μ/8)+μ/4+(extra+shift)≤loss+Mrow →
        Hb.Pays qh Mrow length ampP loss) ∧
      (Fintype.card Hb.Class:ℝ)≤depthTwoHighClassBound e μ ∧
      Hb.value=Z^shift*∑q : BufferIndex e,keyBinnedCount
        ((Finset.univ.filter (fun l=>(1+qh)/2≤bufferValue e (select l))).filter (fun l=>select l=q)) key x (μ/32)
        (fun k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue e q-1)*exponentBinUpper (μ/32) k 3+extra)) := by
  let rows := Finset.univ.filter (fun l=>(1+qh)/2≤bufferValue e (select l))
  let expo := fun (i : BufferIndex e) (b : Fin 4→ℤ) => exponentBinUpper (μ/32) b 0+
    (2*bufferValue e i-1)*exponentBinUpper (μ/32) b 3+(extra+shift)
  have hw : 0<μ/32 := by positivity
  have hthr : ∀l ∈ rows,(1+qh)/2≤bufferValue e (select l) := fun l hl => (Finset.mem_filter.mp hl).2
  let Rec := secondStepBinRecord rows select x (μ/32) lab W expo (fun i => bufferValue e i)
    (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
    (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
    (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
    (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)
  refine ⟨Rec,?_,?_,?_⟩
  · intro length ampP loss hlen hamp' hloss
    refine secondStepBinRecord_pays rows select x (μ/32) lab W expo (fun i => bufferValue e i)
      (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)
      qh Mrow length ampP loss (extra+shift) (fun i b => rfl) rfl ?_ ?_
    · intro l hl
      have hth := hthr l hl
      have h78 := (hfacts l hth).1
      refine ⟨by linarith,by linarith,by linarith⟩
    · intro l hl
      have hth := hthr l hl
      have h78 := (hfacts l hth).1
      have hδ0 : 0 ≤ 2*bufferValue e (select l)-1 := by linarith
      have hδhi : 2*bufferValue e (select l)-1 ≤ 3/4 := by linarith
      have hr := Cycle63InitialMass.unmarkedDensity_lipschitz
        (δ₁:=2*bufferValue e (select l)-1) (δ₂:=2*bufferValue e (select l)-1) hδ0 le_rfl hδhi
      have hρ0 : 0≤unmarkedDensity (2*bufferValue e (select l)-1) := hr.2.2.1
      have hρ1 : unmarkedDensity (2*bufferValue e (select l)-1)≤5/6 := by
        have hden : 0 < 3*(5-2*(2*bufferValue e (select l)-1)) := by linarith
        have hf : (1/6:ℝ) ≤ 10*(2*bufferValue e (select l)-1)/(3*(5-2*(2*bufferValue e (select l)-1))) :=
          (le_div_iff₀ hden).mpr (by linarith)
        unfold unmarkedDensity
        linarith
      have hfreq := frequencyLoss_nonneg Z 32 (μ/64) hZ (by norm_num) (by positivity)
      exact high_row_pay_arith hδ0 hρ0 hρ1 (by linarith) hlen hamp' hloss (hfacts l hth).2.2.2
  · have hcard := secondStepBinRecord_card rows select x (μ/32) lab W expo (fun i => bufferValue e i)
      (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)
      (148+μ/8) (fun l _ j => hbox l j)
    unfold depthTwoHighClassBound
    exact_mod_cast hcard
  · refine (secondStepBinRecord_value rows select x (μ/32) lab W expo (fun i => bufferValue e i)
      (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [keyBinnedCount_eq_of_val_eq (pieceLabels rows select q) lab key hkey x (μ/32) (fun b => Z^(expo q b))]
    have e2 : (fun b : Fin 4→ℤ => Z^(expo q b)) = fun b =>
        Z^((exponentBinUpper (μ/32) b 0+(2*bufferValue e q-1)*exponentBinUpper (μ/32) b 3+extra)+shift) := by
      funext b
      congr 1
      simp only [expo]
      ring
    rw [e2,keyBinnedCount_rpow_shift _ _ _ _ Z shift (zero_lt_one.trans hZ)]
    unfold pieceLabels
    congr!

end Generic


#print axioms high_record_of_facts
end
end OAI.SevenEighths.Cycle153HighProvider
