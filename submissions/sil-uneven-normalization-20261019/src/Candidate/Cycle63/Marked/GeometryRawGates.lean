import Candidate.Cycle63.Marked.WholeFamilyAnchor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
import Candidate.Cycle63.Physical.InitialMass.GeometryHighShell
import Candidate.Cycle63.Marked.DeletionGeometry
import Candidate.Cycle63.Marked.RetainedSlotCaps
import Candidate.Cycle63.Marked.LabeledRawMax
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition

/- Original module: Candidate.Cycle63.Marked.WholeFixedBad. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open HeckeFamily CenteredMomentNaturalFixedRaySource CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def markedFixedIdeal (M : Ideal O) : Ideal O:=M⊓Ideal.span {(72:O)}

lemma markedFixedIdeal_ne_zero (M : Ideal O) [NeZero M] : markedFixedIdeal M≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne M)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma span72_ne_top : (Ideal.span {(72:O)})≠⊤ := by
  intro h
  have hu : IsUnit (72:O):=Ideal.span_singleton_eq_top.mp h
  have h2 : (-2:O)∣72:=⟨-36,by norm_num⟩
  exact CanonicalRowCompletion.negative_two_prime.not_isUnit (isUnit_of_dvd_unit h2 hu)

lemma markedFixedIdeal_ne_top (M : Ideal O) : markedFixedIdeal M≠⊤ := by
  intro h
  exact span72_ne_top (top_le_iff.mp (h ▸ (inf_le_right : markedFixedIdeal M≤Ideal.span {(72:O)})))

/-- One fixed nonzero bad ideal works for every detector anchor and every
geometric dictionary member, independently of moving source allocations. -/
theorem marked_fixed_ideal_gates (M : Ideal O) [NeZero M] (η : Character) :
    markedFixedIdeal M≤M ∧ internalQ (markedFixedIdeal M) η≠0 ∧
      internalQ (markedFixedIdeal M) η≠⊤ ∧
      internalQ (markedFixedIdeal M) η≤Ideal.span {(72:O)} :=
  ⟨inf_le_left,internalQ_ne_zero _ (markedFixedIdeal_ne_zero M) η,
    internalQ_ne_top _ (markedFixedIdeal_ne_top M) η,inf_le_left.trans inf_le_right⟩

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.marked_fixed_ideal_gates
end

/- Original module: Candidate.Cycle63.Marked.GeometryMarkedPacket. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentChildRows RayFourExpansion
open CenteredMomentCanonicalFirst Cycle63Moment
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- A geometric second row supplies a fixed-dictionary coefficient identity,
polynomial Euler holes, and both source-support gates required for weighted
joint multiplicity. The fixed dictionary does not depend on either allocation. -/
theorem eventually_geometry_marked_packet
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Bfirst Bmask bΦ : ℝ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι α Label : Type}[Fintype ι][Fintype α][DecidableEq α][Fintype Label],
      ∀(reflected second : Bool)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
        (row : secondLiveRows (fun l=>(datum l).block))
        (hparent : (datum row.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin column)
        (hfirst : first row.val.1=geometryFirstLabel s R seed K Z ξ hK bin column)
        (hR : (datum row.val.1).R≠0)(ψ : RayCharacter),
      ((geometryFirstSource s R seed K Z ξ hK bin column.1).C.absNorm:ℝ)≤Z^Bfirst→
      ∀(st : NaturalState Z Bmask bΦ)(z : O)(hz : st.radial.keep z),
      st.character=(datum row.val.1).τ ψ→
      st.puncture=(datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C)→
      z=(if second then -row.val.2.2.2.val else row.val.2.2.2.val)→
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf:=geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin
        column datum first row hfirst
      let rawKey:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left u₀ unit hf
      let key:=if second then reflectedNonzeroJointLabel rawKey else rawKey
      let index:=(geometryDictionaryRay reflected s R seed K Z ξ hK bin column,ψ)
      let holes:=(datum row.val.1).input.η.modulus*
        ((datum row.val.1).R*(if second then (datum row.val.1).D else (datum row.val.1).C))
      holes≠0 ∧ (holes.absNorm:ℝ)≤Z^(2*Bfirst+Bmask+1) ∧
      (∀I,idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index)
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I) ∧
      (Supported key.val.1.1.1 ∧ key.val.1.1.2≠0 ∧
        Supported key.val.2.1.1 ∧ key.val.2.1.2≠0) ∧
      (primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 ∧
        primeSupport key.val.2.1.1=primeSupport key.val.2.1.2) := by
  filter_upwards [Deletion26.eventually_geometry_holes_cap (excluded F₀.character R₀) Bfirst Bmask]
    with Z he
  refine ⟨he.1,?_⟩
  intro ι α Label _ _ _ _ reflected second s hη R seed K ξ hK bin column datum first row
    hparent hfirst hR ψ hnorm st z hz hchar hpuncture hrow left unit hf rawKey key index holes
  have hholes:=he.2 reflected second s hη R seed K ξ hK bin column (datum row.val.1) st
    hparent hpuncture hnorm
  have hd:=actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed K Z ξ hK
    bin column datum first row hparent hfirst hR ψ
  have hmask (I : Ideal O) :
      idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index) (nonzeroJointSourceRow key).val
        (nonzeroJointSourceRow key).property).character holes) I := by
    have transfer (χ χ' : Character) (u v : O) (hu : u≠0) (hv : v≠0)
        (hc : χ=χ') (hr : u=v) :
        (naturalRow χ u hu).character=(naturalRow χ' v hv).character := by
      subst χ';subst v;rfl
    have hv : (if second then -row.val.2.2.2.val else row.val.2.2.2.val)≠0 :=
      hrow ▸ st.row_ne_zero z hz
    rw [transfer _ _ _ _ _ hv hchar hrow,hpuncture]
    exact hd.2 I
  have hfirstSupport : Supported key.val.1.1.1 ∧ Supported key.val.1.1.2 ∧
      primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 := by
    have heq : key.val.1=geometryFirstLabel s R seed K Z ξ hK bin column := by
      cases second <;> exact hfirst
    rw [heq]
    exact ⟨(geometryFirstSource s R seed K Z ξ hK bin column.1).hC,
      (geometryFirstSource s R seed K Z ξ hK bin column.1).hD,
      (geometryFirstSource s R seed K Z ξ hK bin column.1).sameSupport⟩
  refine ⟨hholes.1,hholes.2,hmask,?_,?_⟩
  · refine ⟨hfirstSupport.1,hfirstSupport.2.1.1,?_⟩
    cases second <;> exact ⟨(datum row.val.1).hC,(datum row.val.1).hD.1⟩
  · refine ⟨hfirstSupport.2.2,?_⟩
    cases second <;> exact (datum row.val.1).sameSupport

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventually_geometry_marked_packet
end

/- Original module: Candidate.Cycle63.Marked.GeometryRawGates. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeDetectorZeros LocalMoment Cycle63Moment Cycle63InitialMass
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A common polynomial height for all selected buffered rows. -/
def geometryRawHeight (Z τ : ℝ) (I : ℕ) : ℝ :=
  (2*Real.pi+6*(I+1:ℕ))*Z^τ

lemma geometry_raw_height_nonneg {Z τ : ℝ} (hZ : 0 ≤ Z) (I : ℕ) :
    0 ≤ geometryRawHeight Z τ I := by
  unfold geometryRawHeight
  positivity

lemma geometry_raw_height_zero {Z τ : ℝ} (hZ : 1 ≤ Z) (hτ : 0 ≤ τ)
    (i I : ℕ) (hi : i ≤ I) :
    2*Real.pi*Z^(τ/2)+(3*i:ℕ)*Z^τ ≤ geometryRawHeight Z τ I := by
  have hr := Real.rpow_le_rpow_of_exponent_le hZ (show τ/2 ≤ τ by linarith)
  have hz := Real.rpow_nonneg (zero_le_one.trans hZ) τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Real.pi by positivity)
  unfold geometryRawHeight
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz]

lemma geometry_raw_height_time {Z τ t : ℝ} (hZ : 0 ≤ Z)
    (i I : ℕ) (hi : i ≤ I)
    (ht : |t|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ) : |t| ≤ geometryRawHeight Z τ I := by
  have hz := Real.rpow_nonneg hZ τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  unfold geometryRawHeight
  push_cast at ht ⊢
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz,
    mul_nonneg Real.pi_pos.le hz]

lemma geometry_raw_height_frequency {Z τ t v : ℝ} (hZ : 0 ≤ Z)
    (i I : ℕ) (hi : i ≤ I)
    (ht : |t|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ)
    (hv : |t+v|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ) : |v| ≤ geometryRawHeight Z τ I := by
  have hz := Real.rpow_nonneg hZ τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  have habs : |v| ≤ |t+v|+|t| := by
    calc
      |v| = |t+v+-t| := congrArg abs (by ring)
      _ ≤ |t+v|+|t| := by simpa only [abs_neg] using abs_add_le (t+v) (-t)
  unfold geometryRawHeight
  push_cast at ht hv ⊢
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz,
    mul_nonneg Real.pi_pos.le hz]

/-- The fixed buffered index contributes exactly Jτ to the scale exponent. -/
lemma geometry_raw_height_power {Z τ : ℝ} (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (I J : ℕ) :
    (1+geometryRawHeight Z τ I)^J ≤
      (1+2*Real.pi+6*(I+1:ℕ))^J*Z^(τ*(J:ℝ)) := by
  have hz := Real.one_le_rpow hZ hτ
  have hp : 0 < Z := zero_lt_one.trans_le hZ
  have h : 1+geometryRawHeight Z τ I ≤ (1+2*Real.pi+6*(I+1:ℕ))*Z^τ := by
    unfold geometryRawHeight
    nlinarith
  calc
    _ ≤ ((1+2*Real.pi+6*(I+1:ℕ))*Z^τ)^J :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (geometry_raw_height_nonneg (τ:=τ) hp.le I)) h J
    _ = _ := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]

/-- Literal buffered admission supplies both maximum gates used by marked
counting, together with its uniform finite index bound. -/
lemma geometry_zero_bin_raw_gates {Z Bmask bΦ e : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p) :
    p.1.val ≤ bufferCount e ∧
      51/100 ≤ bufferValue e p ∧ bufferValue e p ≤ 7/8 ∧
      bufferValue e p ≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T)<bufferValue e p+2*e :=
  ⟨hbin.2.1,hbin.2.2.1,hbin.2.2.2.1,hbin.2.2.2.2.1,hbin.2.2.2.2.2.2.2.1⟩

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.geometry_raw_height_power
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.geometry_zero_bin_raw_gates
end
