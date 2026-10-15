import Candidate.Cycle62.Moment.WholeSourceDatum
import Candidate.Cycle62.Physical.HighResidualAllocation

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle62HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

lemma diagonal_retained_cost_le_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Data ι) (L : Ideal O) (z : O) :
    (∑ alloc ∈ s.toSource.active L, retainedAllocationCost s L alloc z) ≤
      ∑ a ∈ s.toSource.active L, ∑ b ∈ s.toSource.active L,
        Real.sqrt (retainedAllocationCost s L a z) *
          Real.sqrt (retainedAllocationCost s L b z) := by
  apply Finset.sum_le_sum
  intro a ha
  calc
    _ = Real.sqrt (retainedAllocationCost s L a z) *
        Real.sqrt (retainedAllocationCost s L a z) :=
      (Real.mul_self_sqrt (retained_allocation_cost_nonneg s L a z)).symm
    _ ≤ _ := Finset.single_le_sum (s := s.toSource.active L)
      (f := fun b => Real.sqrt (retainedAllocationCost s L a z)*
        Real.sqrt (retainedAllocationCost s L b z))
      (fun b _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ha

/-- The buffered high support is fixed at the natural row before the residual
projector or either allocation is chosen. The actual clipping contribution
remains in the pointwise exponent through the dyad contraction. -/
theorem actual_high_retained_shell {α : Type} [Fintype α] [DecidableEq α]
    (P : HighSourceParameters) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character,
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ a : ℝ, 51/100 ≤ a → a ≤ 1 → ∀ i : ℕ,
      ∀ S : Finset α, ∀ s : Data S,
      ∀ st : NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
        (z : O) (hz : st.radial.keep z),
      ∀ (w σ v : S → ℝ) (θ : S → RayQuotient.Characters M H) (ap bp : ℝ),
      ∀ Ds : Finset (Ideal O), (∀ L ∈ Ds, Squarefree L) →
      ∀ T e : ℝ, 1 ≤ T → (∀ L ∈ Ds, T ≤ (L.absNorm : ℝ)) →
      (∀ L ∈ Ds, (L.absNorm : ℝ) < 2*T) →
      (∀ L ∈ Ds, ∀ alloc ∈ s.toSource.active L, ∀ b : Bool,
        HighSourceAdmissible hH P η₀ Z a i n
          (wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
            s b L alloc w σ v θ ap bp)) →
      (∀ L ∈ Ds, ∀ alloc ∈ s.toSource.active L, ∀ b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
          s b L alloc w σ v θ ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
          Cycle62.Physical.sourcePostClip s.toSource b Z L alloc ≤ e) →
      (∑ L ∈ Ds, ∑ alloc ∈ s.toSource.active L,
        retainedAllocationCost s L alloc z) ≤
      C*(wholeControl s)^2*(2*T)^(2*ε)*
        Z^(e+s.toSource.allowance Z+
          Cycle62.Physical.plainClipAllowance Z ![s.b₁,s.b₂]) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hactual⟩ := actual_high_source_datum M H hH P
  obtain ⟨Csh,hCsh,hshell⟩ := uniform_retained_pair_shell (ι := α) ε hε
  let K := Cp^2*(max 1 Cs)^(Fintype.card α)
  have hK : 0 < K := mul_pos (sq_pos_of_pos hCp)
    (pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _)
  refine ⟨n,4*K*Csh,by positivity,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i S s st hQM hQη z hz w σ v θ ap bp Ds hDs T e hT hlo hhi hvalid hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hpoint (L : Ideal O) (hL : L ∈ Ds)
      (alloc : Allocation L (Finset.univ : Finset (S ⊕ Fin 2)))
      (halloc : alloc ∈ s.toSource.active L) (b : Bool) :
      (normalizedPositiveNorm s.toSource b Z L alloc z)^2 ≤ K*Z^e := by
    let D := wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
      s b L alloc w σ v θ ap bp
    have hcard : D.liveCard P ≤ Fintype.card α := by
      change (liveIndices L alloc).card ≤ Fintype.card α
      exact (Finset.card_le_univ _).trans (by simpa using Finset.card_le_univ S)
    have hc := high_source_datum_cap M H P hZ.1.le hCs.le (by linarith : 1/2 ≤ a)
      (hZ.2 a ha ha' i D (hvalid L hL alloc halloc b)) le_rfl hcard
    have hn := normalizedPositiveNorm_sq_bound s.toSource b Z hZp L alloc z K
      ((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α))
      (by convert hc using 1; rfl)
    exact hn.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (hexp L hL alloc halloc b)) hK.le)
  have hpairs (L : Ideal O) (hL : L ∈ Ds)
      (x : Allocation L (Finset.univ : Finset (S ⊕ Fin 2))) (hx : x ∈ s.toSource.active L)
      (y : Allocation L (Finset.univ : Finset (S ⊕ Fin 2))) (hy : y ∈ s.toSource.active L)
      (b c : Bool) :
      normalizedPositiveNorm s.toSource b Z L x z *
        normalizedPositiveNorm s.toSource c Z L y z ≤ K*Z^e := by
    have hhx := hpoint L hL x hx b
    have hhy := hpoint L hL y hy c
    nlinarith [sq_nonneg (normalizedPositiveNorm s.toSource b Z L x z-
      normalizedPositiveNorm s.toSource c Z L y z)]
  have hbound := hshell S S s s Ds hDs (fun _ _ _=>z) (fun _ _ _=>z) T Z
    hT hZ.1 hlo hhi (fun _ _=>K*Z^e) (fun _ _=>by positivity) hpairs
  calc
    _ ≤ ∑ L ∈ Ds, ∑ x ∈ s.toSource.active L, ∑ y ∈ s.toSource.active L,
        Real.sqrt (retainedAllocationCost s L x z)*
          Real.sqrt (retainedAllocationCost s L y z) :=
      Finset.sum_le_sum (fun L _=>diagonal_retained_cost_le_pairs s L z)
    _ ≤ _ := hbound.trans_eq (by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool, Nat.cast_ofNat,
        nsmul_eq_mul]
      rw [show e+s.toSource.allowance Z+Cycle62.Physical.plainClipAllowance Z ![s.b₁,s.b₂] =
        e+(s.toSource.allowance Z+s.toSource.allowance Z+
          Cycle62.Physical.plainClipAllowance Z ![s.b₁,s.b₂]+
          Cycle62.Physical.plainClipAllowance Z ![s.b₁,s.b₂])/2 by ring,
        Real.rpow_add hZp]
      ring)


/-- Residual allocations are contracted at each fixed encoded row; only
then is the joint physical pool counted by the fixed natural dictionary. -/
theorem actual_high_joint_shell_energy {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base → Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hloss : 0 < loss) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T ap bp : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroJointSourceLabel left u₀ unit → Base)
        (holes : NonzeroJointSourceLabel left u₀ unit → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow l).val
          (nonzeroJointSourceRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^m) →
      ∀ (S : NonzeroJointSourceLabel left u₀ unit → Finset α)
        (s : ∀ l, Data (S l)) (w σ v : ∀ l, S l → ℝ)
        (θ : ∀ l, S l → RayQuotient.Characters M H)
        (Ds : NonzeroJointSourceLabel left u₀ unit → Finset (Ideal O)),
      (∀ l ∈ labels, ∀ L ∈ Ds l, Squarefree L) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, T ≤ (L.absNorm : ℝ) ∧ (L.absNorm : ℝ) < 2*T) →
      (∀ l ∈ labels, (wholeControl (s l))^2 ≤ Kcontrol) →
      (∀ l ∈ labels, (s l).toSource.allowance Z+
        Cycle62.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂] ≤ allowance) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        HighSourceAdmissible hH P η₀ Z a i n
          (wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp)) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
          (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
          Cycle62.Physical.sourcePostClip (s l).toSource b Z L alloc ≤ e) →
      (∑ l ∈ labels, ∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤
      C*Kcontrol*(1+3*(i+1 : ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨J,Ccount,hCcount,hcount⟩ := actual_whole_joint_high_row_count M H hH
    base η₀ B Q loss hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,Cshell,hCshell,hactual⟩ := actual_high_retained_shell (α := α) M H hH P ε hε
  refine ⟨n,Ccount*Cshell,mul_pos hCcount hCshell,?_⟩
  filter_upwards [hactual η₀,eventually_ge_atTop (2 : ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro left u₀ unit q m a e allowance Kcontrol T ap bp i hq ha ha' hK hT
    labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm
    hmissing S s w σ v θ Ds hDs hdyad hcontrol hallowance hvalid hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hTshared : 0 ≤ 3*(i+1 : ℕ)*Z^P.τ := by positivity
  have hcard := hcount left u₀ unit Z hZ₂ q m a (3*(i+1 : ℕ)*Z^P.τ)
    P.Bmask P.bΦ hq ha ha' hTshared labels st hQM hQη z hz
    (fun l => naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l)))
    index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
  let W := Cshell*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpoint (l : NonzeroJointSourceLabel left u₀ unit) (hl : l ∈ labels) :
      (∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤ W := by
    have hr := hZ.2 a (by linarith : 51/100 ≤ a) (by linarith : a ≤ 1) i (S l) (s l)
      (st l) (hQM l) (hQη l) (z l) (hz l) (w l) (σ l) (v l) (θ l) ap bp
      (Ds l) (hDs l hl) T e hT (fun L hL => (hdyad l hl L hL).1)
      (fun L hL => (hdyad l hl L hL).2) (hvalid l hl) (hexp l hl)
    apply hr.trans
    dsimp [W]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcontrol l hl) hCshell.le)
        (Real.rpow_nonneg (by positivity) _)
    · exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith [hallowance l hl])
    · positivity
    · positivity
  calc
    _ ≤ ∑ _l ∈ labels, W := Finset.sum_le_sum hpoint
    _ = (labels.card : ℝ)*W := by simp [nsmul_eq_mul]
    _ ≤ (Ccount*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
        Z^(m+q*unmarkedDensity (2*a-1)+loss))*W :=
      mul_le_mul_of_nonneg_right hcard hW
    _ = _ := by
      dsimp [W]
      rw [show m+q*unmarkedDensity (2*a-1)+loss+e+allowance =
        (m+q*unmarkedDensity (2*a-1)+loss)+(e+allowance) by ring,
        Real.rpow_add hZp (m+q*unmarkedDensity (2*a-1)+loss) (e+allowance)]
      ring

#print axioms actual_high_joint_shell_energy

#print axioms actual_high_retained_shell
#print axioms diagonal_retained_cost_le_pairs
end
end OAI.SevenEighths.Cycle62Moment
