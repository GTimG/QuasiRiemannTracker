import Candidate.Cycle63.Moment.HighSourceEnergy
import Candidate.Cycle63.Physical.HighProfiles.Source

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open Cycle63HighProfiles LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Separate normalization of the two literal plain profiles restores a
single squared original profile control, after the actual high-row estimate. -/
theorem actual_profile_high_source_datum (P : HighSourceParameters) (N : ℕ)
    {ap bp : ℝ} (hap : 0 < ap) (S : Finset (ℕ × ℕ)) (hS : (0,0) ∈ S)
    (T : Finset (ℕ × ℕ)) (Cprofile : ℝ) (hCprofile : 0 < Cprofile) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character,
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ a : ℝ, 51/100 ≤ a → a ≤ 1 →
      ∀ i : ℕ, ∀ {Dict : Type*} [Fintype Dict]
        (D : HighSourceDatum M H P η₀ Z Dict),
      HighSourceAdmissible hH P η₀ Z a i n D →
      ∀ (p : Profiles ap bp) (U : Fin 2 → ℝ) (hU : ∀ j, 0 < U j),
      (∀ j, 1 ≤ U j * bp) → ∀ s : Data D.Slot,
      s.W₁ = (p.profile 0 : ℝ → ℂ) → s.W₂ = (p.profile 1 : ℝ → ℂ) →
      D.source = normalizedData hap S p U hU s →
      clippedControl hap S p U hU 0 * clippedControl hap S p U hU 1 ≤
        Cprofile * p.control T → ∀ E : ℝ,
      D.total P ≤ E → D.liveCard P ≤ N →
      ‖Cycle63.Physical.sourcePositiveRow s.toSource D.second
          D.projector D.allocation D.z‖^2 ≤
        C * (p.control T)^2 *
          Z^((2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hactual⟩ := actual_high_source_datum M H hH P
  let K := Cp^2 * (max 1 Cs)^N
  have hK : 0 < K := mul_pos (sq_pos_of_pos hCp)
    (pow_pos (zero_lt_one.trans_le (le_max_left 1 Cs)) _)
  refine ⟨n,Cprofile^2*K,mul_pos (sq_pos_of_pos hCprofile) hK,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i Dict _ D hD p U hU hret s hW₀ hW₁ hsource hcontrol E hE hN
  have ha₂ : 1/2 ≤ a := by linarith
  have hrow := high_source_datum_cap M H P hZ.1.le hCs.le ha₂
    (hZ.2 a ha ha' i D hD) hE hN
  have hnormalized : ‖Cycle63.Physical.sourcePositiveRow
      (normalizedData hap S p U hU s).toSource D.second
      D.projector D.allocation D.z‖^2 ≤
      K * Z^((2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N) := by
    simpa only [HighSourceDatum.row,hsource] using hrow
  exact (sourcePositiveRow_normalized_bound hap S hS p U hU hret s hW₀ hW₁
    D.second D.projector D.allocation D.z T Cprofile _ hCprofile.le hcontrol
    hnormalized).trans_eq (by dsimp only [K]; ring)

theorem actual_profile_joint_high_energy {Base Family : Type*} [Fintype Base] [Fintype Family]
    (base : Base → Character) (B Q loss : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss)
    {ap bp : ℝ} (hap : 0 < ap) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a E : ℝ) (i : ℕ), q ≤ Q → 33/40 ≤ a → a ≤ 7/8 →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ D : NonzeroJointSourceLabel left u₀ unit → HighSourceDatum M H P η₀ Z Family,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Family → Base,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Family → Ideal O,
      (∀ l ∈ labels, HighSourceAdmissible hH P η₀ Z a i n (D l)) →
      (∀ l ∈ labels, (D l).total P ≤ E ∧ (D l).liveCard P ≤ N) →
      (∀ l ∈ labels, ∀ j, ∀ I : Ideal O, idealCoeff ((D l).character j) I =
        idealCoeff (CenteredMomentNaturalRowSource.excluded
          (CenteredMomentNaturalRowSource.naturalRow (base (dictionary l j))
          (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
            (puncture l j)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum (D l).character (D l).hcharacter
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^m) →
      ∀ (S T : Finset (ℕ × ℕ)), (0,0) ∈ S →
      ∀ (p₀ : Profiles ap bp) (p : NonzeroJointSourceLabel left u₀ unit → Profiles ap bp)
        (U : NonzeroJointSourceLabel left u₀ unit → Fin 2 → ℝ)
        (hU : ∀ l j, 0 < U l j),
      (∀ l ∈ labels, ∀ j, 1 ≤ U l j * bp) →
      ∀ s : ∀ l, Data (D l).Slot,
      (∀ l ∈ labels, (s l).W₁ = ((p l).profile 0 : ℝ → ℂ) ∧
        (s l).W₂ = ((p l).profile 1 : ℝ → ℂ)) →
      (∀ l ∈ labels, (D l).source = normalizedData hap S (p l) (U l) (hU l) (s l)) →
      ∀ Cprofile : ℝ, 0 ≤ Cprofile →
      (∀ l ∈ labels, clippedControl hap S (p l) (U l) (hU l) 0 *
        clippedControl hap S (p l) (U l) (hU l) 1 ≤ Cprofile * p₀.control T) →
      (∑ l ∈ labels, ‖Cycle63.Physical.sourcePositiveRow (s l).toSource
        (D l).second (D l).projector (D l).allocation (D l).z‖^2) ≤
        C*Cprofile^2*(p₀.control T)^2*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
          Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
            2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  obtain ⟨J,hjoint⟩ := actual_joint_high_source_energy (Family := Family)
    M H hH base B Q loss N hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,C,hC,hactual⟩ := hjoint P
  refine ⟨n,C,hC,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro left u₀ unit q m a E i hq ha ha' labels D dictionary puncture
    hvalid hsize hmask hzero hnonzero heq hsupport hnorm hmissing
    S T hS p₀ p U hU hret s hW hsource Cprofile hCp hcontrol
  have hsum := hZ.2 left u₀ unit q m a E i hq ha ha' labels D dictionary puncture
    hvalid hsize hmask hzero hnonzero heq hsupport hnorm hmissing
  have hpoint : ∀ l ∈ labels,
      ‖Cycle63.Physical.sourcePositiveRow (s l).toSource (D l).second
          (D l).projector (D l).allocation (D l).z‖^2 ≤
        Cprofile^2*(p₀.control T)^2*‖(D l).row P‖^2 := by
    intro l hl
    have hc := mul_nonneg (clippedControl_nonneg hap S (p l) (U l) (hU l) 0)
      (clippedControl_nonneg hap S (p l) (U l) (hU l) 1)
    rw [sourcePositiveRow_normalized hap S hS (p l) (U l) (hU l)
      (hret l hl) (s l) (hW l hl).1 (hW l hl).2,
      ←hsource l hl, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, mul_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc (hcontrol l hl) 2)
      (sq_nonneg _)).trans_eq (by unfold HighSourceDatum.row; ring)
  calc
    _ ≤ ∑ l ∈ labels, Cprofile^2*(p₀.control T)^2*‖(D l).row P‖^2 :=
      Finset.sum_le_sum hpoint
    _ = (Cprofile^2*(p₀.control T)^2) * ∑ l ∈ labels, ‖(D l).row P‖^2 := by
      rw [Finset.mul_sum]
    _ ≤ (Cprofile^2*(p₀.control T)^2) *
        (C*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
          Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
            2*P.εplain*P.d+2*P.εslot*P.d*N)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

#print axioms actual_profile_joint_high_energy
#print axioms actual_profile_high_source_datum
end
end OAI.SevenEighths.Cycle63Moment
