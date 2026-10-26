/- Actual native returned-count consumer for all fixed-depth source histories.
The positive physical weights, including reciprocal residual and Cauchy factors, are kept intact.
Apache-2.0; native PR67 returned bin/count proof is reused. -/
import Candidate.Research.RecursiveAffine.UniformHistory
import Candidate.Research.RecursiveAffine.PhysicalHistoryCode
import Candidate.Cycle63.Physical.InitialMass.DepthTwoReturnedCount
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass LocalMoment

/-- Count the actual physical carrier records through their literal full-key history
injection, with a single terminal density payment. Source records and reciprocal
weights stay on their original dependent carrier; they are not replaced by
records on all formal histories. The only source-payment premise is pointwise weighted payment of
the actual native classes; no desired joint prefix count or returned sum is assumed. -/
theorem actual_carrier_returned_sum {Base : Type} [Fintype Base]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Bsrc B loss : ℝ) (hBsrc : 0 ≤ Bsrc) (hB : 0 ≤ B) (hloss : 0 < loss)
    (n : ℕ) (hbudget : (n : ℝ)*Bsrc ≤ B) :
    ∃ J : ℕ, ∀ (base : Base → Character) (η₀ : Character), ∃ C : ℝ, 0 < C ∧
      ∀ (boxes : ℕ → Finset (Fin 4 → ℤ)) (units : ∀ k, History k → FirstSourceLabel → O)
        (lefts : ℕ → Bool) (root : O) {P : Type*} (code : P → History n)
        (hcode : Function.Injective code) (unit : Bool → P → FirstSourceLabel → O)
        (Z T : ℝ), 2 ≤ Z → 0 ≤ T →
      ∀ R : ∀ b p, SecondStepHighCount M H hH base η₀ Z B T b
        (historyMultiplier units lefts root n (code p)) (unit b p),
      ∀ (rows : Finset P) (W : P → ℝ) (K E : ℝ),
      (∀ p ∈ rows, HistoryFacts units lefts root Z Bsrc boxes n (code p)) →
      (∀ p ∈ rows, 0 ≤ W p) → 0 ≤ K →
      (∀ b, ∀ p ∈ rows, (Fintype.card (R b p).Class : ℝ) ≤ K) →
      (∀ b, ∀ p ∈ rows, ∀ σ, 4/5 ≤ (R b p).zeroBin σ ∧ (R b p).zeroBin σ ≤ 7/8) →
      (∀ b, ∀ p ∈ rows, ∀ σ,
        W p*Z^((R b p).exponent σ + (R b p).missExp σ +
          unmarkedDensity (2*(R b p).zeroBin σ-1)*(R b p).rowExp σ + historyMissing lefts Z n (code p)) ≤ Z^E) →
      ∑ p ∈ rows, W p*∑ b, (R b p).value ≤
        C*(∏ k ∈ Finset.range n, (((boxes k).card : ℝ)+1))*(1+T)^J*K*Z^(E+loss) := by
  let eps := loss/3
  have heps : 0 < eps := by dsimp [eps]; positivity
  let width := loss/(3*(3+4*B))
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hwid : width*(3+4*B)=loss/3 := by
    dsimp [width]
    field_simp
  obtain ⟨Cp,hCp,hprefix⟩ := finite_history_fibre_count_uniform Bsrc eps hBsrc heps n
  obtain ⟨J,hJ⟩ := depth_two_returned_sum (Base:=Base) M H hH B eps width hB heps hwidth
  refine ⟨J,fun base η₀ => ?_⟩
  obtain ⟨Cr,hCr,hret⟩ := hJ base η₀
  refine ⟨Cr*Cp,mul_pos hCr hCp,?_⟩
  intro boxes units lefts root P code hcode unit Z T hZ hT R rows W K E hvalid hW hK hclass hzero hpay
  have hZ0 : 0 < Z := by linarith
  let Pc : ℝ := ∏ k ∈ Finset.range n, (((boxes k).card : ℝ)+1)
  let Apre := Cp*Pc*Z^eps
  have hPc : 0 ≤ Pc := Finset.prod_nonneg (fun k _ => add_nonneg (Nat.cast_nonneg _) zero_le_one)
  have hApre : 0 ≤ Apre := mul_nonneg (mul_nonneg hCp.le hPc) (Real.rpow_nonneg hZ0.le _)
  have hmiss : ∀ p ∈ rows, 0 ≤ historyMissing lefts Z n (code p) ∧ historyMissing lefts Z n (code p) ≤ B := by
    intro p hp
    have hm := historyMissing_bounds units lefts root Z Bsrc (by linarith) boxes n (code p) (hvalid p hp)
    exact ⟨hm.1,hm.2.trans hbudget⟩
  have hpre : ∀ m : ℝ, ∀ D : Ideal O,
      (((rows.filter (fun p => historyMissing lefts Z n (code p) ≤ m)).filter
        (fun p => Ideal.span {historyMultiplier units lefts root n (code p)} = D)).card : ℝ) ≤ Apre*Z^m := by
    intro m D
    let S := rows.image code
    let F := (rows.filter (fun p => historyMissing lefts Z n (code p) ≤ m)).filter
      (fun p => Ideal.span {historyMultiplier units lefts root n (code p)} = D)
    let G := S.filter (fun x => historyMissing lefts Z n x ≤ m ∧
      Ideal.span {historyMultiplier units lefts root n x} = D)
    have hvalidS : ∀ x ∈ S, HistoryFacts units lefts root Z Bsrc boxes n x := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact hvalid p hp
    have hmaps : ∀ p ∈ F, code p ∈ G := by
      intro p hp
      obtain ⟨hp',hD⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpRows,hm⟩ := Finset.mem_filter.mp hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem code hpRows,hm,hD⟩
    have hcard : F.card ≤ G.card := Finset.card_le_card_of_injOn code hmaps
      (fun p _ p' _ h=>hcode h)
    have hh := hprefix boxes units lefts root Z hZ S hvalidS m D
    calc _ = (F.card : ℝ) := rfl
      _ ≤ (G.card : ℝ) := Nat.cast_le.mpr hcard
      _ ≤ Cp*Pc*Z^(m+eps) := hh
      _ = Apre*Z^m := by
        dsimp [Apre]
        have he : Z^(m+eps)=Z^eps*Z^m := by
          rw [← Real.rpow_add hZ0]
          congr 1
          ring
        rw [he]
        ring
  have hh := hret (fun p=>historyMultiplier units lefts root n (code p)) unit Z T hZ hT R rows W
    (fun p=>historyMissing lefts Z n (code p)) Apre K E hW hmiss hApre hK hpre hclass hzero hpay
  calc ∑ p ∈ rows, W p*∑ b, (R b p).value
      ≤ Cr*(1+T)^J*Apre*K*Z^(E+width*(3+4*B)+eps) := hh
    _ = (Cr*Cp)*Pc*(1+T)^J*K*Z^(E+loss) := by
      have he : Z^eps*Z^(E+width*(3+4*B)+eps)=Z^(E+loss) := by
        rw [← Real.rpow_add hZ0,hwid]
        congr 1
        dsimp [eps]
        ring
      dsimp [Apre]
      calc Cr*(1+T)^J*(Cp*Pc*Z^eps)*K*Z^(E+width*(3+4*B)+eps)
          = (Cr*Cp)*Pc*(1+T)^J*K*(Z^eps*Z^(E+width*(3+4*B)+eps)) := by ring
        _ = _ := by rw [he]

#print axioms actual_carrier_returned_sum
end
end OAI.SevenEighths.Cycle153JointCount
