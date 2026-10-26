/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed-Q adaptation of CorrectedMarkedCompleted; inherited source notices remain required.
The genuine forcing-ideal count pays the corrected marked source on the original
finite rows, keep predicate, and positive radial weight. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedFixedQMarkedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentHeckeExpansion CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondExceptionalCount CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedDetectorAmplitude
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open Record1252270103Second
local notation "O" => ActualEisensteinCubic.O

theorem corrected_fixedQ_marked_completed_exceptional_energy
    (a b ε Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →Q≠⊤ →Q≤Ideal.span {(72:O)} →∃C₀ : ℝ,0<C₀ ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ι : Type*,∀inst : Fintype ι,∀s : Input ι,
      s.W₁=(W₁:ℝ→ℂ) →s.W₂=(W₂:ℝ→ℂ) →s.b₁≤b →s.b₂≤b →
      ∀Z : ℝ,1<Z →∀η : Character,∀χ : RayFourExpansion.RayCharacter,
      ∀C D : Ideal O,∀hC : Supported C,∀U : Finset (CommonIndex C D),
      idealCoeff η C≠0 →
      ∀R : Ideal O,R≠0 →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀keep : O→Prop,∀Φ : 𝓢(ℝ,ℂ),(∀x,0≤(Φ x).re) →∀H : ℝ,
      (∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→z≠0) →
      (∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→
        FixedInducingRow (childCharacter η χ) Q (fixedBadMask*idealGenerator R) A z) →
      (∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→
        (HeckeRowClosure.rowConductorBound (childCharacter η χ)
        (fixedBadMask*idealGenerator R) 1 (A*z):ℝ)≤Z^Bχ) →
      ∀Cr Mrow : ℝ,0≤Cr →
      (∀z,keep z→(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0→
        (Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^Mrow) →
      ∀A₁ A₂ Df K : Ideal O,A₁≠0 →A₂≠0 →Df∣R →((A₁*A₂).absNorm:ℝ)≤Z^BA →
      ∀P : Finset (Ideal O),0<P.card →(∀p∈P,Prime p) →(∀p∈P,16≤p.absNorm) →
      (∀p∈P,(p.absNorm:ℝ)≤Z^Bpool) →(∀p∈P,∀i I,I∈s.slots i→¬p∣I) →
      2*((idealDividingPool P Df).card+depth+1:ℝ)≤P.card →
      ∀t L : ℝ,0<L →L≤s.X₁ →L≤s.X₂ →L≤s.Y₁ →L≤s.Y₂ →
      (∀n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
        frozenProfile W₁ W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0→
          (idealDividingPool P (n.1*n.2)).card≤depth) →
      (∑'z : O,if keep z then
        (‖modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P))
          R 1 (childCharacter η χ) t (A*z)‖^2/volume s)*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((Mrow-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
          (max 1 L)^(-α)*slotControl s.toData)^2*volume s*
            SchwartzMap.seminorm ℝ 0 0 Φ := by
  obtain ⟨J,S,hS,hfinite⟩ := corrected_fixedQ_marked_exceptional_energy
    a b ε Bχ BA Bpool α depth ha hb hε hBχ hBA hBpool hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,hC₀,hfinite⟩ := hfinite Q hQ0 hQ hQ72
  refine ⟨C₀,hC₀,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι inst s hsW₁ hsW₂ hb₁ hb₂ Z hZ η χ C D hC U hη R hR
    A keep Φ hΦ H hrows hex hcond Cr Mrow hCr hNrow A₁ A₂ Df K hA₁ hA₂ hDR hnormA
    P hP hp hN hpool havoid hbudget t L hL hX₁ hX₂ hY₁ hY₂ hcount
  apply Real.tsum_le_of_sum_le
  · intro z
    dsimp only
    split_ifs
    · exact mul_nonneg (div_nonneg (sq_nonneg _) (volume_pos s).le) (hΦ _)
    · exact le_rfl
  intro F
  let rows := F.filter (fun z=>keep z ∧ (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0)
  have hs (z : O) (hz : z∈rows) : keep z ∧ (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re≠0 :=
    (Finset.mem_filter.mp hz).2
  have hh := hfinite W₁ W₂ hs₁ hs₂ ι inst s hsW₁ hsW₂ hb₁ hb₂ Z hZ η χ C D hC U hη R hR
    rows (fun z hz=>hrows z (hs z hz).1 (hs z hz).2)
    (fun z hz=>hex z (hs z hz).1 (hs z hz).2)
    (fun z hz=>hcond z (hs z hz).1 (hs z hz).2) Cr Mrow hCr
    (fun z hz=>hNrow z (hs z hz).1 (hs z hz).2)
    A₁ A₂ Df K hA₁ hA₂ hDR hnormA P hP hp hN hpool havoid hbudget
    t L hL hX₁ hX₂ hY₁ hY₂ hcount keep Φ hΦ H
  apply le_trans _ hh
  apply le_of_eq
  dsimp only [rows]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hk : keep z
  · by_cases hw : (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re=0
    · simp only [A,hk,hw,ne_eq,not_true_eq_false,and_false,ite_false,ite_true,mul_zero]
    · simp only [A,hk,hw,ne_eq,not_false_eq_true,and_self,ite_true]
  · simp only [A,hk,false_and,ite_false]

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_fixedQ_marked_completed_exceptional_energy
