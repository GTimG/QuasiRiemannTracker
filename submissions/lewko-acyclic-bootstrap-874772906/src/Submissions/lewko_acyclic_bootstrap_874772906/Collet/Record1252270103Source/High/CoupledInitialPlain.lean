/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal squarefree ordinary-pair sums on the existing centered source pools. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SourceModifier
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledInitial
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentHeckeExpansion
open CenteredMomentSourceRectangle CenteredMomentRectangle CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentCommonRadialData
open QRH.Record1252270103Restoration OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledInitialPlainDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def pairProjector (I J:Ideal O):ℂ :=
  if ordinarySmallHole I J then (QRH.Record1252270103KernelMass.squarefreeIndicator (I*J):ℂ) else 0

lemma sourceModifier_pack (v:ι→Ideal O)(I J:Ideal O) :
    sourceModifier 1 1 1 (fun _=>1) (pack v I J)=pairProjector I J := by
  simp only [sourceModifier_eq_literal,one_mul,mul_one,pack_left,pack_right,pairProjector]

lemma finite_sum_same_support {α:Type*} (S T:Finset α)(f:α→ℂ)
    (hS:∀a,f a≠0→a∈S)(hT:∀a,f a≠0→a∈T) :
    (∑a∈S,f a)=∑a∈T,f a := by
  have hs : ∑'a,f a=∑a∈S,f a := tsum_eq_sum (fun a ha=>by
    by_contra hn;exact ha (hS a hn))
  have ht : ∑'a,f a=∑a∈T,f a := tsum_eq_sum (fun a ha=>by
    by_contra hn;exact ha (hT a hn))
  exact hs.symm.trans ht

lemma squarefreePlainSum_finite (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)(b X₁ X₂:ℝ)
    (hX₁:0<X₁)(hX₂:0<X₂)(hw₁:W₁ 0=0)(hw₂:W₂ 0=0)
    (hs₁:Function.support W₁⊆Set.Iic b)(hs₂:Function.support W₂⊆Set.Iic b)
    (S₁ S₂:Finset (Ideal O))
    (h₁:∀I,W₁ ((I.absNorm:ℝ)/X₁)≠0→I∈S₁)
    (h₂:∀I,W₂ ((I.absNorm:ℝ)/X₂)≠0→I∈S₂) :
    squarefreePlainSum ψ W₁ W₂ b X₁ X₂=
      ∑I:S₁,∑J:S₂,pairProjector I J*ψ (I*J)*W₁ ((I.val.absNorm:ℝ)/X₁)*W₂ ((J.val.absNorm:ℝ)/X₂) := by
  let f : (Ideal O×Ideal O)→ℂ:=fun n=>pairProjector n.1 n.2*ψ (n.1*n.2)*
    W₁ ((n.1.absNorm:ℝ)/X₁)*W₂ ((n.2.absNorm:ℝ)/X₂)
  have he : squarefreePlainSum ψ W₁ W₂ b X₁ X₂=∑n∈plainPairPool b X₁ X₂,f n := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [f,pairProjector]
    split_ifs <;> simp
  rw [he]
  have cover (W:ℝ→ℂ)(X:ℝ)(hX:0<X)(hw:W 0=0)(hs:Function.support W⊆Set.Iic b)
      (I:Ideal O)(hi:W ((I.absNorm:ℝ)/X)≠0) : I∈idealBall (b*X) := by
    apply (mem_idealBall _ _).mpr
    refine ⟨?_,(div_le_iff₀ hX).mp (hs hi)⟩
    intro hz
    subst I
    simp only [map_zero,Nat.cast_zero,zero_div,hw,ne_eq,not_true_eq_false] at hi
  have hn (n:Ideal O×Ideal O)(h:f n≠0):
      W₁ ((n.1.absNorm:ℝ)/X₁)≠0 ∧ W₂ ((n.2.absNorm:ℝ)/X₂)≠0 :=
    ⟨right_ne_zero_of_mul (left_ne_zero_of_mul h),right_ne_zero_of_mul h⟩
  rw [finite_sum_same_support (plainPairPool b X₁ X₂) (S₁×ˢS₂) f
    (fun n h=>Finset.mem_product.mpr ⟨cover W₁ X₁ hX₁ hw₁ hs₁ n.1 (hn n h).1,
      cover W₂ X₂ hX₂ hw₂ hs₂ n.2 (hn n h).2⟩)
    (fun n h=>Finset.mem_product.mpr ⟨h₁ n.1 (hn n h).1,h₂ n.2 (hn n h).2⟩)]
  rw [Finset.sum_product]
  rw [←Finset.sum_coe_sort S₁ (fun I=>∑J∈S₂,f (I,J))]
  apply Finset.sum_congr rfl
  intro I hI
  exact (Finset.sum_coe_sort S₂ (fun J=>f (I,J))).symm

lemma input_plain_zero (s:Input ι) : s.W₁ 0=0 ∧ s.W₂ 0=0 := by
  constructor
  · by_contra hn
    exact s.plain₁_ne 0 (s.coverage₁ 0 (Or.inl (by simpa using hn))) rfl
  · by_contra hn
    exact s.plain₂_ne 0 (s.coverage₂ 0 (Or.inl (by simpa using hn))) rfl

end
end QRH.Record1252270103Source.High.CoupledInitial
#print axioms QRH.Record1252270103Source.High.CoupledInitial.squarefreePlainSum_finite
#print axioms QRH.Record1252270103Source.High.CoupledInitial.input_plain_zero
