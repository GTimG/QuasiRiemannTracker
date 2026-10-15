import Candidate.Cycle63.Physical.InitialMass.SecondRetainedAssembly
import Candidate.Cycle63.Physical.InitialMass.FirstProjectorMultiplicity

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCommonRadialData IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

abbrev SecondBlockCode := (p : Ideal O × Ideal O) ×
  Finset (CommonIndex p.1 p.2) × (Fin 4→ℤ)

def secondBlockCode (s : SecondBlockSource) : SecondBlockCode :=
  ⟨(s.C,s.D),s.inactive,s.dyad⟩

/-- Once the source's remaining auxiliary labels are fixed, the joint
encoding loses only the two finite ray labels and the dyadic block. -/
theorem actual_second_row_key_injective {Label Aux : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel) (aux : Label→Aux)
    (hlabel : Function.Injective (fun l=>(first l,aux l,secondBlockCode (s l)))) :
    Function.Injective (fun r : secondLiveRows s=>
      (secondEncodedRow s first r,aux r.val.1,(s r.val.1).dyad,r.val.2.1,r.val.2.2.1)) := by
  intro r t h
  have hj := congrArg Prod.fst h
  have ha := congrArg (fun x=>x.2.1) h
  have hn := congrArg (fun x=>x.2.2.1) h
  have hχ := congrArg (fun x=>x.2.2.2.1) h
  have hψ := congrArg (fun x=>x.2.2.2.2) h
  dsimp only at hj ha hn hχ hψ
  have hf : first r.val.1=first t.val.1 := congrArg Sigma.fst hj
  have hc : secondBlockCode (s r.val.1)=secondBlockCode (s t.val.1) := by
    have he := congrArg (fun x : JointSourceLabel=>
      (⟨x.2.1,x.2.2.val.1,(s r.val.1).dyad⟩ : SecondBlockCode)) hj
    exact he.trans (by dsimp only [secondBlockCode,secondEncodedRow]; rw [hn])
  have hl : r.val.1=t.val.1 := hlabel (Prod.ext hf (Prod.ext ha hc))
  have hz := congrArg (fun x : JointSourceLabel=>x.2.2.val.2) hj
  apply Subtype.ext
  rcases r with ⟨⟨l,χ,ψ,z⟩,hr⟩
  rcases t with ⟨⟨m,χ',ψ',z'⟩,ht⟩
  dsimp only at hl hχ hψ
  cases hl
  cases hχ
  cases hψ
  have hz' : z=z' := Subtype.ext hz
  cases hz'
  rfl


def actualSecondBlockCode {ι : Type*} [Fintype ι] (s : Input ι)
    (R seed : Ideal O) (K Tsec Z ξ : ℝ) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    SecondBlockCode := ⟨q.1.val.val,q.2.1,fun i=>(q.2.2 i:ℤ)⟩

/-- Actual common labels and block intervals have no further hidden
multiplicity after their ideal pair, partition and four dyads are recorded. -/
theorem actual_second_block_code_injective {ι : Type*} [Fintype ι] (s : Input ι)
    (R seed : Ideal O) (K Tsec Z ξ : ℝ) :
    Function.Injective (actualSecondBlockCode s R seed K Tsec Z ξ) := by
  rintro ⟨p,U,n⟩ ⟨p',U',n'⟩ h
  have hp : p.val.val=p'.val.val := congrArg Sigma.fst h
  have hp' : p=p' := Subtype.ext (Subtype.ext hp)
  cases hp'
  have ht := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hU : U=U' := congrArg Prod.fst ht
  cases hU
  have hn := congrArg Prod.snd ht
  have hn' : n=n' := funext (fun i=>Subtype.ext (congrFun hn i))
  cases hn'
  rfl

/-- Selecting the other first-stage choices at each first-label/projector
pair leaves just the displayed divisor as auxiliary source information. -/
theorem actual_second_joint_block_code_injective {α Label : Type*}
    [Fintype α] [DecidableEq α]
    (slots : Label→Finset α) (s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O) (K Tsec : Label→ℝ) (Z ξ : ℝ)
    (first : Label→FirstSourceLabel)
    (hfirst : Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q : (l : Label)×ActualSecondBlockIndex
        (s l) (R l) (seed l) (K l) (Tsec l) Z ξ=>
      (first q.1,seed q.1,actualSecondBlockCode (s q.1) (R q.1) (seed q.1)
        (K q.1) (Tsec q.1) Z ξ q.2)) := by
  rintro ⟨l,q⟩ ⟨m,v⟩ h
  have hf : first l=first m := congrArg Prod.fst h
  have hs : seed l=seed m := congrArg (fun x=>x.2.1) h
  have hl : l=m := hfirst (Prod.ext hf hs)
  cases hl
  have hq : q=v := actual_second_block_code_injective (s l) (R l) (seed l)
    (K l) (Tsec l) Z ξ (congrArg (fun x=>x.2.2) h)
  cases hq
  rfl



/-- The injective source code applies to the literal heterogeneous block
family, including the character witness used in its window columns. -/
theorem actual_second_joint_source_keys {α Label : Type*}
    [Fintype α] [DecidableEq α]
    (slots : Label→Finset α) (s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0<K l)
    (first : Label→FirstSourceLabel)
    (hfirst : Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q : (l : Label)×ActualSecondBlockIndex
        (s l) (R l) (seed l) (K l) (Tsec l) Z ξ=>
      (first q.1,seed q.1,secondBlockCode
        (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
          (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2).block)) :=
  actual_second_joint_block_code_injective slots s R seed K Tsec Z ξ first hfirst

/-- The fiber of the joint encoding is bounded by its actual auxiliary
projectors, four dyads and two ray characters. The residual projector is
absent: its sum has already been contracted inside the row energy. -/
theorem actual_second_row_fiber_card {Label Aux : Type*} [Fintype Label]
    [DecidableEq Aux] (s : Label→SecondBlockSource)
    (first : Label→FirstSourceLabel) (aux : Label→Aux)
    (hlabel : Function.Injective (fun l=>(first l,aux l,secondBlockCode (s l))))
    (j : JointSourceLabel) (A : Finset Aux) (N : Finset (Fin 4→ℤ))
    (haux : ∀r : secondLiveRows s,secondEncodedRow s first r=j → aux r.val.1∈A)
    (hdyad : ∀r : secondLiveRows s,secondEncodedRow s first r=j → (s r.val.1).dyad∈N) :
    ((Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j)).card)≤
      A.card*N.card*(Fintype.card RayCharacter)^2 := by
  let fiber := Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j)
  let target := A ×ˢ (N ×ˢ ((Finset.univ : Finset RayCharacter) ×ˢ (Finset.univ : Finset RayCharacter)))
  have hk := actual_second_row_key_injective s first aux hlabel
  have hc : fiber.card≤target.card := Finset.card_le_card_of_injOn
    (fun r : secondLiveRows s=>(aux r.val.1,(s r.val.1).dyad,r.val.2.1,r.val.2.2.1))
    (by
      intro r hr
      have hj := (Finset.mem_filter.mp hr).2
      exact Finset.mem_product.mpr ⟨haux r hj,Finset.mem_product.mpr
        ⟨hdyad r hj,Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_univ _⟩⟩⟩)
    (by
      intro r hr t ht he
      apply hk
      exact Prod.ext ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp ht).2.symm) he)
  calc
    _≤target.card := hc
    _=_ := by simp only [target,Finset.card_product,Finset.card_univ];ring


/-- In a fixed joint row the first projector costs a divisor small power,
not the size of the first-stage source pool. The dyads and ray labels are
kept explicit for their separate finite summation. -/
theorem actual_second_projector_fiber_bound (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀Z : ℝ,1≤Z → ∀{Label : Type*}[Fintype Label]
      (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel) (seed : Label→Ideal O),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (j : NonzeroJointSourceLabel left u₀ unit) (N : Finset (Fin 4→ℤ)),
      ((Ideal.span {jointSourceRow left u₀ unit j.val}).absNorm:ℝ)≤Z^B →
      (∀r : secondLiveRows s,secondEncodedRow s first r=j.val → (s r.val.1).dyad∈N) →
      ((Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j.val)).card:ℝ)≤
        (K*Z^ε)*N.card*(Fintype.card RayCharacter:ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := first_projector_small_power B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ s first seed hinj hseed hdiv left u₀ unit j N hnorm hdyad
  let A := (idealDivisors (Ideal.span {jointSourceRow left u₀ unit j.val})).filter Squarefree
  have hI : Ideal.span {jointSourceRow left u₀ unit j.val}≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr j.property
  have hcard := actual_second_row_fiber_card s first seed hinj j.val A N
    (by
      intro r hr
      have hd := actual_second_encoded_first_projector s first r left u₀ unit
        (seed r.val.1) (hseed r.val.1) (hdiv r.val.1).1 (hdiv r.val.1).2
      rw [hr] at hd
      exact Finset.mem_filter.mpr ⟨(mem_idealDivisors hI).mpr hd,hseed r.val.1⟩) hdyad
  have hsmall : (A.card:ℝ)≤K*Z^ε := hbound Z hZ _ j.property hnorm A
    (fun L hL=>(Finset.mem_filter.mp hL).2)
    (fun L hL=>(mem_idealDivisors hI).mp (Finset.mem_filter.mp hL).1)
  have hc : ((Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j.val)).card:ℝ)≤
      (A.card:ℝ)*N.card*(Fintype.card RayCharacter:ℝ)^2 := by exact_mod_cast hcard
  exact hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)) (sq_nonneg _))

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_row_key_injective

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_block_code_injective
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_joint_block_code_injective

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_row_fiber_card

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_projector_fiber_bound

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_joint_source_keys
