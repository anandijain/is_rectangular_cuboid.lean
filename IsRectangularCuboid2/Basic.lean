-- import Mathlib.Algebra.BigOperators.Ring
-- import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Analysis.Convex.Side
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Real.Irrational
open scoped Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate
open Module Complex EuclideanGeometry
open AffineSubspace Module
open Affine

-- section AffineSpace'

-- variable (k : Type*) {V : Type*} {P : Type*}
-- variable {ι : Type*}

-- open AffineSubspace Module

-- variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
-- variable [AddCommGroup V] [MetricSpace P] [hd2 : Fact (finrank k V = 2)] [Module.Oriented ℝ V (Fin 2)]
section my_sec
variable (k : Type*) {V : Type*} {P : Type*}
variable {ι : Type*}

-- variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P] [Invertible (2 : k)]
-- variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
-- variable [Module ℝ V]
-- variable [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

variable (a b : P)
def s : Set P := {a, b}
#check s
-- theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
theorem ab_collinear (a b : P) : Collinear ℝ ({a, b} : Set P) := collinear_pair ℝ a b

#eval EuclideanGeometry.oangle a b (midpoint ℝ a b)
#check EuclideanGeometry.oangle a b (midpoint ℝ a b)
-- #check (AffineMap.lineMap a b)

theorem midpoint_collinear (a b : P) : Collinear ℝ ({a, b, midpoint ℝ a b} : Set P) := by
  have m :=  midpoint ℝ a b
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use a, b -ᵥ a
  intro p hp
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  cases' hp with hp hp
  · use 0
    simp [hp]
  cases' hp with hp hp
  . use 1
    simp [hp]
  . use (1/2 : ℝ)
    simp [hp]
    rw [midpoint, AffineMap.lineMap]
    simp
end my_sec
section foo
theorem irr2 : Irrational 2 := by
  unfold Irrational

  sorry

variable (p q r : Prop)
#check And p q
fun
#check p → (q → p) -- is -> left assoc?
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
variable (f : A -> B)
#check f

theorem even_pow_is_even (n m: ℕ) (hp : Even n) : Even (n ^ m) := by
  sorry

theorem roots_2_irr (n : ℕ) (hp: n >= 2) : Irrational (2 ^ (1/n)) := by
  sorry

-- how do i find the smallest \N in lean?
-- variable (n : ℕ)
-- variable (x : ℕ -> ℝ)
-- #check (x n)

def foo x :=
  match x with
  | 0   => (1 : ℚ)
  | n+1 => ((1/2) : ℚ) * (foo n) + 1
#eval (1/2) * 1

#check foo
#eval foo 2

theorem equality_ab (a b ε : ℝ) (hp : |a-b| < ε ) : a=b := by
  sorry


theorem divs (n m: ℕ) (hp: ¬IsSquare n) (hpp: n ∣ (m^2)) : n ∣ m := by
  sorry

theorem ex1_2_2 (r : ℚ): ¬ ∃r, 2 ^ r = 3 := by
  unfold Rat
  sorry
end foo









section ex1_2_4

-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Covering.20.5CN.20with.20powers.20of.20non-perfect.20powers

/--
Prop stating that a numer is a perfect power.
-/
def IsPerfectPower (m : ℕ) := ∃ n k, 1 < k ∧ n ^ k = m

theorem one_is_perf_pow : IsPerfectPower 1 := by
  unfold IsPerfectPower
  use 1, 2
  simp

-- #eval 0 ∈ ℕ
#check Nat
#check Nat.zero
#check Nat.zero.succ
#check Nat.succ Nat.zero

theorem zero_is_perf_pow : IsPerfectPower 0 := by
  unfold IsPerfectPower
  use 0, 2
  simp


def Perfect : Set ℕ := {n : ℕ | IsPerfectPower n}
def nonPerfect : Set ℕ := {n : ℕ | ¬IsPerfectPower n}
#check Perfect
#check Perfect ∪ nonPerfect

variable (a : Bool)
#check a ∨ ¬a

theorem a_or_not_a (a : Bool) : a ∨ ¬a := by
  simp

theorem n_is_perfect_or_not (n : ℕ) : (IsPerfectPower n ∨ ¬IsPerfectPower n) := by
  apply Classical.em

/-
Thanks to Floris van Doorn for this proof
-/
theorem covers_n : Perfect ∪ nonPerfect = Set.univ := by
  unfold Perfect nonPerfect
  ext n
  simp
  exact n_is_perfect_or_not n

theorem perf_disojoint_nonperf : Perfect ∩ nonPerfect = ∅ := by
  unfold Perfect nonPerfect
  ext n
  simp


#eval true ∨ true
#check ∀ a : ℤ, ∃! b : ℤ, a + 1 = b

theorem simple_uniqueness_proof : ∀ a : ℤ, ∃! b : ℤ, a + 1 = b := by
  intros a
  use a+1
  apply And.intro
  . rfl
  . intros y hy
    rw [hy]


theorem simpler : ∃! a:ℤ, 1+a=2 := by
  use 1
  apply And.intro
  . rfl
  . intro y
    intro hy
    linarith

#check (1,2)
-- #eval 0^0

lemma mylemma : ∀a:ℕ, a^0=1 := by
  intro a
  rw [pow_zero]

lemma mylemma2 : ∀a:ℕ, a^1=a := by
  intro a
  rw [pow_one]

lemma not_perfect_power_implies_k_le_one (m a k : ℕ)
  (h : ¬IsPerfectPower m) (hpow : a ^ k = m) : k = 0 ∨ k = 1 := by
  by_cases hk : k > 1
  · -- Case 1: k > 1
    exfalso
    apply h
    use a, k

  · -- Case 2: k ≤ 1
    cases k
    · left; rfl -- k = 0
    · right; linarith -- k = 1

/-
if m is not a perfect power, then the only solution for a^b=m must be a=m b=1.
the reason is, we are guaranteed by `h` that ¬∃ n,k : N, k>1 ∧ n^k=m
this means the only options to find solutions for a and b limits b to be 0 or 1.
in the zero case, there is no way to make a^0=m for m>1.
since there is no solution for k=0 and we know that m^1=m ∀m
-/
lemma not_perfect_power_unique_solution (m a b : ℕ)
  (h : ¬IsPerfectPower m) (hm: m > 1) (hab : a ^ b = m) : a = m ∧ b = 1 := by
  apply not_perfect_power_implies_k_le_one m a b at h
  have hb : b = 0 ∨ b = 1 := h hab
  -- want to try b=0 and show that m>1 and a^0 are incompatible
  cases' hb with hb0 hb1
    exfalso
    rw [hb0, pow_zero] at hab
    linarith
  .
    rw [hb1, pow_one] at hab
    exact ⟨hab, hb1⟩


lemma a_perfect_b_not_implies_notequal (a b : ℕ) (ha : IsPerfectPower a) (hb : ¬IsPerfectPower b) : a ≠ b := by
  by_contra h_eq
  rw [h_eq] at ha
  exact hb ha

/--
Every number greater than one can be uniquely represented as a power of a number which isn't a perfect power.
-/
lemma utility_lemma (m : ℕ) (hm : 1 < m) : ∃! n : ℕ × ℕ, ¬IsPerfectPower n.1 ∧ n.1 ^ n.2 = m := by
  have hp : (IsPerfectPower m ∨ ¬IsPerfectPower m) := n_is_perfect_or_not m
  cases hp with
  | inl a =>
    have ha := a
    obtain ⟨na, ka, hk1, hk2⟩ := a
    -- rw [← hk2]
    use (na, ka)
    apply And.intro
    . simp
      apply And.intro
      -- wait what if m=16 (so IsPerfPow) and n=4 (also IsPerf) here, then n is perfect power and 4^2 =  16
      --  i dont think i can prove that n must not be perfect
      -- the way forward is to choose (na,ka) such that na is the smallest possible. then it follows that its not a perfect power
      -- 
      rw [IsPerfectPower]
      --
      -- .
    . simp



  | inr b =>
    use (m, 1)
    apply And.intro
    . simp
      exact b
    . intros y hy
      -- unfold IsPerfectPower at hy
      obtain ⟨hya, hyb⟩ := hy
      /-
      that m is not a perfect power means theres no solution a^b for b > 1.

      that doesn't mean there exists a solution for b=1, except there must always be m^1
      since we know m>1 then there can't be a solution for any a st b=0 gives a^b=m,.
      so the only solution must be (m,1 ).
      -/
      apply not_perfect_power_unique_solution m y.1 y.2 at hyb
      cases' hyb with hyb1 hyb2
      ext
      rw [hyb1]
      rw [hyb2]
      exact b
      apply hm

def setSeq : ℕ → Set ℕ
| 0 => nonPerfect ∪ {0, 1}
| i + 1 => (· ^ (i + 2)) '' nonPerfect

theorem infinite (i : ℕ) : (setSeq i).Infinite := by
  sorry

theorem covers_ℕ : ⋃ n, setSeq n = Set.univ := by
  sorry

theorem pairwise_disjoint : Set.univ.PairwiseDisjoint setSeq := by
  sorry

end ex1_2_4




















/-
Find an infinite set of infinite Sets that are all pairwise disjoint, but the union of all is equal to N.

My solution was to take the non-perfect powers https://oeis.org/A007916 and just take their powers as the sets Ai, and just tack on 0 and 1 to A1.

Alternatively, I could just prove that the sets cover N>=2. But I'm having trouble stating the problem. In english my proof is:

Each Ai is infinite because you can define the map from N -> Ai[i] just by associating the power. ie for A2 (1->3, 2->9, 3->27...).

The union of all is equal to N>2 because either a) you hit a non-perfect power, and therefore the start of an Ai or b) you are a perfect power and belong to an Ai.

I'm having trouble with pairwise disjoint, but this is my argument:
If the start element (the non-perfect power) of the Ai and Aj are coprime, they must be disjoint. If they aren't coprime but one is even and the other is odd, then they cannot share elements as all powers will be different kinds (odds evens).
If Ai and Aj arent coprime and are both either odd or even, you can make the argument that you can't satisfy the equations for the powers of their prime factorizations.
Ex. 6 and 12 are both non-perfect powers but are both even. but if you try to find 6^n=12^m (written as 2^n*3^n=2^2m*3^m when factorized) then you cannot find n = 2m and n = m except for n=0 which isn't valid.
-/
-- theorem ex1_2_4 := sorry

/-
Show that, for an arbitrary function g : R → R, it is always true that
g(A ∩ B) ⊆ g(A) ∩ g(B) for all sets A, B ⊆ R
-/
theorem ex1_2_7c (A B : Set ℝ) (g : ℝ -> ℝ) : g (A ∩ B) ⊆ (g A) ∩ (g B)
variable (A B : Set ℝ)
#check A ∩ B
