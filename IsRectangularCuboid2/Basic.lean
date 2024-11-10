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

def perfect_powers : Set ℕ := { n | ∃ m k : ℕ, m ≥ 2 ∧ k ≥ 2 ∧ n = m ^ k }
def non_perfect_powers : Set ℕ := { n | n ≥ 2 ∧ n ∉ perfect_powers }

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
