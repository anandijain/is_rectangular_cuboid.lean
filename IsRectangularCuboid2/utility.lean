import Mathlib.Tactic
section ex1_2_4
/-
Exercise 1.2.4. Produce an infinite collection of sets A1, A2, A3, . . . with the
property that every Ai has an infinite number of elements, Ai ∩ Aj = ∅ for all
i, = j, and ⋃∞
i=1 Ai = N
-/
def IsPerfectPower (m : ℕ) := ∃ n k, k > 1 ∧ n^k = m

#eval 0^2 -- 0
#eval 0^0 -- 1

lemma zero_is_perfect_power : (IsPerfectPower 0) := by
  unfold IsPerfectPower
  use 0
  use 2
  simp


lemma one_is_perfect_power : (IsPerfectPower 1) := by
  unfold IsPerfectPower
  use 1
  use 2
  simp

lemma n_perfect_or_not (n : ℕ) : IsPerfectPower n ∨ ¬ IsPerfectPower n := by
  apply Classical.em

lemma not_perfect_power_implies_k_le_one (m a k : ℕ)
  (h : ¬IsPerfectPower m) (hpow : a ^ k = m) : k = 0 ∨ k = 1 := by
  by_cases hk: k > 1
  . exfalso
    apply h
    rw [IsPerfectPower]
    use a
    use k

  . cases k
    . left; simp
    . right; linarith

lemma not_perfect_power_unique_solution (m a b : ℕ)
  (h : ¬IsPerfectPower m) (hm: m > 1) (hab : a ^ b = m) : a = m ∧ b = 1 := by
  apply not_perfect_power_implies_k_le_one m a b at h
  have foo := h hab
  cases' foo with foo1 foo2
  . exfalso
    rw [foo1, pow_zero] at hab
    linarith
  . rw [foo2, pow_one] at hab
    exact ⟨hab, foo2⟩

lemma utility (m : ℕ) (hm : 1 < m) : ∃! n : ℕ × ℕ, ¬IsPerfectPower n.1 ∧ n.1 ^ n.2 = m := by
  have hp: IsPerfectPower m ∨ ¬ IsPerfectPower m := n_perfect_or_not m
  cases hp with
  | inl casea => sorry
  | inr b =>
    use (m, 1)
    apply And.intro
    . simp
      exact b
    . intros y hy
      obtain ⟨hya, hyb⟩ := hy
      apply not_perfect_power_unique_solution m y.1 y.2 at hyb
      cases' hyb with hyb1 hyb2
      ext
      exact hyb1
      exact hyb2
      apply b
      exact hm

end ex1_2_4
