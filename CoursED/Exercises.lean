import Mathlib
import CoursED.Demos

namespace topology

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, continuous_at f x

def unif_limit (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |F n x - f x| ≤ ε

theorem continuous_limit (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (h_F : ∀ n, continuous (F n))
    (h_lim : unif_limit F f) : continuous f := by
  sorry

theorem continuous_iff (f : ℝ → ℝ) (x₀ : ℝ) :
    continuous_at f x₀ ↔
      (∀ u : ℕ → ℝ, seq_limit u x₀ → seq_limit (f ∘ u) (f x₀)) := by
  constructor
  · sorry
  · intro h ε hε
    contrapose! h
    sorry

end topology

namespace algebra

open group

variable {G : Type} [group G]

theorem group_inv_mul {a b : G} : inv (mul a b) = mul (inv b) (inv a) := by
  sorry

structure group_action (G : Type) [group G] (E : Type) where
  act : G → E → E
  id : ∀ e : E, act 1 e = e
  assoc : ∀ g₁ g₂ : G, ∀ e : E, act g₁ (act g₂ e) = act (g₁ * g₂) e

example : group_action G G where
  act g h := g * h
  id := sorry
  assoc := sorry

example : group_action G G where
  act g h := g * h * g⁻¹
  id := sorry
  assoc := sorry

structure subgroup (G : Type) [group G] where
  support : Set G
  id : 1 ∈ support
  mul : ∀ g ∈ support, ∀ h ∈ support, g * h ∈ support

variable {H : subgroup G}

def related (H : subgroup G) (g₁ g₂ : G) : Prop :=
  ∃ h ∈ H.support, g₂ = h * g₁

def normal (H : subgroup G) : Prop :=
  ∀ h ∈ H.support, ∀ g : G, g * h * g⁻¹ ∈ H.support

theorem rel_equiv (H : subgroup G) : Equivalence (related H) := sorry

def rel_setoid (H : subgroup G) : Setoid G where
  r := related H
  iseqv := rel_equiv H

def quotient (G : Type) [group G] (H : subgroup G) := Quotient (rel_setoid H)

-- Multiplication is well-defined on the quotient
theorem key (g₁ g₂ h₁ h₂ : G) (H1 : related H g₁ g₂) (H2 : related H h₁ h₂) :
    related H (g₁ * h₁) (g₂ * h₂) := by
  sorry

instance (h_normal : normal H) : group (quotient G H) where
  mul := by -- Pass multiplication to the quotient
    #check Quotient.map₂
    apply Quotient.map₂ group.mul
    intros g₁ g₂ H1 h₁ h₂ H2
    apply key
    assumption
    assumption
  e := sorry
  inv := sorry
  assoc := by
    #check Quotient.map₂_mk
    intros a b c
    obtain ⟨a, rfl⟩ := a.exists_rep
    obtain ⟨b, rfl⟩ := b.exists_rep
    obtain ⟨c, rfl⟩ := c.exists_rep
    simp only [Quotient.map₂_mk]
    simp [group.assoc]
  neutl := sorry
  neutr := sorry
  invl := sorry
  invr := sorry

end algebra

namespace induction

inductive nat
| zero : nat
| succ : nat → nat

def add (a : nat) : nat → nat
| nat.zero => a
| nat.succ b => (add a b).succ

def mul (a : nat) : nat → nat
| nat.zero => nat.zero
| nat.succ b => add (mul a b) a

variable {a b : nat}

theorem nat_add_zero : add a nat.zero = a := by
  rfl

theorem nat_zero_add : add nat.zero b = b := by
  induction b with
  | zero => rfl
  | succ b' hr =>
    rw [add]
    rw [hr]

theorem nat_add_comm : add a b = add b a := sorry

theorem nat_mul_comm : mul a b = mul b a := sorry

end induction

namespace arithmetic

def divides (a b : ℕ) := ∃ k, b = a * k

def prime (n : ℕ) := 2 ≤ n ∧ ∀ a, divides a n → a = 1 ∨ a = n

theorem prime_mod (n : ℕ) (hn : prime n) :
    (∃ k, n = 6 * k + 1) ∨ (∃ k, n = 6 * k + 5) := by
  sorry

theorem infinite_primes : ∀ a, ∃ b > a, prime b := by
  intro n
  let N : ℕ := n.factorial + 1
  have h1 : ∃ p : ℕ, prime p ∧ divides p N := sorry
  obtain ⟨p, hp1, hp2⟩ := h1
  refine ⟨p, ?_, hp1⟩
  contrapose! hp2
  sorry

end arithmetic
