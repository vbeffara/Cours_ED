import Mathlib

-- Topology

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

theorem continuous_iff (f : ℝ → ℝ) (x₀ : ℝ) :
    continuous_at f x₀ ↔
      (∀ u : ℕ → ℝ, seq_limit u x₀ → seq_limit (f ∘ u) (f x₀)) := by
  sorry

-- Arithmetic

def divides (a b : ℕ) := ∃ k, b = a * k

def prime (n : ℕ) := 2 ≤ n ∧ ∀ a, divides a n → a = 1 ∨ a = n

theorem prime_mod (n : ℕ) (hn : prime n) :
    (∃ k, n = 6 * k + 1) ∨ (∃ k, n = 6 * k + 5) := by
  sorry

theorem infinite_primes : ∀ a, ∃ b > a, prime b := by
  sorry

-- Algebra

class group (G : Type) where
  mul : G → G → G
  e : G
  inv : G → G
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  neutl : ∀ a, mul e a = a
  neutr : ∀ a, mul a e = a
  invl : ∀ a, mul (inv a) a = e
  invr : ∀ a, mul a (inv a) = e

open group

variable {G : Type} [group G]

theorem group_inv_mul {a b : G} : inv (mul a b) = mul (inv b) (inv a) := by
  sorry

-- Induction

inductive nat
| zero : nat
| succ : nat → nat

def add (a : nat) : nat → nat
| nat.zero => a
| nat.succ b => (add a b).succ

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
