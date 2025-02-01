import Mathlib

-- Induction

namespace naturels

inductive nat
| zero : nat
| succ : nat → nat

def add (a : nat) : nat → nat
| nat.zero => a
| nat.succ b => (add a b).succ

#check add
#check @add
#print add

variable {a b : nat}

theorem nat_add_zero : add a nat.zero = a := by
  rfl

theorem nat_zero_add : add nat.zero b = b := by
  induction b with
  | zero => rfl
  | succ b' hr =>
    rw [add]
    rw [hr]

def mul (a : nat) : nat → nat
| nat.zero => nat.zero
| nat.succ b => add (mul a b) a

example : mul a nat.zero.succ = a := by
  rw [mul, mul, nat_zero_add]

example : mul nat.zero b = nat.zero := by
  induction b with
  | zero => rfl
  | succ b hb =>
    rw [mul]
    rw [add]
    exact hb

end naturels

-- Working with integers

variable {n : ℤ}

example (hn : Odd n) : ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  unfold Odd at hn
  obtain ⟨k, hk⟩ := hn
  subst hk
  have h1 := k.even_or_odd
  cases' h1  with h h
  · obtain ⟨l, hl⟩ := h
    subst hl
    ring_nf
    use l + 2 * l ^ 2
    ring
  · obtain ⟨l, rfl⟩ := h
    use 1 + 3 * l + 2 * l ^ 2
    ring
