import Mathlib

namespace algebra

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

variable {G : Type} [group G] {a b c : G}

theorem mul_right (h : a = b) c : mul a c = mul b c := by
  subst h
  rfl

theorem cancel_right (h : mul a c = mul b c) : a = b := by
  have key := mul_right h (inv c)
  rw [assoc, invr, neutr] at key
  rw [assoc, invr, neutr] at key
  assumption

theorem inv_unique (h : mul b a = e) : b = inv a := by
  have h1 : mul a (inv a) = e := invr a
  have h2 : mul b (mul a (inv a)) = mul b e := by
    rw [h1]
  rw [neutr] at h2
  rw [← assoc] at h2
  rw [h] at h2
  rw [neutl] at h2
  exact h2.symm

-- Notation

instance : One G where one := group.e

instance : Mul G where mul := group.mul

instance : Inv G where inv := group.inv

theorem assoc' : (a * b) * c = a * (b * c) := assoc a b c

@[simp]
theorem invl' : a⁻¹ * a = 1 := invl a

@[simp]
theorem neutl' : 1 * a = a := neutl a

example (h : c * a = c * b) : a = b := by
  have : c⁻¹ * (c * a) = c⁻¹ * (c * b) := by simp [h]
  -- rw [← assoc] at this -- fails
  simp [← assoc'] at this
  exact this
  -- simpa [← assoc']

-- Plumbing

instance : Group G := Group.ofLeftAxioms assoc neutl invl

example (h : mul b a = e) : b = inv a := by
  change b * a = 1 at h
  change b = a⁻¹
  -- exact?
  exact eq_inv_of_mul_eq_one_left h

example (h : mul b a = e) : b = inv a := eq_inv_of_mul_eq_one_left h

end algebra
