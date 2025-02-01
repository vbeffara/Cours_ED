import Mathlib

def implies (P Q : Prop) : Prop := P → Q

example (P Q : Prop) (hPQ : implies P Q) (hP : P) : Q := by

  -- backward reasoning
  -- apply hPQ
  -- exact hP

  -- forward reasoning
  -- apply hPQ at hP
  -- exact hP

  -- Tactic: exact?
  -- exact?
  -- exact hPQ hP

  sorry

def equivalent (P Q : Prop) : Prop := implies P Q ∧ implies Q P

theorem equiv_comm (P Q : Prop) (hPQ : equivalent P Q) :
    equivalent Q P := by
  constructor
  · unfold equivalent at hPQ
    obtain ⟨h1, h2⟩ := hPQ
    exact h2
  · have h1 : P → Q := hPQ.1
    intro hP
    apply h1
    assumption

example (P Q : Prop) (hPQ : equivalent P Q) : equivalent Q P := by
  -- Tactic: exact?
  -- exact?
  -- exact equiv_comm P Q hPQ

  -- Tactic: exact? after unfolding
  -- unfold equivalent at hPQ ⊢
  -- exact?
  -- exact id (And.symm hPQ)

  -- dsimp [equivalent] at *
  -- solve_by_elim

  simp_all [equivalent]

#check Iff.symm
#print Iff.symm

theorem equiv_comm' (P Q : Prop) (hPQ : equivalent P Q) : equivalent Q P :=
  ⟨hPQ.2, hPQ.1⟩

#print equiv_comm
#print equiv_comm'

example : equiv_comm = equiv_comm' := rfl

-- More idiomatic version

variable {P Q : Prop}

example (hPQ : equivalent P Q) : equivalent Q P :=
  ⟨hPQ.2, hPQ.1⟩
