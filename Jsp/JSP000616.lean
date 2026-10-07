import Init.Data.List.Basic
import Init.Data.List.Lemmas

set_option maxRecDepth 1000000

/-!
# JSP-000616 - Lean 4.20.0, no Mathlib

## Question
How many sum-free subsets do the first several positive integers have?

## Answer (for {1,...,6})
A subset S of {1,...,6} is sum-free if there do not exist a, b, c in S
such that a + b = c. For {1,...,6} there are exactly 24 sum-free subsets
out of 2^6 = 64 total subsets.

All proofs use decide. No sorry, no admit, no native_decide.
-/

def isSumFree (S : List Nat) : Bool :=
  ! (S.any fun a => S.any fun b => S.any fun c => a + b = c)

def powerSet {alpha : Type} : List alpha -> List (List alpha)
  | []      => [[]]
  | (x::xs) => (powerSet xs).map (fun s => x :: s) ++ powerSet xs

def allSubsets (n : Nat) : List (List Nat) :=
  powerSet (List.range' 1 n)

def countSumFree (n : Nat) : Nat :=
  (allSubsets n).filter isSumFree |>.length

theorem sumFreeCount_6 : countSumFree 6 = 24 := by decide

#print axioms sumFreeCount_6