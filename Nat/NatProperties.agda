module Nat.NatProperties where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Algebra
open import Algebra.Structures

+-comm = IsCommutativeMonoid.comm (IsCommutativeSemiring.+-isCommutativeMonoid isCommutativeSemiring)

open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)


lemmam>0→n+1≤m+n : {m n : ℕ} → m > zero → suc n ≤′ m + n
lemmam>0→n+1≤m+n {0}     {n} ()
lemmam>0→n+1≤m+n {suc m} {n} 1≤m
  = ≤⇒≤′ (start
            suc n
            ≤⟨ s≤s (n≤m+n m n) ⟩
            suc (m + n)
            ≤⟨ ≤-refl ⟩
            suc m + n
          ◽)

lemman>0→m+1≤m+n : {m n : ℕ} → n > zero → suc m ≤′ m + n
lemman>0→m+1≤m+n {m} {n} 1≤n rewrite sym (+-comm n m) = lemmam>0→n+1≤m+n {n} {m} 1≤n  
