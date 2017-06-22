module List.NotInList where

open import GPBindings

open import Function
open import Data.List
open import Data.List.Any as Any hiding (map)
open Any.Membership-≡ 
open import Data.Bool
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable

_≢′_ : V → V → Set
x ≢′ y = ⌊ x ≟v y ⌋ ≡ false

lemma≢′sound : {x y : V} → x ≢′ y → x ≢ y
lemma≢′sound {x} x≢′x refl with x ≟v x
lemma≢′sound {x} x≢′x refl | no  x≢x = x≢x refl
lemma≢′sound {x} ()   refl | yes _ 

lemma≢′complete : {x y : V} → x ≢ y → x ≢′ y
lemma≢′complete {x} {y} x≢y with x ≟v y 
lemma≢′complete {x} {y} x≢y | yes x≡y = ⊥-elim (x≢y x≡y)
lemma≢′complete {x} {y} x≢y | no _    = refl

proof≢′Irrelevance : {n m : V}(p1 p2 : n ≢′ m) → p1 ≡ p2
proof≢′Irrelevance {n} {m}   p1   p2 with n ≟v m 
proof≢′Irrelevance {n} {.n}  ()   p2   | yes refl 
proof≢′Irrelevance {n} {m}   refl refl | no _ = refl

-- next is impossible
-- proof : (n m : ℕ)(p1 p2 : n ≢ m) → p1 ≡ p2

data _∉′_ (x : V) : List V → Set where
  ∉′[] : x ∉′ []
  ∉′∷  : {y : V}{xs : List V} → x ≢′ y → x ∉′ xs → x ∉′ (y ∷ xs)

lemma∉′sound : {x : V}{xs : List V} → x ∉′ xs → x ∉ xs
lemma∉′sound {xs = []}      _     ()
lemma∉′sound {xs = y ∷ xs} (∉′∷ x≢′y x∉′xs) (here x≡y)   = ⊥-elim ((lemma≢′sound x≢′y) x≡y)
lemma∉′sound {xs = y ∷ xs} (∉′∷ x≢′y x∉′xs) (there x∈xs) = lemma∉′sound x∉′xs x∈xs

lemma∉′complete : {x : V}{xs : List V} → x ∉ xs → x ∉′ xs
lemma∉′complete {x} {[]}      x∉xs = ∉′[]
lemma∉′complete {x} {y ∷ xs}  x∉xs with x ≟v y 
lemma∉′complete {x} {xs = .x ∷ xs}  x∉x∷xs | yes refl = ⊥-elim (x∉x∷xs (here refl))
lemma∉′complete {x} {xs =  y ∷ xs}  x∉y∷xs | no x≢y   = ∉′∷ (lemma≢′complete x≢y) (lemma∉′complete (x∉y∷xs ∘ there))

proof∉′Irrelevance : {x : V}{xs : List V}(p1 p2 : x ∉′ xs) → p1 ≡ p2
proof∉′Irrelevance {x} {[]}       ∉′[]         ∉′[]        = refl
proof∉′Irrelevance {x} {y ∷ xs}   (∉′∷ x₁ p1)  (∉′∷ x₂ p2) = cong₂ ∉′∷ (proof≢′Irrelevance x₁ x₂) (proof∉′Irrelevance p1 p2)
