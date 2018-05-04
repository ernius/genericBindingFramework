\begin{code}
module List.ListProperties where

open import Function
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Nat
open import Data.Product renaming (Σ to Σₓ;map to mapₓ) 
open import Data.Bool hiding (_∨_;_≟_)
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Properties
open import Data.List.Any.Membership
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
open Any.Membership-≡ renaming (_∈_ to _∈'_;_∉_ to _∉'_) 
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)
import Function.Equality as FE
open import Function.Inverse hiding (sym;_∘_;map;id)
open Inverse

-- Auxiliary Lemmas about lists membership
c∈xs++ys→c∈xs∨c∈ys : {x : ℕ}{xs ys : List ℕ} → x ∈' xs ++ ys → (x ∈' xs) ∨ (x ∈' ys) 
c∈xs++ys→c∈xs∨c∈ys {x} {xs} {ys} = FE.Π._⟨$⟩_ (from (++↔ {A = ℕ} {P = _≡_ x} {xs = xs} {ys = ys})) 
c∈xs∨c∈ys→c∈xs++ys : {x : ℕ}{xs ys : List ℕ} → x ∈' xs ∨ x ∈' ys → x ∈' xs ++ ys 
c∈xs∨c∈ys→c∈xs++ys {x} {xs} {ys} = FE.Π._⟨$⟩_ (to (++↔ {A = ℕ} {P = _≡_ x} {xs = xs} {ys = ys}))
c∈ys→c∈xs++ys : {xs ys : List ℕ}{x : ℕ} → x ∈' ys → x ∈' xs ++ ys 
c∈ys→c∈xs++ys {xs} {ys} {x} x∈ys = c∈xs∨c∈ys→c∈xs++ys {x} {xs} {ys} (inj₂  x∈ys)
c∈xs→c∈xs++ys : {xs ys : List ℕ} {x : ℕ} → x ∈' xs → x ∈' xs ++ ys 
c∈xs→c∈xs++ys {xs} {ys} {x} x∈ys = c∈xs∨c∈ys→c∈xs++ys {x} {xs} {ys} (inj₁  x∈ys)
c∉xs++ys→c∉xs : {c : ℕ}{xs ys : List ℕ} → c ∉' xs ++ ys → c ∉' xs 
c∉xs++ys→c∉xs {c} {xs} {ys} c∉xs++ys c∈xs = c∉xs++ys (c∈xs∨c∈ys→c∈xs++ys (inj₁ c∈xs))
c∉xs++ys→c∉ys : {c : ℕ}{xs ys : List ℕ} → c ∉' xs ++ ys → c ∉' ys 
c∉xs++ys→c∉ys {c} {xs} {ys} c∉xs++ys c∈ys = c∉xs++ys (c∈xs∨c∈ys→c∈xs++ys {c} {xs} {ys} (inj₂ c∈ys))
d∉abc∷xs→d≢a : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ a
d∉abc∷xs→d≢a {a} {b} {c} {.a} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (here refl))
d∉abc∷xs→d≢b : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ b
d∉abc∷xs→d≢b {a} {b} {c} {.b} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (there (here refl)))
d∉abc∷xs→d≢c : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ c
d∉abc∷xs→d≢c {a} {b} {c} {.c} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (there (there (here refl))))
d∉abc∷xs→d∉xs : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ∉' xs
d∉abc∷xs→d∉xs {a} {b} {c} {d} {xs} d∉abc∷xs d∈xs = ⊥-elim (d∉abc∷xs (there (there (there d∈xs))))
d∉ab∷xs→d≢a : {a b d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ xs) → d ≢ a
d∉ab∷xs→d≢a {a} {b}  {.a} {xs} d∉ab∷xs refl = ⊥-elim (d∉ab∷xs (here refl))
d∉ab∷xs→d≢b : {a b d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ xs) → d ≢ b
d∉ab∷xs→d≢b {a} {b} {.b} {xs} d∉ab∷xs refl = ⊥-elim (d∉ab∷xs (there (here refl)))
d∉ab∷xs→d∉xs : {a b  d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ xs) → d ∉' xs
d∉ab∷xs→d∉xs {a} {b} {d} {xs} d∉ab∷xs d∈xs = ⊥-elim (d∉ab∷xs (there (there d∈xs)))
b∉a∷xs→b≢a : {a b : ℕ}{xs : List ℕ} → b ∉' (a ∷ xs) → b ≢ a
b∉a∷xs→b≢a {a} {.a} {xs} a∉a∷xs refl = ⊥-elim (a∉a∷xs (here refl))
b∉a∷xs→b∉xs : {a b : ℕ}{xs : List ℕ} → b ∉' (a ∷ xs) → b ∉' xs 
b∉a∷xs→b∉xs {a} {b} {xs} b∉a∷xs b∈xs = ⊥-elim (b∉a∷xs (there b∈xs))
c∉x∷xs++ys→c∉x∷xs : {a b : ℕ}{xs ys : List ℕ} → a ∉' (b ∷ (xs ++ ys)) → a ∉' b ∷ xs 
c∉x∷xs++ys→c∉x∷xs a∉b∷xs++ys (here a≡b)    = ⊥-elim (a∉b∷xs++ys (here a≡b))
c∉x∷xs++ys→c∉x∷xs a∉b∷xs++ys (there a∈xs)  = ⊥-elim ((c∉xs++ys→c∉xs (b∉a∷xs→b∉xs a∉b∷xs++ys)) a∈xs)
c∉x∷xs++ys→c∉x∷ys : {a b : ℕ}{xs ys : List ℕ} → a ∉' (b ∷ (xs ++ ys)) → a ∉' b ∷ ys 
c∉x∷xs++ys→c∉x∷ys a∉b∷xs++ys (here a≡b)              = ⊥-elim (a∉b∷xs++ys (here a≡b))
c∉x∷xs++ys→c∉x∷ys {xs = xs} a∉b∷xs++ys (there a∈ys)  = ⊥-elim ((c∉xs++ys→c∉ys {xs = xs} (b∉a∷xs→b∉xs a∉b∷xs++ys)) a∈ys)
x∉xs∧y∈xs⇒y≢x : {x y : ℕ}{xs : List ℕ} → x ∉' xs → y ∈' xs → y ≢ x
x∉xs∧y∈xs⇒y≢x {x} {.x} x∉xs x∈xs refl = ⊥-elim (x∉xs x∈xs)
x≢y∧x∉xs⇒x∉y∷xs : {x y : ℕ}{xs : List ℕ} → x ≢ y → x ∉' xs → x ∉' y ∷ xs
x≢y∧x∉xs⇒x∉y∷xs x≢x x∉xs (here refl)  =  ⊥-elim (x≢x refl)
x≢y∧x∉xs⇒x∉y∷xs x≢y x∉xs (there x∈xs) =  ⊥-elim (x∉xs x∈xs)
--
lemmax∉[x]absurd : {x : ℕ} → x ∉' [ x ] → ⊥
lemmax∉[x]absurd x∉[x] = ⊥-elim (x∉[x] (here refl))
--
lemmay∈[x]y≢x : {x y : ℕ} → y ∉' [ x ] → y ≢ x
lemmay∈[x]y≢x y∉[x] y≡x = y∉[x] (here y≡x)
--
lemmay∈[x]y≡x : {x y : ℕ} → y ∈' [ x ] → y ≡ x
lemmay∈[x]y≡x (here y≡x) = y≡x
lemmay∈[x]y≡x (there ()) 
--
lemmaxs++[]≡xs : {A : Set}(xs : List A) → xs ++ [] ≡ xs
lemmaxs++[]≡xs []        =  refl
lemmaxs++[]≡xs (x ∷ xs)  =  cong (_∷_ x) (lemmaxs++[]≡xs xs)
-- Auxiliary functions and properties
Prop- : ℕ → ℕ → Bool
Prop- x = (λ y → not (⌊ x ≟ y ⌋))
--
infixl 5 _-_
_-_ : List ℕ → ℕ → List ℕ
xs - x = filter (Prop- x) xs
--
-prop : ∀ {a b} → b ≢ a → Prop- b a ≡ true
-prop {a} {b} b≢a with b ≟ a 
... | yes b≡a  = ⊥-elim (b≢a b≡a)
... | no _     = refl
--
-prop≢ :  ∀ {a b} → Prop- b a ≡ true → b ≢ a 
-prop≢ {a} {b} prop-ba≡true with b ≟ a
... | no b≢a  = b≢a
-prop≢ {a} {b} ()
    | yes _  
--
lemmafilter→ : {x : ℕ}{xs : List ℕ}{p : ℕ → Bool} → x ∈' filter p xs → (p x ≡ true × x ∈' xs)
lemmafilter→ {x} {[]}      {p}  ()
lemmafilter→ {x} {y ∷ xs}  {p}  x∈filterpy∷xs with p y | inspect p y
...  | false   | [ py≡false ]ᵢ = mapₓ id there (lemmafilter→ {x} {xs} {p} x∈filterpy∷xs)
lemmafilter→ {x} {.x ∷ xs} {p}  (here refl)         
     | true | [ px≡true ]ᵢ = px≡true , here refl
lemmafilter→ {x} {y ∷ xs}  {p}  (there x∈filterpxs)  
     | true | [ py≡true ]ᵢ = mapₓ id there (lemmafilter→ {x} {xs} {p} x∈filterpxs)
--
lemmafilter← : (x : ℕ)(xs : List ℕ)(p : ℕ → Bool) → p x ≡ true →  x ∈' xs → x ∈' filter p xs
lemmafilter← x (.x ∷ xs)  p px≡true (here refl) with p x
lemmafilter← x (.x ∷ xs)  p px≡true (here refl) | true = here refl
lemmafilter← x (.x ∷ xs)  p ()      (here refl) | false 
lemmafilter← x (y ∷ xs)   p px≡true (there x∈xs) with p y
... | false = lemmafilter← x xs p px≡true x∈xs
... | true  = there (lemmafilter← x xs p px≡true x∈xs)
--
lemma- : {x : ℕ}{xs : List ℕ} → x ∈' xs - x → ⊥
lemma- {x} {xs} x∈xs-x = (-prop≢ (proj₁ (lemmafilter→ {x} {xs} {p = Prop- x} x∈xs-x))) refl
--
lemma-∈ : {x y : ℕ}{xs : List ℕ} → x ∈' xs - y → x ∈' xs
lemma-∈ {x} {y} {xs} x∈xs-y = proj₂ (lemmafilter→ {x} {xs} {Prop- y} x∈xs-y)
--
lemma-∉ : {x y : ℕ}{xs : List ℕ} → y ≢ x → x ∉' xs - y → x ∉' xs
lemma-∉ {x} {y} {xs} x≢y x∉xs-y with any (_≟_ x) xs 
... | yes x∈xs = ⊥-elim (x∉xs-y (lemmafilter← x xs (Prop- y) (-prop x≢y) x∈xs)) 
... | no  x∉xs = x∉xs
--
lemmaΓ⊆Δ→Γ,x⊆Δ,x : {x : ℕ}{Γ Δ : List ℕ} → Γ ⊆ Δ → x ∷ Γ ⊆ x ∷ Δ
lemmaΓ⊆Δ→Γ,x⊆Δ,x {x} Γ⊆Δ {y} (here y≡x)     = here y≡x
lemmaΓ⊆Δ→Γ,x⊆Δ,x {x} Γ⊆Δ {y} (there y∈Γ,x)  = there (Γ⊆Δ y∈Γ,x)
--
lemmaΓ⊆Γ,x : {Γ : List ℕ}{x : ℕ} → Γ ⊆ x ∷ Γ
lemmaΓ⊆Γ,x {Γ} {x} {y} y∈Γ = there y∈Γ
--
lemmax∈Γ⇒Γ,x⊆Γ : {Γ : List ℕ}{x : ℕ} → x ∈' Γ → x ∷ Γ ⊆ Γ
lemmax∈Γ⇒Γ,x⊆Γ x∈Γ (here refl)  = x∈Γ
lemmax∈Γ⇒Γ,x⊆Γ x∈Γ (there y∈Γ)  = y∈Γ
--
lemma∈ : {Γ : List ℕ}{x y : ℕ} → y ∈' x ∷ Γ → x ≢ y → y ∈' Γ
lemma∈ {Γ} {x} .{x}  (here refl) x≢y = ⊥-elim (x≢y refl)
lemma∈ {Γ} {x} {y}   (there y∈Γ) x≢y = y∈Γ
--
lemmaΓ⊆Γ++Γ : {Γ : List ℕ} → Γ ++ Γ ⊆ Γ
lemmaΓ⊆Γ++Γ x∈Γ++Γ with c∈xs++ys→c∈xs∨c∈ys x∈Γ++Γ 
... | inj₁ x∈Γ = x∈Γ
... | inj₂ x∈Γ = x∈Γ
--
lemmaΓ⊆Γ++Δ : {Γ Δ : List ℕ} → Γ ⊆ Γ ++ Δ
lemmaΓ⊆Γ++Δ x∈Γ = c∈xs∨c∈ys→c∈xs++ys (inj₁ x∈Γ)
--
lemmaΓ,x,y⊆Γ,y,x : {x y : ℕ}{Γ : List ℕ} → y ∷ x ∷ Γ ⊆ x ∷ y ∷ Γ
lemmaΓ,x,y⊆Γ,y,x (here refl)          = there (here refl)
lemmaΓ,x,y⊆Γ,y,x (there (here refl))  = here refl
lemmaΓ,x,y⊆Γ,y,x (there (there z∈Γ))  = there (there z∈Γ)
--
lemmaΓ++Δ,x⊆Γ,x++Δ : {Γ Δ : List ℕ}{x : ℕ} → Γ ++ x ∷ Δ ⊆ x ∷ Γ ++ Δ
lemmaΓ++Δ,x⊆Γ,x++Δ {Γ} {Δ} {x} {y} y∈Γ++x∷Δ with c∈xs++ys→c∈xs∨c∈ys {y} {Γ} {x ∷ Δ} y∈Γ++x∷Δ
... | inj₁ y∈Γ          = c∈xs∨c∈ys→c∈xs++ys (inj₁ (there y∈Γ))
... | inj₂ (here y≡x)   = here y≡x
... | inj₂ (there y∈Δ)  = c∈xs∨c∈ys→c∈xs++ys {y} {x ∷ Γ} (inj₂ y∈Δ)

lemma[x]-y : {x y : ℕ} → x ≢ y → [ x ] - y ≡ [ x ]
lemma[x]-y {x} {y} x≢y with y ≟ x
... | yes y≡x = ⊥-elim (x≢y (sym y≡x))
... | no  _   = refl

lemma[x]-x : {x : ℕ} → [ x ] - x ≡ []
lemma[x]-x {x} with x ≟ x
... | yes _  = refl
... | no x≢x = ⊥-elim (x≢x refl)
--
lemma--idem : {x : ℕ}{xs : List ℕ} → (xs - x) - x ≡ xs - x
lemma--idem {x} {[]}     rewrite lemma[x]-x {x} = refl
lemma--idem {x} {y ∷ xs} with x ≟ y
... | yes _ = lemma--idem {x} {xs}
... | no  x≢y with x ≟ y
...         | no  _   = cong (_∷_ y) (lemma--idem {x} {xs})
...         | yes x≡y = ⊥-elim (x≢y x≡y) 

lemma[x]-x-y≡[y]-x-y : {x y : ℕ} → ([ x ] - x) - y ≡ ([ y ] - x) - y
lemma[x]-x-y≡[y]-x-y {x} {y} with y ≟ x
lemma[x]-x-y≡[y]-x-y {x} {.x} | yes refl = refl
lemma[x]-x-y≡[y]-x-y {x} {y} | no y≢x   = 
  begin≡
    [ x ] - x - y 
  ≡⟨ cong (λ xs → xs - y) (lemma[x]-x {x}) ⟩
    [] - y
  ≡⟨ refl ⟩
    []
  ≡⟨ sym (lemma[x]-x {y}) ⟩
    [ y ] - y
  ≡⟨ sym (cong (λ xs → xs - y) (lemma[x]-y y≢x)) ⟩  
    [ y ] - x - y
  □

lemma-++-∷-1 : {x : ℕ}{xs ys : List ℕ} → x ∈' ys → xs ⊆ ys → x ∷ xs ⊆ ys
lemma-++-∷-1 {x} {xs} {ys} x∈ys xs⊆ys (here refl)  = x∈ys
lemma-++-∷-1 {x} {xs} {ys} x∈ys xs⊆ys (there y∈xs) =  xs⊆ys y∈xs

lemma-++-∷-2 : {x : ℕ}{xs ys : List ℕ} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
lemma-++-∷-2 {x} {xs} {ys} xs⊆ys (here refl)  = here  refl
lemma-++-∷-2 {x} {xs} {ys} xs⊆ys (there y∈xs) = there (xs⊆ys y∈xs)

lemma-++-1 : {xs xs' ys : List ℕ} → xs ⊆ xs' → xs ⊆ xs' ++ ys
lemma-++-1 {xs} {xs'} {ys} xs⊆xs' {y} y∈xs = c∈xs∨c∈ys→c∈xs++ys {y} {xs'} {ys} (inj₁  (xs⊆xs' y∈xs))

lemma-++ : {xs xs' ys ys' : List ℕ} → xs ⊆ xs' → ys ⊆ ys' → xs ++ ys ⊆ xs' ++ ys'
lemma-++ {xs} {xs'} {ys} {ys'} xs⊆xs' ys⊆ys' {x} x∈xs++ys with c∈xs++ys→c∈xs∨c∈ys {x} {xs} {ys} x∈xs++ys
... | inj₁ x∈xs = c∈xs→c∈xs++ys {xs'} {ys'} {x} (xs⊆xs' x∈xs)
... | inj₂ x∈ys = c∈ys→c∈xs++ys {xs'} {ys'} {x} (ys⊆ys' x∈ys)

lemma-⊆∷ : {x : ℕ}{xs ys zs : List ℕ} → xs ⊆ ys → xs ⊆ x ∷ ys ++ zs
lemma-⊆∷ {x} {xs} {ys} {zs} xs⊆ys {y} y∈xs = there (c∈xs→c∈xs++ys {ys} {zs} {y} (xs⊆ys y∈xs))

lemma⊆ : {xs ys zs ws : List ℕ} → xs ⊆ ys ++ zs → zs ⊆ ys ++ ws → xs ⊆ ys ++ ws
lemma⊆ {xs} {ys} {zs} {ws} xs⊆ys++zs zs⊆ys++ws {x} x∈xs with c∈xs++ys→c∈xs∨c∈ys {x} {ys} {zs} (xs⊆ys++zs x∈xs)
... | inj₁ x∈ys = c∈xs→c∈xs++ys {ys} {ws} {x} x∈ys
... | inj₂ x∈zs with c∈xs++ys→c∈xs∨c∈ys {x} {ys} {ws} (zs⊆ys++ws x∈zs)
...             | inj₁ x∈ys = c∈xs→c∈xs++ys {ys} {ws} {x} x∈ys
...             | inj₂ x∈ws = c∈ys→c∈xs++ys {ys} {ws} {x} x∈ws

lemma⊆m : {xs ys xs' ys' zs : List ℕ} → xs ⊆ zs ++ xs' → ys ⊆ zs ++ ys' → xs ++ ys ⊆ zs ++ xs' ++ ys'
lemma⊆m {xs} {ys} {xs'} {ys'} {zs} xs⊆zs++xs' ys⊆zs++ys' {x} x∈xs++ys with c∈xs++ys→c∈xs∨c∈ys {x} {xs} {ys} x∈xs++ys
... | inj₂ x∈ys with c∈xs++ys→c∈xs∨c∈ys {x} {zs} {ys'} (ys⊆zs++ys' x∈ys)
...             | inj₁ x∈zs  = c∈xs→c∈xs++ys {zs} {xs' ++ ys'} {x} x∈zs
...             | inj₂ x∈ys' = c∈ys→c∈xs++ys {zs} {xs' ++ ys'} {x} (c∈ys→c∈xs++ys {xs'} {ys'} {x} x∈ys')
lemma⊆m {xs} {ys} {xs'} {ys'} {zs} xs⊆zs++xs' ys⊆zs++ys' {x} x∈xs++ys 
    | inj₁ x∈xs with c∈xs++ys→c∈xs∨c∈ys {x} {zs} {xs'} (xs⊆zs++xs' x∈xs)
...             | inj₁ x∈zs  = c∈xs→c∈xs++ys {zs} {xs' ++ ys'} {x} x∈zs
...             | inj₂ x∈xs' = c∈ys→c∈xs++ys {zs} {xs' ++ ys'} {x} (c∈xs→c∈xs++ys {xs'} {ys'} {x} x∈xs')

lemma-⊆ : {x : ℕ}{xs ys zs : List ℕ} → xs ⊆ zs ++ ys → xs - x ⊆ zs ++ (ys - x)
lemma-⊆ {x} {xs} {ys} {zs} xs⊆zs++ys {y} y∈xs-x with lemmafilter→ {y} {xs} {Prop- x} y∈xs-x
... | px≡true , y∈xs with c∈xs++ys→c∈xs∨c∈ys {y} {zs} {ys} (xs⊆zs++ys y∈xs)
...                  | inj₁ y∈zs = c∈xs→c∈xs++ys {zs} {ys - x} {y} y∈zs
...                  | inj₂ y∈ys = c∈ys→c∈xs++ys {zs} {ys - x} {y} (lemmafilter← y ys (Prop- x) px≡true y∈ys)

postulate
  lemma--com : {x y : ℕ}{xs : List ℕ} → (xs - x) - y ≡ (xs - y) - x
  lemma-++- : {x : ℕ}{xs ys : List ℕ} → (xs ++ ys) - x ≡ (xs - x) ++ (ys - x)
  lemma-++-- : {x y : ℕ}{xs ys : List ℕ} → ((xs ++ ys) - x) - y ≡ ((xs - x) - y) ++ ((ys - x) - y)
\end{code}

First element to satisfy some property.

\begin{code}
data First {A : Set}
         (P : A → Set) : List A → Set where
  here  : ∀ {x xs} (px  : P x)                        → First P (x ∷ xs)
  there : ∀ {x xs} (¬px : ¬ (P x))(pxs : First P xs)  → First P (x ∷ xs)
\end{code}


