module AlphaInductionTerminating where

open import GPBindings
open import Alpha
open import OcurrBind
open import FreeVariables
open import Swap
open import Fresh
open import List.ListProperties
open import List.NotInList
open import Chi

open import Function
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.List
open import Data.List.All
open import Relation.Nullary
open import Data.Product hiding (swap)
open import Data.List.Any as Any hiding (tail;map)
open Any.Membership-≡
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]ᵢ)

ListNotOcurrBindF : {F : Functor}(G : Functor) → List V → ⟦ G ⟧ (μ F) → Set
ListNotOcurrBindF G xs e = All (λ x → notOcurrBind' x G e) xs

ListNotOcurrBind : {F : Functor} → List V → μ F → Set
ListNotOcurrBind {F} xs ⟨ e ⟩ = ListNotOcurrBindF F xs e

get : {F : Functor}{xs : List V}{e : μ F} → ListNotOcurrBind xs e → (x : V) → x ∈ xs → x notOcurrBind e
get {F} {xs} {⟨ e ⟩} notcourr x x∈xs = (lookup notcourr) {x} x∈xs

{-# TERMINATING #-}
bindersFreeαElemF : 
    {F : Functor}(G : Functor)(xs : List V)(e : ⟦ G ⟧ (μ F))
    → ∃ (λ e' → ListNotOcurrBindF {F} G xs e')
bindersFreeαElemF (|v| x)        xs e     
  = e , tabulate (λ y∈xs → notOcurrBv)
bindersFreeαElemF |1|            xs e     
  = e , tabulate (λ y∈xs → notOcurrB1)
bindersFreeαElemF (|E| x)        xs e     
  = e , tabulate (λ y∈xs → notOcurrBE)
bindersFreeαElemF (|Ef| G)       xs ⟨ e ⟩ 
  = Data.Product.map  (⟨_⟩) 
                      (λ notOcurr → tabulate (notOcurrBEf ∘ (lookup notOcurr))) 
                      (bindersFreeαElemF G xs e)
bindersFreeαElemF {F} |R|        xs ⟨ e ⟩ 
  = Data.Product.map  (⟨_⟩) 
                      (λ notOcurr → tabulate (notOcurrBR ∘ (lookup notOcurr))) 
                      (bindersFreeαElemF F xs e)
bindersFreeαElemF (G₁ |+| G₂)    xs (inj₁ e) 
  = Data.Product.map  inj₁ 
                      (λ notOcurr → tabulate (notOcurrBinj₁ ∘ (lookup notOcurr)))
                      (bindersFreeαElemF G₁ xs e)
bindersFreeαElemF (G₁ |+| G₂)    xs (inj₂ e) 
  = Data.Product.map  inj₂
                      (λ notOcurr → tabulate (notOcurrBinj₂ ∘ (lookup notOcurr)))
                      (bindersFreeαElemF G₂ xs e)
bindersFreeαElemF (G₁ |x| G₂)    xs (e₁ , e₂) 
  with  bindersFreeαElemF G₁ xs e₁ | bindersFreeαElemF G₂ xs e₂ 
... | (e₁′ , notOcurr₁) | (e₂′ , notOcurr₂)
  = (e₁′ , e₂′) , tabulate (λ x∈xs → notOcurrBx ((lookup notOcurr₁) x∈xs) ((lookup notOcurr₂) x∈xs))
bindersFreeαElemF {F} (|B| S G)  xs (x , e) 
  with fvF {|B| S G} {F} S (x , e)      
... | zs
  with χ' (xs ++ zs) | lemmaχaux∉ (xs ++ zs)
... | z  | z∉xs++fv
  = Data.Product.map  (λ e' → (z , e'))
                      (λ notOcurr → tabulate (λ y∈xs → notOcurrBB≢ (x∉xs∧y∈xs⇒y≢x (c∉xs++ys→c∉xs z∉xs++fv) y∈xs) ((lookup notOcurr) y∈xs)))
                      (bindersFreeαElemF G xs (swapF F G S x z e))

bindersFreeαElem : 
    {F : Functor}(xs : List V)(e : μ F)
    → ∃ (λ e' → ListNotOcurrBind {F} xs e')
bindersFreeαElem {F} xs ⟨ e ⟩ = Data.Product.map (⟨_⟩) id (bindersFreeαElemF F xs e) 

{-# TERMINATING #-}
lemma-bindersFreeαElemF : {F : Functor}(G : Functor)(xs : List V)(e e' : ⟦ G ⟧ (μ F))
    → ~αF G e e' 
    → bindersFreeαElemF G xs e ≡ bindersFreeαElemF G xs e'
lemma-bindersFreeαElemF (|v| x)     xs e      .e      ~αV          = refl
lemma-bindersFreeαElemF |1|         xs .tt    .tt     ~α1          = refl
lemma-bindersFreeαElemF (|E| x)     xs e      .e      ~αE          = refl
lemma-bindersFreeαElemF (|Ef| G)    xs ⟨ e ⟩   ⟨ e' ⟩      (~αEf e~e')
  = cong  (Data.Product.map  (⟨_⟩) (λ notOcurr → tabulate (notOcurrBEf ∘ (lookup notOcurr)))) 
          (lemma-bindersFreeαElemF G xs e e' e~e')
lemma-bindersFreeαElemF {F} |R|     xs ⟨ e ⟩  ⟨ e' ⟩  (~αR e~e')
  = cong  (Data.Product.map  (⟨_⟩) (λ notOcurr → tabulate (notOcurrBR ∘ (lookup notOcurr)))) 
          (lemma-bindersFreeαElemF F xs e e' e~e')  
lemma-bindersFreeαElemF (G₁ |+| G₂)  xs (inj₁ e) (inj₁ e') (~αinj₁ e~e') 
  = cong  (Data.Product.map  inj₁ (λ notOcurr → tabulate (notOcurrBinj₁ ∘ (lookup notOcurr))))
          (lemma-bindersFreeαElemF G₁ xs e e' e~e')   
lemma-bindersFreeαElemF (G₁ |+| G₂)  xs (inj₂ e) (inj₂ e') (~αinj₂ e~e') 
  = cong  (Data.Product.map  inj₂ (λ notOcurr → tabulate (notOcurrBinj₂ ∘ (lookup notOcurr))))
          (lemma-bindersFreeαElemF G₂ xs e e' e~e')   
lemma-bindersFreeαElemF (G₁ |x| G₂)  xs (e₁ , e₂) (e₁′ , e₂′) (~αx e₁~e₁′ e₂~e₂′) 
  with bindersFreeαElemF G₁ xs e₁  | bindersFreeαElemF G₂ xs e₂  |
       bindersFreeαElemF G₁ xs e₁′  | bindersFreeαElemF G₂ xs e₂′  |
       lemma-bindersFreeαElemF G₁ xs e₁ e₁′ e₁~e₁′ | lemma-bindersFreeαElemF G₂ xs e₂ e₂′ e₂~e₂′
... | (e₁″ , notOcurr₁) | (e₂″ , notOcurr₂) | .(e₁″ , notOcurr₁) | .(e₂″ , notOcurr₂) | refl | refl
  = refl
lemma-bindersFreeαElemF {F} (|B| S G) xs (x , e) (y , e′) xe~ye′ 
  with  fvF {|B| S G} {F} S (x , e)
  |     inspect (fvF {|B| S G} {F} S) (x , e)
  |     fvF {|B| S G} {F} S (y , e′)
  |     lemma~fv S xe~ye′
... | zs | [ fv≡zs ]ᵢ | .zs | refl 
  with  χ' (xs ++ zs)  | lemmaχaux∉ (xs ++ zs)
... | z | z∉xs++fv
  = cong  (Data.Product.map  (λ e' → (z , e')) 
                             (λ notOcurr → tabulate (λ y∈xs → notOcurrBB≢ (x∉xs∧y∈xs⇒y≢x (c∉xs++ys→c∉xs z∉xs++fv) y∈xs) ((lookup notOcurr) y∈xs)))) 
          (lemma-bindersFreeαElemF {F} G xs (swapF F G S x z e) (swapF F G S y z e′) (lemma~B xe~ye′ z#xe))
  where
  z∉fv : z ∉ fvF {|B| S G} {F} S (x , e) 
  z∉fv = subst (_∉_ z)  (sym fv≡zs) (c∉xs++ys→c∉ys {z} {xs} z∉xs++fv)
  z#xe : fresh' S z (|B| S G) (x , e)
  z#xe = lemmafv#' z∉fv

lemma-bindersFreeαElem : 
    {F : Functor}(xs : List V)(e e' : μ F) 
    → e ~α e' 
    → bindersFreeαElem xs e ≡ bindersFreeαElem xs e'
lemma-bindersFreeαElem {F} xs ⟨ e ⟩  ⟨ e' ⟩ e~e' 
  = cong (Data.Product.map (⟨_⟩) id)  (lemma-bindersFreeαElemF F xs e e' e~e')

{-# TERMINATING #-}
lemma-bindersFreeαAlphaF : 
    {F : Functor}(G : Functor)(xs : List V)(e  : ⟦ G ⟧ (μ F)) 
    → ~αF G (proj₁ (bindersFreeαElemF G xs e)) e
lemma-bindersFreeαAlphaF (|v| x)     xs e                             = ~αV
lemma-bindersFreeαAlphaF |1|         xs e                             = ~α1
lemma-bindersFreeαAlphaF (|E| B)     xs e                             = ~αE
lemma-bindersFreeαAlphaF (|Ef| G)    xs ⟨ e ⟩              = ~αEf    (lemma-bindersFreeαAlphaF G xs e )
lemma-bindersFreeαAlphaF {F} |R|     xs ⟨ e ⟩              = ~αR     (lemma-bindersFreeαAlphaF F xs e )
lemma-bindersFreeαAlphaF (G₁ |+| G₂) xs (inj₁ e)           = ~αinj₁  (lemma-bindersFreeαAlphaF G₁ xs e)
lemma-bindersFreeαAlphaF (G₁ |+| G₂) xs (inj₂ e)           = ~αinj₂  (lemma-bindersFreeαAlphaF G₂ xs e)
lemma-bindersFreeαAlphaF (G₁ |x| G₂) xs (e₁ , e₂)    = ~αx     (lemma-bindersFreeαAlphaF G₁ xs e₁) 
                                                               (lemma-bindersFreeαAlphaF G₂ xs e₂)
lemma-bindersFreeαAlphaF {F} (|B| S G)   xs (x , e) 
  with  fvF {|B| S G} {F} S (x , e)
  |     inspect (fvF {|B| S G} {F} S) (x , e)
... | zs | [ fv≡zs ]ᵢ   
  with  χ' (xs ++ zs)  | lemmaχaux∉ (xs ++ zs)
... | z  | z∉xs++fv
  = ~αB zs (λ y y∉zs → lemma~ y∉zs)
  where
  open ~-Reasoning(F)(G)
  lemma~ : {y : V} → y ∉ zs 
         → ~αF G  (swapF F G S z y (proj₁ (bindersFreeαElemF G xs (swapF F G S x z e))))
                  (swapF F G S x y e)
  lemma~ {y} y∉zs
    =  begin
         swapF F G S z y (proj₁ (bindersFreeαElemF G xs (swapF F G S x z e) ))
       ∼⟨ lemma~swapEquiv (lemma-bindersFreeαAlphaF G xs (swapF F G S x z e) ) z y ⟩
         swapF F G S z y (swapF F G S x z e)
       ∼⟨ lemma~swapCancel z#xe y#xe ⟩
         swapF F G S x y e
       ∎
    where
    z∉fv : z ∉ fvF {|B| S G} {F} S (x , e) 
    z∉fv = subst (_∉_ z)  (sym fv≡zs) (c∉xs++ys→c∉ys {z} {xs} z∉xs++fv)
    z#xe : fresh' S z (|B| S G) (x , e)
    z#xe = lemmafv#' z∉fv
    y∉fv : y ∉ fvF {|B| S G} {F} S (x , e) 
    y∉fv = subst (_∉_ y)  (sym fv≡zs) y∉zs
    y#xe : fresh' S y (|B| S G) (x , e)
    y#xe = lemmafv#' y∉fv

lemma-bindersFreeαAlpha : 
    {F : Functor}(xs : List V)(e  : μ F) 
    → proj₁ (bindersFreeαElem xs e) ~α e
lemma-bindersFreeαAlpha {F} xs ⟨ e ⟩ = lemma-bindersFreeαAlphaF F xs e 

αCompatiblePred : {F : Functor} → (μ F → Set) → Set
αCompatiblePred {F = F} P = {e e' : μ F} → e ~α e' → P e → P e'

strong∼αCompatible  : {A : Set}{F : Functor} 
                    → (μ F → A) → μ F → Set
strong∼αCompatible f M = ∀ N → M ~α N → f M ≡ f N

fihα : {F : Functor}(G : Functor)(P : μ F → Set) → ⟦ G ⟧ (μ F) → List V → Set
fihα (|v| S)     P n        xs = ⊤
fihα |1|         P tt       xs = ⊤
fihα (|E| B)     P b        xs = ⊤
fihα (|Ef| G)    P e        xs = ⊤
fihα |R|         P e        xs = P e × (∀ a → a ∈ xs → a notOcurrBind e)
fihα (G |+| G')  P (inj₁ e) xs = fihα G  P e xs
fihα (G |+| G')  P (inj₂ e) xs = fihα G' P e xs
fihα (G |x| G')  P (e , e') xs = fihα G  P e xs × fihα G' P e' xs
fihα (|B| S G)   P (x , e)  xs = x ∉ xs × fihα G  P e xs

lemma-fih∧notOcurrBind⇛fihα : 
     {F : Functor}(G : Functor)(P : μ F → Set)(e : ⟦ G ⟧ (μ F))(xs : List V) 
     → fih {F} G (λ e' → (∀ c → c ∈ xs → c notOcurrBind e') → P e') e 
     → (∀ c → c ∈ xs → notOcurrBind' c {F} G e)
     → fihα {F} G                       P e xs
lemma-fih∧notOcurrBind⇛fihα (|v| x)     P e          xs fih notOcurr   = tt
lemma-fih∧notOcurrBind⇛fihα |1|         P e          xs fih notOcurr   = tt
lemma-fih∧notOcurrBind⇛fihα (|E| x)     P e          xs fih notOcurr   = tt
lemma-fih∧notOcurrBind⇛fihα (|Ef| G)    P e          xs fih notOcurr   = tt
lemma-fih∧notOcurrBind⇛fihα |R|         P e          xs fih notOcurrR  = fih notOcurr , notOcurr
  where
  notOcurr = λ c c∈xs → notOcurrBRinv (notOcurrR c c∈xs)
lemma-fih∧notOcurrBind⇛fihα (G₁ |+| G₂) P (inj₁ e)   xs fih notOcurrinj₁   
  = lemma-fih∧notOcurrBind⇛fihα G₁    P e xs fih (λ c c∈xs → notOcurrBinj₁inv (notOcurrinj₁ c c∈xs))
lemma-fih∧notOcurrBind⇛fihα (G₁ |+| G₂) P (inj₂ e)   xs fih notOcurrinj₂   
  = lemma-fih∧notOcurrBind⇛fihα G₂    P e xs fih (λ c c∈xs → notOcurrBinj₂inv (notOcurrinj₂ c c∈xs))
lemma-fih∧notOcurrBind⇛fihα (G₁ |x| G₂) P (e₁ , e₂)  xs (fih₁ , fih₂) notOcurr   
  = lemma-fih∧notOcurrBind⇛fihα G₁  P e₁ xs fih₁ (λ c c∈xs → notOcurrBx₁inv (notOcurr c c∈xs)) ,
    lemma-fih∧notOcurrBind⇛fihα G₂  P e₂ xs fih₂ (λ c c∈xs → notOcurrBx₂inv (notOcurr c c∈xs))
lemma-fih∧notOcurrBind⇛fihα (|B| S G)   P (a  , e)   xs fih notOcurr   
  with Any.any (_≟v_ a) xs
... | yes a∈xs 
  = ⊥-elim ((notOcurrBBinv≢ (notOcurr a a∈xs)) refl) 
... | no a∉xs  
  = a∉xs , lemma-fih∧notOcurrBind⇛fihα G P e xs fih (λ c c∈xs → notOcurrBBinv (notOcurr c c∈xs))

aux : {F : Functor}(P : μ F → Set)(xs : List V)
      → ((e : ⟦ F ⟧ (μ F)) → fihα F P e xs → P ⟨ e ⟩)      
      → (e : ⟦ F ⟧ (μ F)) 
      → fih F (λ e' → (∀ c → c ∈ xs → c notOcurrBind e') → P e') e
      → ((c : V) → c ∈ xs → _notOcurrBind_ {F} c ⟨ e ⟩) 
      → P ⟨ e ⟩
aux {F} P xs hiα e hi notBind = hiα e (lemma-fih∧notOcurrBind⇛fihα {F} F P e xs hi notBind)

αPrimInd : {F : Functor}(P : μ F → Set)(xs : List V)
  → αCompatiblePred P 
  → ((e : ⟦ F ⟧ (μ F)) → fihα F P e xs → P ⟨ e ⟩)  
  → ∀ e → P e
αPrimInd {F} P xs αP p e with bindersFreeαElem xs e | lemma-bindersFreeαAlpha xs e
... | e' , notBind | e'~e
  = αP e'~e (foldInd  F 
                      (λ e → (∀ c → c ∈ xs → c notOcurrBind e) → P e) 
                      (aux {F} P xs p) 
                      e' 
                      (get notBind))

αIteration : {F : Functor}{A : Set}(xs : List V)
  → ((e : ⟦ F ⟧ (μ F)) → fihα F (const A) e xs → A)
  → (e : μ F) → A
αIteration {A = A} xs f e = αPrimInd (const A) xs (const id) f e

lemma-αIteration-StrongαCompatible : 
  {F : Functor}{A : Set}{xs : List V}{f : (e : ⟦ F ⟧ (μ F)) → fihα F (const A) e xs → A}
  → {e : μ F} 
  → strong∼αCompatible (αIteration xs f) e
lemma-αIteration-StrongαCompatible {xs = xs} {f} {e} e' e~αe' 
  with bindersFreeαElem xs e | bindersFreeαElem xs e' 
  | lemma-bindersFreeαElem xs e e' e~αe' 
... | (x , b) | (.x , .b) | refl = refl

{- Another way to obtain α Iteration -}
foldα : {A : Set}(F : Functor) → List V → (⟦ F ⟧ A → A) → μ F → A
foldα F xs f e with bindersFreeαElem xs e
... | e′ , _ = fold F f e′

lemma-foldα-StrongαCompatible : {A : Set}{F : Functor}{xs : List V}{f : ⟦ F ⟧ A → A}{e : μ F}
  → strong∼αCompatible (foldα F xs f) e
lemma-foldα-StrongαCompatible {xs = xs} {f} {e} e' e~αe' 
  with bindersFreeαElem xs e | bindersFreeαElem xs e' 
  | lemma-bindersFreeαElem xs e e' e~αe' 
... | (x , b) | (.x , .b) | refl = refl


{- Substitution Example - Can be done generically ? -}
-- substAux : {F : Functor}(G : Functor) 
--   → (x : V) → (e' : μ F) → (S : Sort) 
--   → (e : ⟦ G ⟧ (μ F)) 
--   → fihα G (const (⟦ F ⟧ (μ F))) e (x ∷ fv S e') 
--   →  ⟦ G ⟧ (μ F) ⊎ μ F
-- substAux (|v| S')    x e' S e         fihα    = {!!}
-- substAux |1|         x e' S e         fihα    = inj₁ tt
-- substAux (|E| B)     x e' S e         fihα    = inj₁ e
-- substAux (|Ef| G)    x e' S ⟨ e ⟩     fihα    = {! substAux {G} G x e' S e fihα)!}
-- substAux |R|         x e' S ⟨ e ⟩     (r , _) = inj₁ ⟨ r ⟩
-- substAux (G₁ |+| G₂) x e' S (inj₁ e)  fihα    = [ inj₁ ∘ inj₁ , inj₂ ]′ (substAux G₁ x e' S e fihα)
-- substAux (G₁ |+| G₂) x e' S (inj₂ e)  fihα    = [ inj₁ ∘ inj₂ , inj₂ ]′ (substAux G₂ x e' S e fihα)
-- substAux (G₁ |x| G₂) x e' S (e₁ , e₂) (fihα₁ , fihα₂) = {! !}
-- substAux (|B| S' G)  x e' S (y  , e)  fihα   = {!!}

-- substAux' : (F : Functor) 
--   → (x : V) → (e' : μ F) → (S : Sort) 
--   → (e : ⟦ F ⟧ (μ F)) 
--   → fihα F (const (⟦ F ⟧ (μ F))) e (x ∷ fv S e') 
--   → ⟦ F ⟧ (μ F)
-- substAux' F x e' S e fihα with substAux {F} F x e' S e fihα
-- ... | inj₁ r      = r
-- ... | inj₂ ⟨ r ⟩  = r

-- _[_≔_]_ : {F : Functor} → μ F → V → μ F → Sort → μ F
-- _[_≔_]_ {F} e x e' S = ⟨ αIteration (x ∷ fv S e') (substAux' F x e' S) e ⟩

