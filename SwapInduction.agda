module SwapInduction where

open import GPBindings
open import Swap

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product

fihS : {F : Functor}(G : Functor)(P : μ F → Set) → ⟦ G ⟧ (μ F) → Set
fihS (|v| S)       P n        = ⊤
fihS |1|           P tt       = ⊤
fihS (|E| B)       P b        = ⊤
fihS (|Ef| G)      P e        = ⊤
fihS |R|           P e        = P e 
fihS (G |+| G')    P (inj₁ e) = fihS G  P e 
fihS (G |+| G')    P (inj₂ e) = fihS G' P e 
fihS (G |x| G')    P (e , e') = fihS G  P e  × fihS G' P e' 
fihS {F} (|B| S G) P (x , e)  = (y : V) → fihS G  P (swapF G S x y e)

foldmapFS : {F : Functor}(G : Functor)(P : μ F → Set)
          → ((e : ⟦ F ⟧ (μ F)) → fihS F P e →  P ⟨ e ⟩)
          → (e : ⟦ G ⟧ (μ F))
          → AccF F G e
          → fihS G P e
foldmapFS (|v| S)        P hi n        _                  = tt
foldmapFS |1|            P hi tt       _                  = tt
foldmapFS (|E| B)        P hi b        _                  = tt
foldmapFS (|Ef| F)       P hi b        _                  = tt
foldmapFS {F} |R|        P hi ⟨ e ⟩    (accR acce)        = hi e (foldmapFS {F} F P hi e acce)
foldmapFS (F |+| F')     P hi (inj₁ e) (acc+₁ acce)       = foldmapFS F  P hi e acce
foldmapFS (F |+| F')     P hi (inj₂ e) (acc+₂ acce)       = foldmapFS F' P hi e acce
foldmapFS (F |x| F')     P hi (e , e') (accx acce acce')  = foldmapFS F  P hi e acce , foldmapFS F' P hi e' acce'
foldmapFS {F} (|B| S G)  P hi (x , e)  (accB facc)        = λ y → foldmapFS G P hi (swapF G S x y e) (facc y) 

swapInd : (F : Functor)(P : μ F → Set)    
  → ((e : ⟦ F ⟧ (μ F)) → fihS F P e →  P ⟨ e ⟩)  
  → (e : μ F) → P e
swapInd F P hi e = foldmapFS {F} |R| P hi e (accF e)
