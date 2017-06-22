{- System F, Nominal syntax, Substitution Composition another proof ? -}
module Examples.Ahora where

open import Data.Empty
open import Relation.Nullary
open import Function
open import Data.Nat hiding (fold)
open import Data.Nat.Properties
open import Data.List hiding (unfold)
open import Data.List.All
open import Data.Sum
open import Data.Product hiding (swap)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)

open import Data.List.Any as Any hiding (tail;map)
open Any.Membership-≡

open import GPBindings
open import Atom
open import Swap
open import Fresh
open import FreeVariables
open import Alpha
open import AlphaInduction
open import OcurrBind
open import List.ListProperties
open import Examples.SystemF
open ~-Reasoning(tF)

TreeTermF =  |Ef| tF |x| |Ef| tF |x| |Ef| tF 
TreeTerm = μ TreeTermF

PSComp : {x y : V} → TreeTerm → Set
PSComp {x} {y} ⟨ M , N , L ⟩ = x ∉ y ∷ fv L
  → (M [ x ≔ N ]) [ y ≔ L ] ~α (M [ y ≔ L ])[ x ≔ N [ y ≔ L ] ]

αCompatiblePSComp : ∀ {x y : V} → αCompatiblePred {TreeTermF} (PSComp {x} {y})
αCompatiblePSComp {x} {y} {⟨ M , N , L ⟩} {⟨ M′ , N′ , L′ ⟩} (~αR (~αx M~M′ (~αx N~N′ L~L′))) PMs x∉y:fvL′
  =  begin
       (M′  [ x ≔ N′  ])  [ y ≔ L′  ]
     -- Strong α compability of inner substitution operation       
     ≈⟨ cong (λ z → z [ y ≔ L′ ]) (lemma-substα (σ (lemma-~αEf M~M′))) ⟩
       (M   [ x ≔ N′  ])  [ y ≔ L′  ]
     -- Strong α compability of outter substitution operation       
     ≈⟨ lemma-substα {M [ x ≔ N′ ]} {M [ x ≔ N ]} (lemma-substα′ {x} {M} (σ (lemma-~αEf N~N′))) ⟩
       (M   [ x ≔ N   ])  [ y ≔ L′  ]
     ∼⟨ lemma-substα′ {y} {M [ x ≔ N   ]} (σ (lemma-~αEf L~L′)) ⟩
       (M   [ x ≔ N   ])  [ y ≔ L   ]
     ∼⟨ PMs x∉y∶fvL ⟩ 
       (M   [ y ≔ L   ])  [ x ≔ N   [ y ≔ L   ] ]
     ≈⟨ cong (λ P → P [ x ≔ N [ y ≔ L ] ]) (lemma-substα (lemma-~αEf M~M′)) ⟩ 
       (M′  [ y ≔ L   ])  [ x ≔ N   [ y ≔ L   ] ]
     ≈⟨ lemma-substα {M′ [ y ≔ L ]} {M′ [ y ≔ L′ ]} {N [ y ≔ L ]} {x} (lemma-substα′ {y} {M′} (lemma-~αEf L~L′))  ⟩        
       (M′  [ y ≔ L′  ])  [ x ≔ N   [ y ≔ L   ] ]
     ≈⟨ cong (λ P → (M′ [ y ≔ L′ ])  [ x ≔ P ]) (lemma-substα (lemma-~αEf N~N′))   ⟩
       (M′  [ y ≔ L′  ])  [ x ≔ N′  [ y ≔ L   ] ]
     ∼⟨ lemma-substα′ {x} {M′  [ y ≔ L′ ]} {N′ [ y ≔ L ]} (lemma-substα′ {y} {N′} (lemma-~αEf L~L′)) ⟩ 
       (M′  [ y ≔ L′  ])  [ x ≔ N′  [ y ≔ L′  ] ]
     ∎
  where
  x∉y∶fvL : x ∉ y ∷ fv L
  x∉y∶fvL = subst (λ xs → x ∉ y ∷ xs) (lemma~fv (σ (lemma-~αEf L~L′))) x∉y:fvL′

αproof :  {x y : V}(Ms : μ TreeTermF)
           → ListNotOcurrBind (x ∷ y ∷ []) Ms 
           → ListNotOcurrBind (fv Ms) Ms
           → PSComp {x} {y} Ms
αproof {x} {y} ⟨ M , N , L ⟩ nOcc nOcc2 x∉y∶fvL
   =  begin
         (M  [ x ≔ N  ])  [ y ≔ L ]
      ≈⟨ lemma-substα {M [ x ≔ N ]} (lemmaSubsts {x} {M} {N} x:fvN∉bM) ⟩
         M   [ x ≔ N ]n   [ y ≔ L ]
      ∼⟨ lemmaSubsts {y} {M [ x ≔ N ]n} {L} y:fvL∉bM[x≔N]n ⟩
         M   [ x ≔ N ]n   [ y ≔ L ]n
      ∼⟨ lemma-substCompositionN {x} {y} {M} {N} {L} x∉y∶fvL x∉bL ⟩
         M   [ y ≔ L ]n   [ x ≔ N [ y ≔ L ]n  ]n
      ∼⟨ lemma-substnα′ {x} {M [ y ≔ L ]n} (σ (lemmaSubsts {y} {N} y:fvL∉bN))  ⟩
         M   [ y ≔ L ]n   [ x ≔ N [ y ≔ L ]   ]n
      ∼⟨ σ (lemmaSubsts {x} {M [ y ≔ L ]n} {N [ y ≔ L ]} x:fvN[y≔L]∉bM[y≔L]n) ⟩
         M   [ y ≔ L ]n   [ x ≔ N [ y ≔ L ]   ]
      ≈⟨ lemma-substα (σ (lemmaSubsts {y} {M} {L} y:fvL∉bM)) ⟩
         (M  [ y ≔ L  ])  [ x ≔ N [ y ≔ L ]   ]
       ∎
  where
  fvM++fvN++fvL∉bM,N,L : ListNotOcurrBind {TreeTermF} (fv M ++ fv N ++ fv L) ⟨ M , N , L ⟩
  fvM++fvN++fvL∉bM,N,L = subst (λ xs → ListNotOcurrBind xs ⟨ M , N , L ⟩) (lemmafvtern {tF} {tF} {tF} {M} {N} {L}) nOcc2
  fvM++fvN++fvL∉bM : ListNotOcurrBind (fv M ++ fv N ++ fv L) M
  fvM++fvN++fvL∉bM
    = lemmalistNotOcurrBindEf→ListNotOcurrBindR (listNotOcurrBx₁inv (lemmalistNotOcurrBindFR→ListNotOcurrBindF fvM++fvN++fvL∉bM,N,L))
  fvM++fvN++fvL∉bN : ListNotOcurrBind (fv M ++ fv N ++ fv L) N
  fvM++fvN++fvL∉bN
    = lemmalistNotOcurrBindEf→ListNotOcurrBindR (listNotOcurrBx₁inv (listNotOcurrBx₂inv (lemmalistNotOcurrBindFR→ListNotOcurrBindF fvM++fvN++fvL∉bM,N,L)))
  fvM++fvN++fvL∉bL : ListNotOcurrBind (fv M ++ fv N ++ fv L) L
  fvM++fvN++fvL∉bL
    = lemmalistNotOcurrBindEf→ListNotOcurrBindR (listNotOcurrBx₂inv (listNotOcurrBx₂inv (lemmalistNotOcurrBindFR→ListNotOcurrBindF fvM++fvN++fvL∉bM,N,L)))
  x:y∉bM : ListNotOcurrBind (x ∷ y ∷ []) M
  x:y∉bM = lemmalistNotOcurrBindEf→ListNotOcurrBindR (listNotOcurrBx₁inv (lemmalistNotOcurrBindFR→ListNotOcurrBindF nOcc))
  x:y∉bN : ListNotOcurrBind (x ∷ y ∷ []) N
  x:y∉bN = lemmalistNotOcurrBindEf→ListNotOcurrBindR (listNotOcurrBx₁inv (listNotOcurrBx₂inv (lemmalistNotOcurrBindFR→ListNotOcurrBindF nOcc)))
  x:y∉bL : ListNotOcurrBind (x ∷ y ∷ []) L
  x:y∉bL = lemmalistNotOcurrBindEf→ListNotOcurrBindR (listNotOcurrBx₂inv (listNotOcurrBx₂inv (lemmalistNotOcurrBindFR→ListNotOcurrBindF nOcc)))
  x:fvN∉bM : ListNotOcurrBind (x ∷ fv  N) M
  x:fvN∉bM = lemma-binds:cons (lemma-binds:head x:y∉bM) (lemma-binds++l (lemma-binds++r {fv M} fvM++fvN++fvL∉bM))
  x∉bL : x notOcurrBind L
  x∉bL = lemma-binds:head x:y∉bL
  y:fvL∉bM : ListNotOcurrBind (y ∷ fv L) M
  y:fvL∉bM = lemma-binds:cons (lemma-binds:head (lemma-binds:tail x:y∉bM)) (lemma-binds++r {fv N} (lemma-binds++r {fv M} fvM++fvN++fvL∉bM))
  y:fvL∉bN : ListNotOcurrBind (y ∷ fv L) N
  y:fvL∉bN = lemma-binds:cons (lemma-binds:head (lemma-binds:tail x:y∉bN)) (lemma-binds++r {fv N} (lemma-binds++r {fv M} fvM++fvN++fvL∉bN))
  y:fvL∉bM[x≔N]n : ListNotOcurrBind (y ∷ fv L) (M [ x ≔ N ]n)
  y:fvL∉bM[x≔N]n
    = lemma-foldCtxBinds y:fvL∉bM (lemma-binds:cons (notOcurrBR (notOcurrBx notOcurrBv (notOcurrBindR→notOcurrBindEf (lemma-binds:head y:fvL∉bN)))) (lemma-bindsR (lemma-binds× lemma-bindsv (lemmalistNotOcurrBindFR→ListNotOcurrBindEf (lemma-binds:tail y:fvL∉bN)))))
  [x]∉bM[y≔L]n : ListNotOcurrBind [ x ] (M [ y ≔ L ]n)
  [x]∉bM[y≔L]n = lemma-foldCtxBinds (lemma-binds:cons (lemma-binds:head x:y∉bM ) []) (lemma-bindsR ( lemma-binds× (notOcurrBv ∷ []) ( lemmalistNotOcurrBindFR→ListNotOcurrBindEf ( lemma-binds:cons  (lemma-binds:head x:y∉bL) []))))
  fv⟨y,L⟩∉bM : {L : μ tF} → ListNotOcurrBind (y ∷ fv L) M → ListNotOcurrBind (fv {cF} ⟨ y , L ⟩) M
  fv⟨y,L⟩∉bM {⟨ L ⟩} y:fvL∉bM = lemma-binds:cons (lemma-binds:head y:fvL∉bM) (lemma-binds:tail y:fvL∉bM)
  y∉bL : y notOcurrBind L
  y∉bL = lemma-binds:head (lemma-binds:tail x:y∉bL)
  fvL∉bL : ListNotOcurrBind (fv L) L
  fvL∉bL = lemma-binds++r {fv N} (lemma-binds++r {fv M} fvM++fvN++fvL∉bL)
  fv⟨y,L⟩∉b⟨y,L⟩ : {L : μ tF} → y notOcurrBind L → ListNotOcurrBind (fv L) L → ListNotOcurrBind (fv {cF}⟨ y , L ⟩) ⟨ y , L ⟩
  fv⟨y,L⟩∉b⟨y,L⟩ {⟨ L ⟩} y∉bL fvL∉bL = lemma-binds:cons (notOcurrBR (notOcurrBx notOcurrBv (notOcurrBEf (notOcurrBRinv y∉bL)))) ((lemma-bindsR (lemma-binds× lemma-bindsv (lemmalistNotOcurrBindFR→ListNotOcurrBindEf fvL∉bL))))
  fvN[y≔L]n∉bM[y≔L]n : ListNotOcurrBind (fv (N [ y ≔ L ]n)) (M [ y ≔ L ]n)
  fvN[y≔L]n∉bM[y≔L]n
    = lemma-binds⊆  {fv {cF} ⟨ y , L ⟩ ++ fv N} {fv (N [ y ≔ L ]n)}
                    (foldCtxFV {cF} {tF} {tF} {⟨ y , L ⟩} {N})
                    (lemma-binds++  {fv {cF} ⟨ y , L ⟩} {fv N}
                                    (lemma-foldCtxBinds  {cF} {tF} {tF} {substaux} {⟨ y , L ⟩} {M} {fv {cF} ⟨ y , L ⟩} (fv⟨y,L⟩∉bM {L} y:fvL∉bM) (fv⟨y,L⟩∉b⟨y,L⟩ {L} y∉bL fvL∉bL))
                                    (lemma-foldCtxBinds  (lemma-binds++l (lemma-binds++r {fv M} fvM++fvN++fvL∉bM))
                                                         (lemma-bindsR ( lemma-binds× lemma-bindsv (lemmalistNotOcurrBindFR→ListNotOcurrBindEf (lemma-binds++l (lemma-binds++r {fv M} fvM++fvN++fvL∉bL)))))))
  x:fvN[y≔L]n∉bM[y≔L]n : ListNotOcurrBind (x ∷ fv (N [ y ≔ L ]n)) (M [ y ≔ L ]n)
  x:fvN[y≔L]n∉bM[y≔L]n = lemma-binds:cons (lemma-binds:head [x]∉bM[y≔L]n) fvN[y≔L]n∉bM[y≔L]n
  x:fvN[y≔L]∉bM[y≔L]n : ListNotOcurrBind (x ∷ fv (N [ y ≔ L ])) (M [ y ≔ L ]n)
  x:fvN[y≔L]∉bM[y≔L]n = subst (λ xs → ListNotOcurrBind (x ∷ xs) (M [ y ≔ L ]n)) (lemma~fv (σ (lemmaSubsts y:fvL∉bN))) x:fvN[y≔L]n∉bM[y≔L]n

lemma-substComposition2 : {x y : V}{Ms : TreeTerm} → PSComp {x} {y} Ms
lemma-substComposition2 {x} {y} {⟨ M , N , L ⟩}
 = αProof  (PSComp {x} {y})
           (x ∷ y ∷ []) 
           (αCompatiblePSComp {x} {y})
           αproof
           ⟨ M , N , L ⟩

