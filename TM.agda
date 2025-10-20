open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; inject₁; fromℕ; toℕ)
open import Data.List using (List; []; _∷_; [_])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Bool.Base as Bool
  using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning

--{-# BUILTIN NATURAL ℕ #-}

data Move : Set where
  right : Move
  left : Move



data ⟨_×_×_⟩ (A B C : Set) : Set where
  ⟨_!_!_⟩ : A → B → C → ⟨ A × B × C ⟩

π₁ : {A B C : Set} → ⟨ A × B × C ⟩ → A
π₁ ⟨ a ! _ ! _ ⟩ = a

π₂ : {A B C : Set} → ⟨ A × B × C ⟩ → B
π₂ ⟨ _ ! b ! _ ⟩ = b

π₃ : {A B C : Set} → ⟨ A × B × C ⟩ → C
π₃ ⟨ _ ! _ ! c ⟩ = c


{-
  The transition function reads a state and a symbol
  and returns a movement a new state and a symbol
  to write.
-}
trans-fun : ℕ → ℕ → Set
trans-fun n-states n-symbols = Fin (suc (suc n-states)) → Fin (suc n-symbols)
           → ( Fin (suc (suc n-states)) ×  (Move ⊎ Fin (suc n-symbols)) )


{-
  A Turing Machine is defined by the states, symbols and
  transition functon.
-}
data TM  : Set where
  TM⟨_,_,_⟩ : (n-states : ℕ) → (n-symbols : ℕ) → trans-fun n-states n-symbols
              → TM

tm-States : TM → ℕ
tm-States TM⟨ n-states , _ , _ ⟩ =  n-states


tm-Symbols : TM → ℕ
tm-Symbols TM⟨ _ , n-symbols , _ ⟩ =  n-symbols

tm-trans : (tm  : TM) → Fin (suc (suc (tm-States tm))) → Fin (suc (tm-Symbols tm))
           → ( Fin (suc (suc (tm-States tm))) ×  (Move ⊎ (Fin (suc (tm-Symbols tm)))) )
tm-trans TM⟨ _ , _ , δ ⟩ = δ 

Config :  TM  → Set 
Config tm =
           ⟨ List (Fin (suc (tm-Symbols tm))) ×
             Fin (suc (suc (tm-States tm))) ×
             List (Fin (suc (tm-Symbols tm))) ⟩


data ▹(tm : TM) :
               -- → (tm : TM) →
               Config tm
               → Config tm → Set where
               
  move-left : 
              {st st' : Fin (suc (suc (tm-States tm)))} →
              {sym1 sym2 : Fin (suc (tm-Symbols tm))} →
              {l1 l2 : List (Fin (suc (tm-Symbols tm)))} 
            → tm-trans tm st sym2 ≡  ( st' , inj₁ left )
            ------------------------------------
           →
             ▹ tm ⟨ (sym1 ∷ l1) ! st ! (sym2 ∷ l2) ⟩
             ⟨ l1 ! st' ! (sym1 ∷ sym2 ∷ l2) ⟩

  blank-right : 
              {st : Fin (suc (suc (tm-States tm)))} →
              {l1 : List (Fin (suc (tm-Symbols tm)))} 
            ------------------------------------
           →
             ▹ tm ⟨ l1 ! st ! [] ⟩
             ⟨ l1 ! st ! [ Fin.zero ] ⟩

  blank-left : 
              {st : Fin (suc (suc (tm-States tm)))} →
              {l : List (Fin (suc (tm-Symbols tm)))}
            ------------------------------------
           →
             ▹ tm ⟨ [] ! st ! l ⟩
             ⟨ [ Fin.zero ] ! st ! l ⟩

  

  move-right : 
              {st st' : Fin (suc (suc (tm-States tm)))} →
              {sym1 sym2 : Fin (suc (tm-Symbols tm))} →
              {l1 l2 : List (Fin (suc (tm-Symbols tm)))} 
            → tm-trans tm st sym2 ≡  ( st' , inj₁ right )
            ------------------------------------
           →
             ▹ tm ⟨ (sym1 ∷ l1) ! st ! (sym2 ∷ l2) ⟩
             ⟨ sym2 ∷ sym1 ∷ l1 ! st' ! l2 ⟩

 

  write :
              {st st' : Fin (suc (suc (tm-States tm)))} →
              {sym1 sym2 : Fin (suc (tm-Symbols tm))} →
              {l1 l2 : List (Fin (suc (tm-Symbols tm)))} 
            → tm-trans tm st sym1 ≡  ( st' , inj₂ sym2 )
            ------------------------------------
           →
             ▹ tm ⟨ l1 ! st ! (sym1 ∷ l2) ⟩
             ⟨ l1 ! st' ! sym2 ∷ l2 ⟩

data Halt(tm : TM) : Config tm → Set where
  halt :
    {l1 l2 : List (Fin (suc (tm-Symbols tm)))} →
    Halt tm ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩


data ▹*(tm : TM) : Config tm → Config tm → Set where
  refl-clos :
           {config : Config tm} →
            ▹* tm config config

  one-step :
           {config1 config2 : Config tm} →
           ▹ tm config1 config2 →
            ▹* tm config1 config2

  trans-clos :
             {config1 config2 config3 : Config tm} →
             ▹* tm config1 config2 →
             ▹* tm config2 config3 →
             ▹* tm config1 config3



func-erase-last : trans-fun 1 1
func-erase-last Fin.zero Fin.zero = (Fin.suc (Fin.suc Fin.zero) , inj₁ left)
func-erase-last Fin.zero (Fin.suc Fin.zero) = (Fin.zero , inj₁ right)
func-erase-last (Fin.suc Fin.zero) y =  (Fin.suc Fin.zero , inj₂ y)
func-erase-last (Fin.suc (Fin.suc Fin.zero)) Fin.zero = (Fin.suc Fin.zero , inj₁ left)
func-erase-last (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero) = ( Fin.suc (Fin.suc Fin.zero)) , inj₂ (Fin.zero)


erase-last : TM
erase-last = TM⟨ 1 , 1 , func-erase-last ⟩

#b : Fin 2
#b = Fin.zero

#1 : Fin 2
#1 = Fin.suc Fin.zero



erase-last-step0 : ▹ erase-last ⟨ [] ! Fin.zero !  #1 ∷ #1 ∷ #1 ∷ [] ⟩
                                ⟨ [ #b ] ! Fin.zero ! #1 ∷ #1 ∷ #1 ∷ [] ⟩
erase-last-step0 = blank-left

erase-last-step1 : ▹ erase-last ⟨ [ #b ] ! Fin.zero !  #1 ∷ #1 ∷ #1 ∷ [] ⟩
                                ⟨  #1 ∷ #b ∷ [] ! Fin.zero !  #1 ∷ #1 ∷ [] ⟩
erase-last-step1 = move-right refl

erase-last-step2 : ▹ erase-last ⟨  #1 ∷ #b ∷ [] ! Fin.zero !  #1 ∷ #1 ∷ [] ⟩
                                ⟨ #1 ∷ #1 ∷ #b ∷ [] ! Fin.zero !  #1 ∷ [] ⟩
erase-last-step2 = move-right refl

erase-last-step3 : ▹ erase-last ⟨ #1 ∷ #1 ∷ #b ∷ [] ! Fin.zero !  #1 ∷ [] ⟩
                                ⟨ #1 ∷ #1 ∷ #1 ∷ #b ∷ [] ! Fin.zero ! [] ⟩ 
                                
erase-last-step3 = move-right refl

erase-last-step4 : ▹ erase-last ⟨ #1 ∷ #1 ∷ #1 ∷ #b ∷ [] ! Fin.zero ! [] ⟩
                    ⟨ #1 ∷ #1 ∷ #1 ∷ #b ∷ [] ! Fin.zero ! [ #b ] ⟩
                                
                                
erase-last-step4 = blank-right

erase-last-step5 : ▹ erase-last ⟨ #1 ∷ #1 ∷ #1 ∷ #b ∷ [] ! Fin.zero ! [ #b ] ⟩
                    ⟨ #1 ∷ #1 ∷ #b ∷ [] ! Fin.suc (Fin.suc Fin.zero) ! #1 ∷ #b ∷ [] ⟩
                    
                                
                                
erase-last-step5 = move-left refl


erase-last-step6 : ▹ erase-last ⟨ #1 ∷ #1 ∷ #b ∷ [] !
                                  Fin.suc (Fin.suc Fin.zero) ! #1 ∷ #b ∷ [] ⟩
                   ⟨ #1 ∷ #1 ∷ #b ∷ [] ! Fin.suc (Fin.suc Fin.zero) ! #b ∷ #b ∷ [] ⟩
                    
                    
                                
                                
erase-last-step6 = write refl

erase-last-step7 : ▹ erase-last ⟨ #1 ∷ #1 ∷ #b ∷ [] !
                                  Fin.suc (Fin.suc Fin.zero) ! #b ∷ #b ∷ [] ⟩
                   ⟨ #1 ∷ #b ∷ [] ! Fin.suc Fin.zero ! #1 ∷ #b ∷ #b ∷ [] ⟩
                    
                    
                                
                                
erase-last-step7 = move-left refl



erase-last-example : ▹* erase-last ⟨ [] ! Fin.zero !  #1 ∷ #1 ∷ #1 ∷ [] ⟩
                           ⟨ #1 ∷ #b ∷ [] ! Fin.suc Fin.zero ! #1 ∷ #b ∷ #b ∷ [] ⟩
erase-last-example = trans-clos
                      (trans-clos
                      (trans-clos
                      (trans-clos
                      (trans-clos
                      (trans-clos
                      (trans-clos (one-step erase-last-step0)
                                 (one-step erase-last-step1))
                                 (one-step erase-last-step2))
                                 (one-step erase-last-step3))
                                 (one-step erase-last-step4))
                                 (one-step erase-last-step5))
                                 (one-step erase-last-step6))
                                 (one-step erase-last-step7)

{--}
