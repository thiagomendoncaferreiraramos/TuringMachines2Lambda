open import TM
open import Lambda
open import Data.Nat using (ℕ; zero; suc; ⌊_/2⌋; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; [_])
open import Data.Fin using (Fin; inject₁; fromℕ; toℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)

ℕ2ƛ-aux : ℕ → Term
ℕ2ƛ-aux zero = ` "x"
ℕ2ƛ-aux (suc n) = ` "f" · (ℕ2ƛ-aux n)

ℕ2ƛ : ℕ → Term
ℕ2ƛ n = ƛ "f" ⇒ ƛ "x" ⇒ (ℕ2ƛ-aux n)


NIL-ƛ : Term
NIL-ƛ = ƛ "z" ⇒ ƛ "x" ⇒ ƛ "y" ⇒ ` "x"

PAIR-ƛ : Term → Term → Term
PAIR-ƛ m n = ƛ "f" ⇒ ` "f" · m · n


List2ƛ : {S : Set} → List S → (S → Term) → Term
List2ƛ [] _ =  NIL-ƛ
List2ƛ (x ∷ xs) fl = PAIR-ƛ (fl x) (List2ƛ xs fl)

Fin2ƛ : {n : ℕ} → Fin n → Term
Fin2ƛ m = ℕ2ƛ (toℕ m)

ITE-ƛ : Term → Term → Term → Term
ITE-ƛ i t e =  i · t · e

TRUE-ƛ : Term
TRUE-ƛ = ƛ "x" ⇒ ƛ "y" ⇒ ` "x"

FALSE-ƛ : Term
FALSE-ƛ = ƛ "x" ⇒ ƛ "y" ⇒ ` "y"

RIGHT-ƛ : Term
RIGHT-ƛ = PAIR-ƛ NIL-ƛ TRUE-ƛ

LEFT-ƛ : Term
LEFT-ƛ = PAIR-ƛ NIL-ƛ FALSE-ƛ

IS-0-ƛ : Term
IS-0-ƛ = ƛ "n" ⇒ ` "n" · (ƛ "x" ⇒ FALSE-ƛ ) · TRUE-ƛ

PRED-ƛ : Term
PRED-ƛ = ƛ "n" ⇒ ƛ "f" ⇒ ƛ "x" ⇒
           ` "n" · (ƛ "g" ⇒ ƛ "h" ⇒ ` "h" · (` "g" · ` "f")) ·
                (ƛ  "u" ⇒ ` "x" ) · (ƛ "u" ⇒ ` "u")

SUB-ƛ : Term
SUB-ƛ = ƛ "m" ⇒ ƛ "n" ⇒ ` "n" · PRED-ƛ · ` "m"

trans-fun2ƛ-aux : {n-states n-symbols : ℕ} →
              trans-fun n-states n-symbols →
              Fin (suc (suc n-states)) → Fin (suc n-symbols)
              → Term
trans-fun2ƛ-aux δ st1 sym1
                with δ st1 sym1
...  | ⟨ st , inj₁ left ⟩  = PAIR-ƛ (Fin2ƛ st) LEFT-ƛ
...  | ⟨ st , inj₁ right ⟩  = PAIR-ƛ (Fin2ƛ st) RIGHT-ƛ
...  | ⟨ st , inj₂ sym ⟩ = PAIR-ƛ (Fin2ƛ st) (Fin2ƛ sym)

δ2ƛ-aux : {n-states n-symbols : ℕ} →
              trans-fun n-states n-symbols →
              Fin (suc (suc n-states)) → Fin (suc n-symbols)
              → Term
δ2ƛ-aux δ Fin.zero Fin.zero = trans-fun2ƛ-aux δ Fin.zero Fin.zero
δ2ƛ-aux δ (Fin.suc m) Fin.zero = {!!}
δ2ƛ-aux δ Fin.zero (Fin.suc n) = {!!}
δ2ƛ-aux δ (Fin.suc m) (Fin.suc n) = {!ƛ "x1" ⇒ ƛ "x2" ⇒ ITE-ƛ!}


{-
trans-fun n-states n-symbols = Fin (suc (suc n-states)) → Fin (suc n-symbols)
           → ( Fin (suc (suc n-states)) ×  (Move ⊎ Fin (suc n-symbols)) )
-}

{-

 move-left : 
              {st st' : Fin (suc (suc (tm-States tm)))} →
              {sym1 sym2 : Fin (suc (tm-Symbols tm))} →
              {l1 l2 : List (Fin (suc (tm-Symbols tm)))} 
            → tm-trans tm st sym2 ≡  ( st' , inj₁ left )
            ------------------------------------
           →
             ▹ tm ⟨ (sym1 ∷ l1) ! st ! (sym2 ∷ l2) ⟩
             ⟨ l1 ! st' ! (sym1 ∷ sym2 ∷ l2) ⟩


-}

tuple2nat : ℕ × ℕ → ℕ
tuple2nat ⟨ m , n ⟩ = ⌊ (m + n) * (suc (m + n)) /2⌋ + n



nat2tuple : ℕ → ℕ × ℕ
nat2tuple zero = ⟨ zero , zero ⟩
nat2tuple (suc n) with nat2tuple n
...                 |    ⟨ zero , n ⟩  = ⟨ suc n , zero ⟩
...                 |    ⟨ suc m , n ⟩ = ⟨ m , suc n ⟩ 

{-
transtoƛ : {n-states}
-}
