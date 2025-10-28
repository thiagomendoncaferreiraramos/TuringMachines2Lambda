open import TM
open import Lambda
open import Data.Nat using (ℕ; zero; suc; ⌊_/2⌋; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; [_])
open import Data.Fin using (Fin; inject₁; fromℕ; toℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

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

IS-NIL-ƛ : Term
IS-NIL-ƛ = ƛ "p" ⇒ ` "p" · (ƛ "x" ⇒ ƛ "y" ⇒ FALSE-ƛ)

RIGHT-ƛ : Term
RIGHT-ƛ = PAIR-ƛ NIL-ƛ TRUE-ƛ

LEFT-ƛ : Term
LEFT-ƛ = PAIR-ƛ NIL-ƛ FALSE-ƛ

FST-ƛ : Term
FST-ƛ = ƛ "p" ⇒ ` "p" · TRUE-ƛ

SND-ƛ : Term
SND-ƛ = ƛ "p" ⇒ ` "p" · FALSE-ƛ

IS-0-ƛ : Term
IS-0-ƛ = ƛ "n" ⇒ ` "n" · (ƛ "x" ⇒ FALSE-ƛ ) · TRUE-ƛ

PRED-ƛ : Term
PRED-ƛ = ƛ "n" ⇒ ƛ "f" ⇒ ƛ "x" ⇒
           ` "n" · (ƛ "g" ⇒ ƛ "h" ⇒ ` "h" · (` "g" · ` "f")) ·
                (ƛ  "u" ⇒ ` "x" ) · (ƛ "u" ⇒ ` "u")

SUB-ƛ : Term
SUB-ƛ = ƛ "m" ⇒ ƛ "n" ⇒ ` "n" · PRED-ƛ · ` "m"

LEQ-ƛ : Term
LEQ-ƛ = ƛ "m" ⇒ ƛ "n" ⇒ IS-0-ƛ · (SUB-ƛ · ` "m" · ` "n")

AND-ƛ : Term
AND-ƛ = ƛ "p" ⇒ ƛ "q" ⇒ ` "p" · ` "q" · ` "p"

EQ-ƛ : Term
EQ-ƛ = ƛ "m" ⇒ ƛ "n" ⇒ AND-ƛ · (LEQ-ƛ · ` "m" · ` "n") · (LEQ-ƛ · ` "n" · ` "m")

trans-fun2ƛ-aux : {n-states n-symbols : ℕ} →
              trans-fun n-states n-symbols →
              Fin (suc (suc n-states)) → Fin (suc n-symbols)
              → Term
trans-fun2ƛ-aux δ st1 sym1
                with δ st1 sym1
...  | ⟨ st , inj₁ left ⟩  = PAIR-ƛ (Fin2ƛ st) LEFT-ƛ
...  | ⟨ st , inj₁ right ⟩  = PAIR-ƛ (Fin2ƛ st) RIGHT-ƛ
...  | ⟨ st , inj₂ sym ⟩ = PAIR-ƛ (Fin2ƛ st) (Fin2ƛ sym)

ℕ2Fin : {n : ℕ} → ℕ → Fin (suc n)
ℕ2Fin zero = Fin.zero
ℕ2Fin {zero} _ = Fin.zero
ℕ2Fin {suc n} (suc i) = Fin.suc (ℕ2Fin {n} i)

δ2ƛ-1 : {n-states n-symbols : ℕ} → trans-fun n-states n-symbols
        → Fin (suc (suc n-states)) → ℕ
        → Term
δ2ƛ-1 {nst} {nsym} δ st zero = trans-fun2ƛ-aux {nst} {nsym} δ st Fin.zero
δ2ƛ-1 δ st (suc n) = ITE-ƛ (EQ-ƛ · (ℕ2ƛ (suc n)) · ` "x")
                     (trans-fun2ƛ-aux δ st (ℕ2Fin (suc n))) (δ2ƛ-1 δ st n)


δ2ƛ-2 : {n-states n-symbols : ℕ} → trans-fun n-states n-symbols
        → ℕ
        → Term
δ2ƛ-2 {nst} {nsym} δ zero = δ2ƛ-1 δ Fin.zero nsym
δ2ƛ-2 {nst} {nsym} δ (suc n) = ITE-ƛ (EQ-ƛ · (ℕ2ƛ (suc n)) · ` "y")
                               (δ2ƛ-1 δ (ℕ2Fin (suc n)) (suc nsym)) (δ2ƛ-2 δ n)


-- Transform the transition function into a λ term:
δ2ƛ : {n-states n-symbols : ℕ} → trans-fun n-states n-symbols
        → Term

δ2ƛ {nst} {nsym} δ = ƛ "y" ⇒ ƛ "x" ⇒ δ2ƛ-2 δ (suc (suc nst))

Config2ƛ : {tm : TM} → Config tm → Term
Config2ƛ ⟨ l1 ! st ! l2 ⟩   = PAIR-ƛ (List2ƛ l1 Fin2ƛ) (PAIR-ƛ (Fin2ƛ st)
                                       (List2ƛ l2 Fin2ƛ))


-- Selecting the new state and direction from "x"
δ-Config-aux : {n-states n-symbols : ℕ} → trans-fun n-states n-symbols
        → Term
δ-Config-aux δ = (δ2ƛ δ) · (FST-ƛ · (SND-ƛ · ` "x")) ·
                       (FST-ƛ · (SND-ƛ · (SND-ƛ · ` "x")))


δ-Config : {n-states n-symbols : ℕ} → trans-fun n-states n-symbols
        → Term
δ-Config δ = ITE-ƛ (IS-NIL-ƛ · (FST-ƛ · (SND-ƛ · (δ-Config-aux δ))))
                    (ITE-ƛ (SND-ƛ · (SND-ƛ · (δ-Config-aux δ)))
                           (PAIR-ƛ (PAIR-ƛ (SND-ƛ · (SND-ƛ · ` "x"))
                                           (FST-ƛ · ` "x"))
                                   (PAIR-ƛ (FST-ƛ · (δ-Config-aux δ))
                                           (SND-ƛ · (SND-ƛ · (SND-ƛ · ` "x")))))
                           (PAIR-ƛ (SND-ƛ · (FST-ƛ · ` "x"))
                                   (PAIR-ƛ (FST-ƛ · (δ-Config-aux δ))
                                           (PAIR-ƛ (FST-ƛ · (FST-ƛ · ` "x"))
                                                   (SND-ƛ · (SND-ƛ · ` "x"))))))
                    (PAIR-ƛ (FST-ƛ · ` "x")
                            (PAIR-ƛ (FST-ƛ · (δ-Config-aux δ))
                                    (PAIR-ƛ (SND-ƛ · (δ-Config-aux δ))
                                            (SND-ƛ · (SND-ƛ · (SND-ƛ · ` "x"))))))



tmƛ-Rel : TM → Term
tmƛ-Rel TM⟨ _ , _ , δ ⟩ = ƛ "x" ⇒ (ITE-ƛ (IS-NIL-ƛ · (FST-ƛ · ` "x"))
                         (PAIR-ƛ (List2ƛ [ zero ] ℕ2ƛ) (SND-ƛ · ` "x"))
                         (ITE-ƛ (IS-NIL-ƛ · (SND-ƛ · (SND-ƛ · ` "x")))
                                (PAIR-ƛ (FST-ƛ · ` "x")
                                        (PAIR-ƛ (SND-ƛ · (FST-ƛ · ` "x"))
                                              (List2ƛ [ zero ] ℕ2ƛ)))
                                (δ-Config δ)))


G : TM → Term
G tm = ƛ "r" ⇒ ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             (` "r" · ` "r" · ((tmƛ-Rel tm) · ` "x"))


tm-sim : TM → Term
tm-sim tm = (G tm) · (G tm)


-- ITE-ƛ[] : 


equiv1 : ∀(tm : TM) →

               ((ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             (` "r" · ` "r" · ((tmƛ-Rel tm) · ` "x"))) [ "r" := (G tm)]) ≡ (ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             ((G tm) · (G tm) · ((tmƛ-Rel tm) · ` "x")))

equiv1 tm  = {!!}

refl-clos-sim4 : ∀(tm : TM) → ∀ (l1 l2 : List (Fin (suc (tm-Symbols tm)))) →

               ((ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             (` "r" · ` "r" · ((tmƛ-Rel tm) · ` "x"))) [ "r" := (G tm)]) ≡ (ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             ((G tm) · (G tm) · ((tmƛ-Rel tm) · ` "x"))) →
              
              ((ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             (` "r" · ` "r" · ((tmƛ-Rel tm) · ` "x"))) [ "r" := (G tm)]) · Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩ ⋙*
             (ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             ((G tm) · (G tm) · ((tmƛ-Rel tm) · ` "x"))) · Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩
refl-clos-sim4 tm l1 l2 rel rewrite cong (_· Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩) rel = ⋙-refl 


refl-clos-sim3 : ∀(tm : TM) → ∀ (l1 l2 : List (Fin (suc (tm-Symbols tm)))) → 
              (ƛ "r" ⇒ ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             (` "r" · ` "r" · ((tmƛ-Rel tm) · ` "x"))) · (G tm) · Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩ ⋙*
              ((ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             (` "r" · ` "r" · ((tmƛ-Rel tm) · ` "x"))) [ "r" := (G tm)]) · Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩
refl-clos-sim3 tm l1 l2 = ⋙1-step (β-left β)


refl-clos-sim2 : ∀(tm : TM) → ∀ (l1 l2 : List (Fin (suc (tm-Symbols tm)))) → 
              (ƛ "r" ⇒ ƛ "x" ⇒ ITE-ƛ (EQ-ƛ · (FST-ƛ · (SND-ƛ · ` "x")) · (ℕ2ƛ 1))
                             (` "x")
                             (` "r" · ` "r" · ((tmƛ-Rel tm) · ` "x"))) · (G tm) · Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩ ⋙*
              Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩
refl-clos-sim2 tm l1 l2 = {!!}

refl-clos-sim1 : ∀(tm : TM) → ∀ (l1 l2 : List (Fin (suc (tm-Symbols tm)))) → 
              (G tm) · (G tm) · Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩ ⋙*
              Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩

refl-clos-sim1 tm l1 l2 = refl-clos-sim2 tm l1 l2


refl-clos-sim : ∀(tm : TM) → ∀ (l1 l2 : List (Fin (suc (tm-Symbols tm)))) → 
              tm-sim tm · Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩ ⋙*
              Config2ƛ {tm} ⟨ l1 ! Fin.suc Fin.zero ! l2 ⟩

refl-clos-sim tm l1 l2 = refl-clos-sim1 tm l1 l2

lambda-sim-tm : ∀(tm : TM) → ∀(config1 config2 : Config tm)
                → ▹* tm config1 config2 × Halt tm config2 →
                (tm-sim tm) · (Config2ƛ {tm} config1) ⋙* (Config2ƛ {tm} config2)

lambda-sim-tm tm config1 config2 ⟨ refl-clos , halt ⟩ = {!!}
lambda-sim-tm tm config1 config2 ⟨ one-step x , snd ⟩ = {!!}
lambda-sim-tm tm config1 config2 ⟨ trans-clos fst fst₁ , snd ⟩ = {!!}

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
