module LongestParen where

open import Function using (_∘_; id)
open import Data.Maybe hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])

open ≡-Reasoning
open import Data.List.Properties using (map-compose)

variable
  A B C : Set
{-
inits : {A : Set} → List A → List (List A)
inits [] = [] ∷ []
inits (x ∷ xs) = [] ∷ map (λ ys → x ∷ ys) (inits xs)
-}

inits⁺ : List A → List (List A)
inits⁺ [] = []
inits⁺ (x ∷ xs) = (x ∷ []) ∷ map (λ ys → x ∷ ys) (inits⁺ xs)

-- monads

_=<<_ : (A → Maybe B) → Maybe A → Maybe B
f =<< nothing = nothing
f =<< just x  = f x

_<=<_ : (B → Maybe C) → (A → Maybe B) → A → Maybe C
(f <=< g) x = f =<< g x

monad1 : (m : Maybe A) → (just =<< m) ≡ m
monad1 nothing = refl
monad1 (just x) = refl

monad3 : ∀ (m : Maybe A) (f : A → Maybe B) (g : B → Maybe C) →
         ((λ x → g =<< f x) =<< m) ≡ (g =<< (f =<< m))
monad3 nothing  f g = refl
monad3 (just x) f g = refl

-- spine

postulate
  Char : Set
  Spine : Set
  bstep : Char → Spine → Spine
  stepM : Char → Spine → Maybe Spine
  null[] : Spine

build : List Char → Spine
build []       = null[]
build (x ∷ xs) = bstep x (build xs)

parseS : List Char → Maybe Spine
parseS []       = just null[]
parseS (x ∷ xs) = (stepM x <=< parseS) xs

bsteps : List Char → Spine → Spine
bsteps []       = id
bsteps (x ∷ xs) = bstep x ∘ bsteps xs

stepsM : List Char → Spine → Maybe Spine
stepsM []       = just
stepsM (x ∷ xs) = stepM x <=< stepsM xs

build-bsteps : (ys xs : List Char) →
               bsteps ys (build xs) ≡ build (ys ++ xs)
build-bsteps [] xs = refl
build-bsteps (y ∷ ys) xs = cong (bstep y) (build-bsteps ys xs)


parseS-stepsM : (ys xs : List Char) →
               stepsM ys =<< parseS xs ≡ parseS (ys ++ xs)
parseS-stepsM [] xs = monad1 (parseS xs)
parseS-stepsM (y ∷ ys) xs
  rewrite monad3 (parseS xs) (stepsM ys) (stepM y) =
       cong (λ m → stepM y =<< m) (parseS-stepsM ys xs)

--

filtJust : List (Maybe Spine) → List Spine
filtJust [] = []
filtJust (nothing ∷ xs) = filtJust xs
filtJust (just x ∷ xs) = x ∷ filtJust xs

pickJust : Maybe Spine → Spine
pickJust nothing  = null[]
pickJust (just x) = x

postulate
   _⊕_ : Spine → Spine → Spine
   ⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
   ⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
   ⊕-idem : ∀ x → x ⊕ x ≡ x
   null[]⊕-l : ∀ x → null[] ⊕ x ≡ x

choose : List Spine → Spine
choose [] = null[]
choose (x ∷ xs) = x ⊕ choose xs

choose-pickJust : ∀ x xs →
   choose (filtJust (x ∷ xs)) ≡ pickJust x ⊕ choose (filtJust xs)
choose-pickJust nothing xs = sym (null[]⊕-l  _)
choose-pickJust (just x) xs = refl

--

postulate
 parse-build-1 : ∀ ys x →
   (choose ∘ map build ∘ inits) ys ⊕ pickJust (parseS (ys ++ [ x ])) ≡
    (choose ∘ map build ∘ inits) ys ⊕ build (ys ++ [ x ])

postulate
 choose-inits-snoc : ∀ {A : Set} (ys : List A) x f →
  (choose ∘ map f ∘ inits) ys ⊕ f (ys ++ [ x ]) ≡
    (choose ∘ map f ∘ inits) (ys ++ [ x ])


parse-build-gen : ∀ ys xs →
   (choose ∘ map build ∘ inits) ys ⊕
     (choose ∘ filtJust ∘ map (stepsM ys <=< parseS) ∘ inits⁺) xs ≡
      (choose ∘ map build ∘ inits) ys ⊕
        (choose ∘ map (bsteps ys ∘ build) ∘ inits⁺) xs
parse-build-gen ys [] = refl
parse-build-gen ys (x ∷ xs) =
   (choose ∘ map build ∘ inits) ys ⊕
     (choose ∘ filtJust ∘ map (stepsM ys <=< parseS) ∘ inits⁺) (x ∷ xs)
  ≡⟨ refl ⟩
    (choose ∘ map build ∘ inits) ys ⊕
     choose (filtJust (stepsM ys =<< stepM x null[] ∷
       map (stepsM ys <=< parseS) (map (λ ys₁ → x ∷ ys₁) (inits⁺ xs))))
  ≡⟨ cong (λ t → (choose ∘ map build ∘ inits) ys ⊕
      choose (filtJust (t ∷ (map (stepsM ys <=< parseS) ∘ map (λ ys₁ → x ∷ ys₁) ∘ inits⁺) xs)))
       (parseS-stepsM ys [ x ]) ⟩
   (choose ∘ map build ∘ inits) ys ⊕
    choose (filtJust (parseS (ys ++ [ x ]) ∷
         map (stepsM ys <=< parseS) (map (λ ys₁ → x ∷ ys₁) (inits⁺ xs))))
  ≡⟨ cong (λ xs → (choose ∘ map build ∘ inits) ys ⊕ xs)
             (choose-pickJust (parseS (ys ++ x ∷ [])) _) ⟩
   (choose ∘ map build ∘ inits) ys ⊕
      (pickJust (parseS (ys ++ [ x ])) ⊕
         (choose ∘ filtJust ∘
            map (stepsM ys <=< parseS) ∘ map (λ ys₁ → x ∷ ys₁) ∘ inits⁺) xs)
  ≡⟨ sym (⊕-assoc _ _ _) ⟩
   ((choose ∘ map build ∘ inits) ys ⊕ pickJust (parseS (ys ++ [ x ]))) ⊕
        (choose ∘ filtJust ∘
           map (stepsM ys <=< parseS) ∘ map (λ ys₁ → x ∷ ys₁) ∘ inits⁺) xs
  ≡⟨ cong (λ zs → zs ⊕ (choose ∘ filtJust ∘
         map (stepsM ys <=< parseS) ∘ map (λ ys₁ → x ∷ ys₁) ∘ inits⁺) xs)
       (parse-build-1 ys x) ⟩
   ((choose ∘ map build ∘ inits) ys ⊕ build (ys ++ [ x ])) ⊕
      (choose ∘ filtJust ∘
         map (stepsM ys <=< parseS) ∘ map (λ ys₁ → x ∷ ys₁) ∘ inits⁺) xs
  --
  ≡⟨ cong (λ z → z ⊕ (choose ∘ filtJust ∘
          map (stepsM ys <=< parseS) ∘ map (λ ys₁ → x ∷ ys₁) ∘ inits⁺) xs)
      (choose-inits-snoc ys x build) ⟩
   (choose ∘ map build ∘ inits) (ys ++ [ x ]) ⊕
     (choose ∘ filtJust ∘
        map (stepsM ys <=< parseS) ∘ map (λ ys₁ → x ∷ ys₁) ∘ inits⁺) xs
  ≡⟨ cong (λ ws → (choose ∘ map build ∘ inits) (ys ++ [ x ]) ⊕
                        choose (filtJust ws))
        {(map (λ x₁ → stepsM ys =<< parseS x₁) (map (λ ys₁ → x ∷ ys₁) (inits⁺ xs)))} {(map ((λ x₁ → stepsM ys =<< parseS x₁) ∘ (λ ys₁ → x ∷ ys₁)) (inits⁺ xs))}
        (sym (map-compose (inits⁺ xs))) ⟩
   (choose ∘ map build ∘ inits) (ys ++ [ x ]) ⊕
      (choose ∘ filtJust ∘
          map (λ zs → stepsM ys =<< parseS (x ∷ zs)) ∘ inits⁺) xs
  ≡⟨ {!   !} ⟩
   (choose ∘ map build ∘ inits) (ys ++ [ x ]) ⊕
      (choose ∘ filtJust ∘
          map (stepsM (ys ++ [ x ]) <=< parseS) ∘ inits⁺) xs
  ≡⟨ parse-build-gen (ys ++ [ x ]) xs ⟩
   (choose ∘ map build ∘ inits) (ys ++ [ x ]) ⊕
     (choose ∘ map (bsteps (ys ++ [ x ]) ∘ build) ∘ inits⁺) xs
  ≡⟨ {!   !} ⟩
   ((choose ∘ map build ∘ inits) ys ⊕ build (ys ++ [ x ])) ⊕
     (choose ∘ map (bsteps (ys ++ [ x ]) ∘ build) ∘ inits⁺) xs
  ≡⟨ (⊕-assoc _ _ _) ⟩
   (choose ∘ map build ∘ inits) ys ⊕ (build (ys ++ [ x ]) ⊕
    (choose ∘ map (bsteps (ys ++ [ x ]) ∘ build) ∘ inits⁺) xs)
  ≡⟨ {!   !} ⟩
   ((choose ∘ map build ∘ inits) ys ⊕
     (choose ∘ map (bsteps ys ∘ build) ∘ inits⁺) (x ∷ xs))
  ∎
