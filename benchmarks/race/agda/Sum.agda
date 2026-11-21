-- Sum of the first n natural numbers: 2 * (0 + 1 + ... + n) = n * (n + 1).
-- Self-contained (no standard library): every lemma is proved below.

{-# OPTIONS --safe #-}
module Sum where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + n * m
{-# BUILTIN NATTIMES _*_ #-}

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

infix  1 begin_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  3 _∎

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨⟩_ : {A : Set} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ p = p

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : {A : Set} (x : A) → x ≡ x
x ∎ = refl

+-identityʳ : ∀ n → n + zero ≡ n
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm m zero    = +-identityʳ m
+-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n = cong suc (begin
    n + m * suc n
  ≡⟨ cong (n +_) (*-suc m n) ⟩
    n + (m + m * n)
  ≡⟨ sym (+-assoc n m (m * n)) ⟩
    (n + m) + m * n
  ≡⟨ cong (_+ m * n) (+-comm n m) ⟩
    (m + n) + m * n
  ≡⟨ +-assoc m n (m * n) ⟩
    m + (n + m * n)
  ∎)

double : ∀ x → 2 * x ≡ x + x
double x = cong (x +_) (+-identityʳ x)

interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
interchange a b c d =
  begin
    (a + b) + (c + d)
  ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))
  ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
    a + ((b + c) + d)
  ≡⟨ cong (λ x → a + (x + d)) (+-comm b c) ⟩
    a + ((c + b) + d)
  ≡⟨ cong (a +_) (+-assoc c b d) ⟩
    a + (c + (b + d))
  ≡⟨ sym (+-assoc a c (b + d)) ⟩
    (a + c) + (b + d)
  ∎

-- k(k+1) + 2(k+1) = (k+1)(k+2)
step : ∀ k → k * (k + 1) + (suc k + suc k) ≡ suc k * (suc k + 1)
step k =
  begin
    k * (k + 1) + (suc k + suc k)
  ≡⟨ cong (λ x → k * (k + 1) + suc x) (+-suc k k) ⟩
    k * (k + 1) + suc (suc (k + k))
  ≡⟨ +-suc (k * (k + 1)) (suc (k + k)) ⟩
    suc (k * (k + 1) + suc (k + k))
  ≡⟨ cong suc (+-suc (k * (k + 1)) (k + k)) ⟩
    suc (suc (k * (k + 1) + (k + k)))
  ≡⟨ cong (λ x → suc (suc x)) (+-comm (k * (k + 1)) (k + k)) ⟩
    suc (suc ((k + k) + k * (k + 1)))
  ≡⟨ cong (λ x → suc (suc x)) (+-assoc k k (k * (k + 1))) ⟩
    suc (suc (k + (k + k * (k + 1))))
  ≡⟨ cong (λ x → suc (suc (k + x))) (sym (*-suc k (k + 1))) ⟩
    suc (suc (k + k * suc (k + 1)))
  ≡⟨ cong (λ x → suc (x + k * suc (k + 1))) (+-comm 1 k) ⟩
    suc ((k + 1) + k * suc (k + 1))
  ≡⟨⟩
    suc k * (suc k + 1)
  ∎

-- COPY
sumTo : ℕ → ℕ
sumTo zero    = zero
sumTo (suc n) = sumTo n + suc n

sum-formula : ∀ n → 2 * sumTo n ≡ n * (n + 1)
sum-formula zero    = refl
sum-formula (suc k) =
  begin
    2 * (sumTo k + suc k)
  ≡⟨ double (sumTo k + suc k) ⟩
    (sumTo k + suc k) + (sumTo k + suc k)
  ≡⟨ interchange (sumTo k) (suc k) (sumTo k) (suc k) ⟩
    (sumTo k + sumTo k) + (suc k + suc k)
  ≡⟨ cong (_+ (suc k + suc k)) (trans (sym (double (sumTo k))) (sum-formula k)) ⟩
    k * (k + 1) + (suc k + suc k)
  ≡⟨ step k ⟩
    suc k * (suc k + 1)
  ∎
-- END COPY
