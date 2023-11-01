
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc 1) + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

{-


_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc (4)))
  ≡⟨⟩
    7
  ∎
    



_ : 3 * 4 ≡ 12
_ =
G  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ : 2 ^ 3 ≡ 8
_ =
  begin
    2 ^ 3
  ≡⟨⟩
    2 * (2 ^ 2)
  ≡⟨⟩
    2 * (2 * (2 ^ 1))
  ≡⟨⟩
    2 * (2 * (2 * (2 ^ 0)))
  ≡⟨⟩
    8
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    zero
  ∎

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

{-
⟨⟩ O
  ⟨⟩ I

⟨⟩ I
  ⟨⟩ I O

⟨⟩ I O O
  ⟨⟩ I O I

⟨⟩ I O I
  ⟨⟩ I I O

⟨⟩ I I I
  ⟨⟩ I O O O

  I I I
-}



inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = inc(m) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    inc (⟨⟩ I O I) O
  ≡⟨⟩
    inc (⟨⟩ I O) O O
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

from : Bin → ℕ
from ⟨⟩   = zero
from (b O) = 2 * from b
from (b I) = suc (2 * from b)

_ : from (⟨⟩ I O O) ≡ 4
_ =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩
    2 * from(⟨⟩ I O)
  ≡⟨⟩
    2 * (2 * from(⟨⟩ I))
  ≡⟨⟩
    2 * (2 * suc (2 * from(⟨⟩)))
  ≡⟨⟩
    2 * (2 * suc (2 * zero))
  ≡⟨⟩
    2 * (2 * suc (zero))
  ≡⟨⟩
    2 * (2 * 1)
  ∎

_ : to 4 ≡ ⟨⟩ I O O
_ =
  begin
    to 4
  ≡⟨⟩
    inc (to 3)
  ≡⟨⟩
    inc (inc (to 2))
  ≡⟨⟩
    inc (inc (inc (to 1)))
  ≡⟨⟩
    inc (inc (inc (inc (to 0))))
  ≡⟨⟩
    inc (inc (inc (inc (⟨⟩ O))))
  ≡⟨⟩
    inc (inc (inc (⟨⟩ I)))
  ≡⟨⟩
    inc (inc (inc(⟨⟩) O))
  ≡⟨⟩
    inc (inc (⟨⟩ I O))
  ≡⟨⟩
    inc (⟨⟩ I I)
  ≡⟨⟩
    inc (⟨⟩ I) O
  ≡⟨⟩
    inc (⟨⟩) O O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

_ : to 3 ≡ ⟨⟩ I I
_ = refl


-}
