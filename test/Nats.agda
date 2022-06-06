
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

plus3 : Nat → Nat
plus3 n = suc (suc (suc n))


pred : Nat → Nat
pred zero = zero
pred (suc n) = n

test1 = pred (suc (pred (plus3 40)))

twice : Nat → Nat
twice n = 2 * n

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = twice (pow2 n)

consume : Nat → Nat
consume zero = zero
consume (suc n) = consume n

matchOnTwo : Nat → Nat → Nat
matchOnTwo zero zero = suc (suc (zero))
matchOnTwo (suc zero) (suc (suc zero)) = suc zero
matchOnTwo (suc x) (suc y) = x + y
matchOnTwo x y = zero

test2 = consume (pow2 24)