module Main

import Data.Vect
import Data.Vect.Quantifiers
import System

%default total

fiveIsNotZero : Not (the Nat 5 = 0)
fiveIsNotZero = \Refl impossible

threeIsNotZero : Not (the Nat 3 = 0)
threeIsNotZero = \Refl impossible

modFive : Nat -> Nat
modFive k = modNatNZ k 5 fiveIsNotZero

modThree : Nat -> Nat
modThree k = modNatNZ k 3 threeIsNotZero

record FizzBuzzValue where
    constructor MkFizzBuzzValue
    i : Nat
    s : String

data FizzBuzzProp : FizzBuzzValue -> Type where
     FizzCase : (modThree x = 0) ->
                (Not (modFive x = 0)) ->
                FizzBuzzProp (MkFizzBuzzValue x "Fizz")
     BuzzCase : (Not (modThree x = 0)) ->
                (modFive x = 0) ->
                FizzBuzzProp (MkFizzBuzzValue x "Buzz")
     FizzBuzzCase : (modThree x = 0) ->
                    (modFive x = 0) ->
                    FizzBuzzProp (MkFizzBuzzValue x "FizzBuzz")
     NatCase : (Not (modThree x = 0)) ->
               (Not (modFive x = 0)) ->
               FizzBuzzProp (MkFizzBuzzValue x (show x))

data TotalOrderVect : (p : a -> a -> Type) -> (v : Vect n a) -> Type where
     EmptyVectCase : TotalOrderVect p []
     SingletonCase : TotalOrderVect p [x]
     ConsCase : (tailPrf : TotalOrderVect p (y::ys)) ->
                (headPrf : (p x y)) ->
                TotalOrderVect p (x :: y :: ys)

data FizzBuzzValueNatProp : (p : Nat -> Nat -> Type) ->
                            (a : FizzBuzzValue) ->
                            (b : FizzBuzzValue) ->
                            Type where
     FromNatProp : (natProp : p (i a) (i b)) -> FizzBuzzValueNatProp p a b

oneIsNotMulThree : Not (modThree 1 = fromInteger 0)
oneIsNotMulThree Refl impossible

oneIsNotMulFive : Not (modFive 1 = fromInteger 0)
oneIsNotMulFive Refl impossible

safeHead : (Not (n = Z)) -> (Vect n a) -> a
safeHead {n = Z} nIsNotZP [] = void (nIsNotZP Refl)
safeHead {n = (S len)} nIsNotZP (y :: xs) = y

sGTNotS : GT (S k) k
sGTNotS {k = Z} = LTESucc LTEZero
sGTNotS {k = (S n)} = LTESucc sGTNotS

fizzBuzz : (n : Nat) ->
           (nIsNotZP : Not (n = Z)) ->
           (v : Vect n FizzBuzzValue **
                (All FizzBuzzProp v,
                 n = (i (safeHead nIsNotZP v)),
                 TotalOrderVect (FizzBuzzValueNatProp GT) v))
fizzBuzz Z nIsNotZP = void $ nIsNotZP Refl
fizzBuzz (S Z) _ = ([MkFizzBuzzValue 1 "1"] **
    (NatCase oneIsNotMulThree oneIsNotMulFive :: Nil, Refl, SingletonCase))
fizzBuzz (S (S k)) _ = let (y::ys ** (fizzBuzzInTailP, skInHeadP, totalOrderPoof))
                            = (fizzBuzz (S k) SIsNotZ) in
                         case (decEq (modThree (S (S k))) 0, decEq (modFive (S (S k))) 0) of
                            (Yes mulOfThreeP, No notMulOfFiveP) =>
                                 (_ ** (FizzCase mulOfThreeP notMulOfFiveP :: fizzBuzzInTailP,
                                       Refl,
                                       ConsCase totalOrderPoof $
                                                rewrite skInHeadP in FromNatProp sGTNotS))
                            (No notMulOfThreeP, Yes mulOfFiveP) =>
                                (_ ** (BuzzCase notMulOfThreeP mulOfFiveP :: fizzBuzzInTailP,
                                      Refl,
                                      ConsCase totalOrderPoof $
                                               rewrite skInHeadP in FromNatProp sGTNotS))
                            (Yes mulOfThreeP, Yes mulOfFiveP) =>
                                 (_ ** (FizzBuzzCase mulOfThreeP mulOfFiveP :: fizzBuzzInTailP,
                                       Refl,
                                       ConsCase totalOrderPoof $
                                                rewrite skInHeadP in FromNatProp sGTNotS))
                            (No notMulOfThreeP, No notMulOfFiveP) =>
                                (_ ** (NatCase notMulOfThreeP notMulOfFiveP :: fizzBuzzInTailP,
                                      Refl,
                                      ConsCase totalOrderPoof $
                                               rewrite skInHeadP in FromNatProp sGTNotS))

fizzBuzzDriver : (n : Nat) -> Maybe String
fizzBuzzDriver n = case decEq n Z of
                        Yes _ => Nothing
                        No nIsNotZP => Just $ concatMap (++"\n") $
                                              reverse $
                                              map s $
                                              fst $
                                              fizzBuzz n nIsNotZP

partial
main : IO ()
main = do
     args <- getArgs
     case args of
          (_ :: n :: []) => case all isDigit $ unpack n of
                True => case fizzBuzzDriver $ cast n of
                              Just fizzBuzzString => do putStr fizzBuzzString
                                                        exitSuccess
                              Nothing => do putStrLn "The argument can't be zero."
                                            exitFailure
                False => do putStrLn "The argument isn't a number."
                            exitFailure
          _ => do putStrLn "Wrong number of arguments."
                  exitFailure
