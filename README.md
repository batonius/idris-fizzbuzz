# Formally-proven FizzBuzz in Idris.

The `fizzBuzz` function accepts a non-zero natural number n and produces a vector of records with a Nat and a String fields along with the following properties proven at the compile time:
1. The vector has length exactly n, expressed in the vector itself.
2. The Nat field of the head element of the vector equals n, expressed as `n = (i (safeHead nIsNotZP v))`.
3. The vector is strictly ordered by the greater-than relation over the Nat fields of the elements, expressed as `TotalOrderVect (FizzBuzzValueNatProp GT) v`.
4. For every pair in the vector, the string field corresponds to the Nat field according to the FizzBuzz rules, expressed as `All FizzBuzzProp v`.

In other words, properties 1-3 guarantee the function produces the sequence n, (n-1)..1, while property 4 guarantees each element in the sequence has a valid String component. The final type signature of the `fizzBuzz` function looks like
```idris
fizzBuzz : (n : Nat) ->
           (nIsNotZP : Not (n = Z)) ->
           (v : Vect n FizzBuzzValue **
                (All FizzBuzzProp v,
                 n = (i (safeHead nIsNotZP v)),
                 TotalOrderVect (FizzBuzzValueNatProp GT) v))
```
To get a string from it you need something like the `fizzBuzzDriver` function:
```idris
fizzBuzzDriver : (n : Nat) -> Maybe String
fizzBuzzDriver n = case decEq n Z of
                        Yes _ => Nothing
                        No nIsNotZP => Just $ concatMap (++"\n") $
                                              reverse $
                                              map s $
                                              fst $
                                              fizzBuzz n nIsNotZP
```
