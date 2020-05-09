## User-facing language

The AST of the user-facing language, as created directly by the `generate`,
`map`, `foldl`, etc. combinators in `Data.Array.Accelerate`, is contained in
`DAA.Smart` and `DAA.Array.Sugar`. This AST consists of the following types:

```haskell
-- Smart:
newtype Acc a = Acc (SmartAcc (Sugar.ArrRepr a))
newtype SmartAcc a = SmartAcc (PreSmartAcc SmartAcc Exp a)
data PreSmartAcc acc exp as where {- GADT Array AST -}
newtype Exp t = Exp (PreExp SmartAcc Exp t)
data PreExp acc exp t where {- GADT Exp AST -}

-- Sugar:
data Z = Z
data tail :. head = !tail :. !head
data Array sh e where
  Array :: EltRepr sh                 -- extent of dimensions = shape
        -> ArrayData (EltRepr e)      -- array payload
        -> Array sh e
```

`Sugar.ArrRepr` is an associated type, with at least the following rules:

```haskell
ArrRepr () = ()
ArrRepr (Sugar.Array sh e) = Sugar.Array sh e
ArrRepr (a, b) = (((), ArrRepr a), ArrRepr b)
ArrRepr (a, b, c) = ((((), ArrRepr a), ArrRepr b), ArrRepr c)
-- etc.
```

### Examples

```haskell
generate (constant (Z :. 10)) (\i -> toFloating @Int @Float (unindex1 i))
	:: Smart.Acc (Sugar.Array (Sugar.Z Sugar.:. Int) Float)

A.constant 2.0 * A.constant 3.0
	= A.mkMul (A.constant 2.0) (A.constant 3.0)
	= A.Exp (PrimMul numType `PrimApp` tup2 (x, y))
```


## Internal representation

The optimisation passes (sharing recovery and array fusion) convert from the
user-facing representation to different internal languages. First, sharing
recovery (`DAA.Trafo.Sharing.convert{Acc,Afun}With`) converts to a De Bruijn
indexed form (`OpenAcc`), which is defined in `DAA.AST`. Then, array fusion
(`DAA.Trafo.Fusion.convert{Acc,Afun}With`) converts to a "delayed"
representation (`DelayedAcc`), defined in `DAA.Trafo.Base`. All together, the
full conversion is defined in `DAA.Trafo.convert{Acc,Afun}With`, which simply
composes these functions (modulo debug logging).
