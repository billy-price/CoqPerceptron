# CoqPerceptron
Verified Coq Implementation of the Integer Valued Perceptron Algorithm

# Building Benchmarks

## Extract to Haskell

```Bash
make
cd Benchmarks/hs && make
```

Note if ghc fails to compile `ReadData.hs` make the following edit to `FueledPerceptron.hs`

```Haskell
-- Move unsafeCoerce :: a -> b directly below the #endif line
unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif
```

to

```Haskell
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif
unsafeCoerce :: a -> b
```

## Build C++ Perceptron and Data Generator
```Bash
cd Benchmarks/cpp && make
```
